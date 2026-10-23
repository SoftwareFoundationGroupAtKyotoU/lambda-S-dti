(* Generic parallel command runner: writes a Makefile with one rule per job and
   runs `make -j<N>` once. A job counts as successful iff its out_path exists
   after make returns. Used for clang (ML side) and grift compiles alike. *)

(* backend の Builder.build_clang_cmd で組み立てたコマンドを並列コンパイル
   する機構。Makefile生成 + `make -j<N>` は、ベンチマーカー特有の要件
   (計測フェーズと重ならないよう、コンパイルだけを並列化したい)から
   生まれたものなので、backend ではなくここに置く。backend 側 (Builder) は
   「1つの clang コマンドをどう組み立てるか」だけを知っていればよく、
   このモジュールへの依存は無い。 *)

(* One shell command and the file it must produce. *)
(* prerequisite は持たない: 呼び出し側 (Bench_runner) は、このモジュールを
   呼ぶ前に必要なCソース等を全て同期的に書き終えている。out_path はこの
   呼び出しの前には存在しないログディレクトリ配下なので、prerequisite の
   有無に関わらず Make は必ずこのルールを実行する。 *)
type job = {
  out_path : string;  (* このコマンドが生成するはずのファイル。実行後の
                          存在確認だけで成否を判定する (下記 .DELETE_ON_ERROR:)。 *)
  cmd : string;
}

(* Default parallelism: nproc - 1 (4 if nproc is unavailable). *)
(* -j のデフォルト値。nproc-1 (1コアはOS/OCamlドライバ用に残す)。
   nproc が使えない環境向けに fallback=4。 *)
let default_jobs () : int =
  let fallback = 4 in
  try
    let ic = Unix.open_process_in "nproc" in
    let line = input_line ic in
    match Unix.close_process_in ic with
    | Unix.WEXITED 0 -> max 1 (int_of_string (String.trim line) - 1)
    | _ -> fallback
  with _ -> fallback

(* Escape a recipe (shell command) for Make: '$' -> '$$'. *)
(* レシピ本文 (シェルコマンド) 用のエスケープ: Make は自身の変数展開を
   通してからシェルに渡すので '$' だけエスケープすれば良い。 *)
let escape_recipe s = String.concat "$$" (String.split_on_char '$' s)

(* Escape a Make target name: '$' -> '$$' and ':' -> '\:' (log_dir contains ':'). *)
(* ターゲット/prerequisite 名の位置に置く文字列用のエスケープ:
   '$' に加えて ':' もエスケープする。log_dir はタイムスタンプ由来で
   ':' を含む (例 "17:41:08") ため、無エスケープだと Make のルール行構文
   (targets : target-pattern : prereq-patterns という静的パターンルールの
   区切り文字と誤認される) を壊し、"ターゲットパターンが '%' を含んでいません"
   というエラーで停止する。'\:' エスケープは実ファイルパスをそのまま指す
   ことを実機 GNU Make 4.2.1 で確認済み ( .DELETE_ON_ERROR: がエスケープ後の
   ターゲット名でも実ファイルを正しく削除する)。 *)
let escape_target s = escape_recipe (String.concat "\\:" (String.split_on_char ':' s))

(* Write a Makefile: `all` depends on every out_path; each job's output goes to <out_path>.log. *)
let write_makefile ~path (jobs : job list) =
  let buf = Buffer.create 8192 in
  (* レシピが非0終了した場合、Make が (部分的に書きかけの) ターゲット
     ファイルを削除する。これにより make 終了後は Sys.file_exists out_path
     だけで成否判定でき、make の標準出力をパースする必要が無い
     (実機 GNU Make 4.2.1 で動作確認済み)。 *)
  Buffer.add_string buf ".DELETE_ON_ERROR:\n";
  let all_outs = List.map (fun j -> j.out_path) jobs in
  Buffer.add_string buf
    (Printf.sprintf ".PHONY: all\nall: %s\n\n" (String.concat " " (List.map escape_target all_outs)));
  List.iter (fun j ->
    (* レシピの標準出力・標準エラーは <out_path>.log にリダイレクトする。
       複数ジョブを -j で並列実行すると素の標準出力はインターリーブして
       ほぼ読めなくなるため、失敗時に該当ログだけを案内する運用にする。
       ここはシェルに渡す文字列(レシピ本文)なので escape_recipe を使う
       (escape_target の '\:' はシェル上は無害だが、実ファイルパスとの
       対応を分かりやすくするため意図的に使い分ける)。 *)
    Buffer.add_string buf
      (Printf.sprintf "%s:\n\t%s > %s.log 2>&1\n\n"
         (escape_target j.out_path) (escape_recipe j.cmd) (escape_recipe j.out_path))
  ) jobs;
  let oc = open_out path in
  Buffer.output_buffer oc buf;
  close_out oc

(* Run `make -j<jobs> -k` on the Makefile and block until every job has finished. *)
(* `make` 1回の呼び出しで全ジョブを並列コンパイルする。Sys.command は
   `make` プロセス自体の終了を待つブロッキング呼び出しであり、`make` は
   `-k` (keep-going) を指定していても自身の子プロセス (clang) 全てが
   終了するまで戻らない。よってこの関数が返った時点でどの clang プロセスも
   走っていないことが保証され、呼び出し側はこの直後から CPU/メモリを専有
   する直列の計測フェーズを安全に開始できる。 *)
let run_make ~makefile_path ~jobs =
  let cmd =
    Printf.sprintf "make -j%d -k --output-sync=target -f %s"
      (max 1 jobs) (Filename.quote makefile_path)
  in
  Format.printf "@.%s@." cmd;
  (* 終了コードは「どこかのジョブが失敗した」以上の情報を持たない (-k のため)。
     どのジョブが失敗したかは呼び出し側が job.out_path の存在確認で判定する。 *)
  ignore (Sys.command cmd)

(* Entry point: write <log_dir>/bench/build_<label>.mk and run it (no-op for an empty job list). *)
(* jobs に列挙された全ビルドを並列コンパイルする。呼び出し後、各ジョブの
   成否は `Sys.file_exists job.out_path` で判定できる。 *)
let compile_all ~log_dir ~label ~jobs (to_build : job list) : unit =
  match to_build with
  | [] -> ()
  | _ ->
    let makefile_path = Printf.sprintf "%s/bench/build_%s.mk" log_dir label in
    write_makefile ~path:makefile_path to_build;
    run_make ~makefile_path ~jobs
