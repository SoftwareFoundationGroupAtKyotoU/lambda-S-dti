(* 出力フォーマット：Json（1ファイルに配列）, JsonLines（NDJSON） *)
type out_mode = Json | JsonLines
let out_mode = ref JsonLines  (* 推奨: NDJSON。1行=1ミュータント *)

type writer = { oc : out_channel; mutable first : bool }

let open_writer ~log_dir ~mode_str ~file : writer =
  match !out_mode with
  | JsonLines ->
    { oc = open_out (Printf.sprintf "%s/%s_%s.jsonl" log_dir mode_str file); first = true }
  | Json ->
    let oc = open_out (Printf.sprintf "%s/%s_%s.json" log_dir mode_str file) in
    Printf.fprintf oc "{ \"file\": \"%s\", \"mode\": \"%s\", \"mutants\": [\n" file mode_str;
    { oc; first = true }

let mutant_json ~mode_str ~idx ~after_mutate ~times_sec : Yojson.Safe.t =
  Bench_json.obj [
    ("mode", Bench_json.str mode_str);
    ("mutant_index", Bench_json.int idx);
    ("after_mutate", Bench_json.str after_mutate);
    ("times_sec", Bench_json.list (List.map Bench_json.float times_sec));
    ("mem", `Null); ("cast", `Null); ("inference", `Null); ("longest", `Null);
  ]

let write_mutant (w:writer) (j:Yojson.Safe.t) =
  match !out_mode with
  | JsonLines -> Bench_json.to_channel_ln w.oc j
  | Json ->
    if not w.first then output_string w.oc ",\n";
    Yojson.Safe.to_channel w.oc j; w.first <- false

let close_writer (w:writer) =
  (match !out_mode with Json -> output_string w.oc "\n]}\n" | JsonLines -> ());
  close_out w.oc