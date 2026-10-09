# todo — 残作業

[CLAUDE.md](../CLAUDE.md) から参照される用途別ドキュメントの一つ。「次に何をやるか」をここに集約する。
経緯は [history.md](history.md)、使い方は [howto.md](howto.md) を参照。

新しく着手する前に、まず `git log` と `dune runtest`/`compile_test/dotests.sh` を実行して以下がまだ有効か確認すること（実装は git log の方が正しい）。
このリストは `grep -rn "TODO\|FIXME\|yet"` で拾えるものを中心に棚卸ししたもの（初出 2026-08-08、行番号は 2026-09-19 時点のものに更新済み）。

---

## mutant のサンプリングがホスト（OCaml 4.14）と Docker（OCaml 5.2）で異なる

スロット数が `mutation_slot_threshold`（6）以上の対象は `Mutate.sample_subsets_by_length` で部分集合を抽出する。種は `(n, samples_per_slot)` から作る `Random.State` なので同じ環境なら毎回同じだが、OCaml 5.0 で乱数生成器のアルゴリズムが変わったため、ホスト（4.14.1）と Docker（5.2.0）では同じ `mutant_index` が別のスロット選択を指す（2026-09-29 確認: `logs/fsm`（09-27）と `logs/final` の fsm（09-29）はどちらも Docker で 650 件すべて一致。ホストで生成したものとは 1 番と最後の番号以外が違う）。

- 影響: ホストで流す `compile_test/mutation_test.sh` / `test/check_mutants.exe` / ホストでの `bench.exe` は、Docker で計測した mutant とは別の mutant を検査している。loop（5 スロット）と tak（4 スロット）は全列挙なので影響しない。
- 当面の対策: 計測した mutant そのものを検査したいときは Docker の中で流す。ホストのログと Docker のログを `mutant_index` で突き合わせない。
- 恒久対策の案: 自前の小さな PRNG（xorshift など）に置き換えて OCaml のバージョンに依存しないようにする。ただし抽出される mutant が変わり、`logs/final` と対応しなくなるので、論文用の計測が終わってから行う。

## bench: 計測フェーズで最初に走る target だけが遅く出る

2026-10-09 に調査した。計測フェーズ（`Bench_runner`）で最初に走るプロセスは、バイナリに関係なく 1 割ほど遅く出て、その状態が 1 時間ほど続く。今の target の順では、fsm の `untypedALHMT` が毎回これに当たる。

- 証拠: `logs/20261008-20:15:54`（`--all … --cpu 72`）では、coercion の操作が一度も起きない fsm の 10 mutant（`alloc = 0` かつ `compose = 0`）で、どのモードも `untypedALHMT` に対して 0.87〜0.90 になった。ほかのベンチの同じ種類の mutant では、ALh も typed も 1.00 になる。`ALhMT / ALHMT` は最初の約 250 mutant（最初の 1 時間強）で 0.90〜0.95、その後は約 1.0 だった。修正前の 2 回の計測（`20261007-17:57:13`、`20261008-10:16:20`）も、同じく最初が fsm の `untypedALHMT` で、同じ傾向だった
- 確認用ドライバ（`logs/20261008-19:55:54/bench/check_{H,h}.out` の mutant 1）で、H と h のどちらを先に起動しても、最初のプロセスは 0.27〜0.29 s、その後は 0.25〜0.26 s になった。遅さはバイナリではなく順番についてくる。原因（CPU の周波数や C-state、直前の並列コンパイルの後始末など）は特定していない
- 当面の対処: 論文用の fsm `untypedALHMT` は、ダミーの実行（`check_h.out` で mutant 1 を 600 回、約 2.5 分）の後に単独で測り直し、`logs/20261008-20:15:54/untypedALHMT_fsm.jsonl` の `times_sec` を差し替えた（元のファイルは `untypedALHMT_fsm.jsonl.first_run_bak`）
- 恒久対策の案: `Bench_runner.run_batch` の最初に、捨てる run を入れる（例: 最初の target のバイナリを一度空回しする、または数分のダミーの負荷をかける）。今後のどの計測でも最初の target が不利にならなくなる。ただし過去のログと比べる基準が変わるので、論文用の計測が終わってから入れる

関連して、落ち着いた状態でも hash consing ありのバイナリは、GC が支配的な fsm で約 3% 遅い（mutant 1 で H 0.257 s、h 0.249 s）。hash モードでは `.data` が約 1.5 MB 大きく（static な crc が 0.77 → 1.55 MB、`static_crcs_arr` が 0.56 MB）、Boehm GC が GC のたびに root としてスキャンするため、と見ている（1 run で約 210 回 GC する。直接の因果は未確認）。static な crc を GC の root から外す（`GC_exclude_static_roots` など。static な crc はヒープを指さないことが前提）と消せる可能性がある。

## stdlib の CUnimplementedを消す

## 「Boxed」的な汎用タグの導入

個々の新しい型ごとに ground tag を1つずつ消費するのをやめ、「boxed／拡張型」を表す **共通の1つの ground tag** を用意し、その中身（ヒープ確保したオブジェクトの先頭）に実際の型を示す小さな種別フィールドを持たせる2段構成にする。こうすれば、3bit の ground tag 空間を増やさずに任意個の「低頻度・後発の型」を追加できるようになる（float 含め今後増える型はすべてこの Boxed タグ配下に统合する運用も考えられる）

## NaN Tagging による再実装の検討

現在の「ポインタ/整数の下位ビットを盗んでタグ化する」方式を、IEEE754 の double が持つ NaN のペイロードビット（quiet NaN で約51bit）を使ってタグと小さな payload を埋め込む「NaN タギング」方式に置き換えることを、より抜本的な将来の再設計として検討する。JS エンジン（V8 の Smi/HeapObject、JavaScriptCore の NaN-boxing 等）で使われる手法で、ポインタか即値かを下位ビットで判別する現行方式より柔軟に型を詰め込める可能性がある。ただし `value` の表現（`libC/types.h:42` の `typedef intptr_t value;`）や `tag_value`/`untag_value`/`cast`/`coerce` 全体に及ぶ大規模な再設計になるため、実際に着手するかどうかは別途判断する

## blame ラベルの伝播が未実装

monotonic reference/array の deref・subst（`GetExp`/`PutExp`/`DerefExp`/`SubstExp`）で `make_s_coercion` を呼ぶ際、実際の blame range/polarity ではなく `Utils.Error.dummy_range, Pos` を仮置きしている。`compose` が `CMRef`/`CMArray` の unify に失敗して `CFail` を生成する箇所も同様に dummy range を使っている。C ランタイム側の `make_s_coercion`（`libC/crc.c:883`）にも同じ制約がコメントで明記されている。

- `lib/utils/coercion.ml:97` — `compose` 冒頭の `(* TODO: blame *)`
- `lib/utils/coercion.ml:312,325` — `CMRef`/`CMArray` の unify 失敗時に生成する `CFail` が dummy range 固定
- `lib/interpreter/eval.ml:222,242,276,301,620,624,630,634` — `DerefExp`/`SubstExp`/`GetExp`/`PutExp` の monotonic 経路
- `libC/crc.c:883` — `make_s_coercion`（C 版）が同じ理由で blame label 未対応とコメントされている

正しい blame range を持たせるには、これらの呼び出し元まで元の cast 式の range を伝播させる必要がある（未調査）。

なお `lib/backend/toC.ml` の `monotonic_dummy_range`（deref/subst/get/put 向けの効率的な coercion 生成パス、[history.md](history.md) 参照）は名前が似ているが別物: こちらは「`TyDyn` との合流点を判定するための、コンパイル時にのみ使う実体のないダミー range」であり、上記の「実行時 blame に本来必要な range が来ていない」という問題とは無関係。

## `--static`/`--hash`/`--tvs_opt` の未対応の組み合わせ

- `lib/config.ml:33,35,37,39` — `--hash`/`--static`/tvs 最適化はコンパイルモード専用で、インタプリタ実行時に指定すると `NotImplemented` で `failwith` する
- `lib/backend/static_manage.ml:150` — `--static` モードで `TyCoercion` 型が来ると未対応（`Static_manage_bug "yet"`）
- `lib/backend/static_manage.ml:268` — `--static` モードで `CFail` coercion が来ると未対応（`Static_manage_bug "yet"`）

## CFail / 想定外の coercion・型が toC まで到達すると不親切なエラーになる

`lib/typing/typing.ml:345`（`type_of_coercion (CFail _) = assert false`）と同様の問題が `toC.ml` にも複数箇所ある。いずれも「通常の経路には現れない想定」だが、意図しない経路で来た場合にデバッグしづらいエラーメッセージになる。

- `lib/backend/toC.ml:71` — `toC_tycontent` が未知の `ty` パターンで `ToC_bug "toC_content yet"`
- `lib/backend/toC.ml:225` — `toC_crc` が `CFail` で `ToC_bug "toC_crc yet"`
- `lib/backend/toC.ml:354` — `set_ty` が未知の `ty` パターンで `ToC_bug "set_ty yet"`

## `let (a,b,c) = e in ...` タプルパターン束縛のパターン変数は単相

`let (a,b,c) = e in ...`（`lib/frontend/parser.mly` の `LetExpr`/`LetPattern`）は既存の `.field` アクセサ等と同じイディオムで、単一ブランチの `MatchExp` に脱糖して実装している。しかし通常の `LetExp` が右辺 pure value のとき得る let-polymorphism（`lib/typing/typing.ml:262-269`）と異なり、`MatchExp` の各ブランチのパターン変数は `env_of_mf`（`lib/typing/typing.ml:49-59`）により単相にしか束縛されない。そのため `let (f, g) = ((fun x -> x), (fun x -> x)) in (f 1, g true)` のように、個別には多相な値をタプルパターンで受けた場合は型エラーになる（`f`/`g` がどちらも単相インスタンスにしかならないため）。

（`let (f, g) = (id, id) in (f 1, g true)` のように別々のパターン変数を1回ずつ使うだけなら単相でも問題なく通る。単相性が実際に問題になるのは `let (f, g) = (id, id) in (f 1, f true)` のように同じパターン変数を複数の型でインスタンス化しようとしたとき。）

対応する場合は `env_of_mf`/`MatchExp` の型付け側でブランチごとに generalize するよう変更する必要があり、`match` 全体の意味論に関わる別の大きな変更になる。現状は既知の制限として受容している（回帰テストは `test/test_typing.ml` を参照）。

## monotonic ref/array coercion の `has_tv` が未設定

`libC/crc.c:325`（`new_mref`）・`crc.c:345`（`new_marray`）で `has_tv` フィールドがコメントアウトされたまま（`/*.has_tv = TODO yet, */`）になっており、実質 0 固定。`CMRef`/`CMArray` の runtime crc が型変数を含んでいても `has_tv` に反映されない。non-monotonic 版（`new_ref`/`new_array`）は `c1->has_tv | c2->has_tv` を正しく設定しているのと対称性が崩れている。影響範囲は未調査。

## bench のインタプリタ計測（廃止済み・復活は要検討）

`f2a9c0a`「refactor bench」で bench はコンパイル専用になり、インタプリタの時間/メモリ
計測（旧 `mem_json` の `Failure "yet"`、旧 `Text` out_mode）と core_bench 基盤は削除した。
mutation 後プログラムがインタプリタで評価まで通るかの回帰は `test/test_mutate.ml` の
差分カバレッジテストでカバーしている。

インタプリタ計測を復活させる場合は (a) サンプルが stdin 入力を要求する形式に変わった
ことへの対応（`samples/input/<name>.txt` を評価時に流す）、(b) 計測基盤の再導入が必要。
旧実装は `f2a9c0a` 以前の git 履歴（`Translate.CC.translate` / `translate_alt` →
`Eval.CC.eval_program` を `measure_mem_to_json` で包む形）を参照。

## その他の小さな TODO（旧リストから継続）

- **`Cls.Cast` 周りの base_inj/base_proj シングルトン化**（旧 TODO）は、ショートサーキット最適化（インライン展開でディスパッチを消す方式）によって実質的に置き換えられた。まだ性能が問題になる場合のみ再検討する。
- `lib/frontend/lexer.mll:113` — コメントが閉じられないまま EOF に達した場合、`Format.eprintf` で警告を出すのみで例外を送出していない。
- `lib/utils/utils.ml:56` — `Utils.Lexing` モジュールの存在意義が不明なコードに `(* TODO: why does it exist? *)` が付いたまま。
- `lib/utils/pp.ml:85` — `gt_binop`（演算子の pretty-print 用の優先順位比較）に `(* TODO: replace to level *)`。優先順位を表す `level` のようなものに置き換えたいという意図と思われるが未着手。
- `bin/main.ml:28` — ファイルモード実行時、プログラムが正しく書けていなくてもコンパイルが通ってしまうことがある（例: `bad.ml`）。原因未調査。

## 多相関数の coercion テンプレートのキャッシュと、型変数が解決された後に残るコスト（loop で Grift に負ける）

2026-09-27 に調査・試作した。効果は確認できたが、込み入っていて論文で説明しにくいので一旦差し戻した。後で「さらなる最適化」として実装する。

**現象**（logs/20260926-19:17:54、untypedALHMT）: loop #19（`let rec loop (n: ?) (acc: ?) f = ... in let id = fun (x: ?) -> x in ...`）は当方 90ms、Grift 47ms。cast 数はほぼ同じで、1 回あたりのコストが約 2 倍。当方が Grift に負けている loop の mutant は、ほぼ「`acc: ?`、`id` が `? -> ?`、f は注釈なし（推論）」の形（#13/#19/#25/#29）に限られる。f に `?` を付けるだけの mutant（#24/#28/#31/#32）は 24〜32ms で、Grift（62〜65ms）より速い。

**原因**: f の型が型変数 `X1 -> X0` と推論され、`let rec` で一般化されることで、次のコストがかかる。
- toC は、実行時の型変数（クロージャ環境から読む `_tyN`）を含む coercion を「テンプレート」として出力し、実行のたびに `crctmpN = (crc){...}; alloc_crc(&crctmpN)` で組み立てる。型変数が最初の 2 回の DTI で解決済みでも、毎回 `alloc_crc` → `normalize_tv` → intern 検索をやり直す
- main で `id : ? -> ?` を `X1 -> X0` へ coerce するので、id は関数プロキシ（`fun_wrapped_call_funcD`）になる。プロキシが持つ `crc2 = C_FUN(ty1!, ty0?)` は、`ty0`/`ty1` が未解決の時点で作られた static な C_TV の coercion で、解決後も C_TV のまま残る。そのため f を呼ぶたびに、引数への `ty1!` の適用（`capp.c` の C_TV 適用）と、継続への `ty0?` の合成（`crc.c` の左 C_TV の合成）で `normalize_tv` が呼ばれ、`new_id` → `alloc_crc` → intern 検索が走る（各 100 万回。型変数は全部解決済み）。`crc2` は `has_tv = 1` のままなので、compose のメモ化にも載らない

**試作した実装 1: テンプレートの出力箇所ごとのキャッシュ**（`lib/backend/toC.ml` のみ）:
- `Cls.Coercion` でテンプレートを `alloc_crc` している箇所に、ファイルスコープの static なキャッシュ（`crccacheN_e`、`crckeyN_e_i`）を出力する。キーはテンプレート全体（入れ子を含む）に現れる実行時の型変数のポインタの組。キーが一致すれば、子の `alloc_crc` も含めてまとめて飛ばす。入れ子は一番外側だけキャッシュする
- `alloc_crc` の結果が `has_tv == 0` のときだけ登録する。型変数を含まない crc は後から変わらない（DTI が書き換えるのは TYVAR ノードだけ）ので、キーが一致すれば同じ結果になる。未解決の間は毎回 `alloc_crc` するので、DTI の挙動は変わらない
- static な型（`&tyint` や `&tyN`）はキーに入れない。解決は一方向で、bench の `set_tysN()` で static な型変数を戻すときにキャッシュも NULL に戻す。bench の driver は `set_tysN()` と `clear_crc_caches()` を必ず対にして呼ぶので、intern 表を捨てたあとに古いポインタが残ることもない
- キャッシュを出さない条件は次のとおり
  - 関数本体の `SetTy` が `GC_MALLOC` する型変数をキーに含むもの。呼ぶたびにポインタが変わるので必ず外れる。ただし `For`/`While` の本体では、ループの外で束縛されたものは反復の間変わらないので除外しない
  - キーが空のもの
  - 静的に `has_tv = 1` で、かつ C_TV でないもの（キーが実行時の型変数の mref/marray。結果も必ず `has_tv = 1`）
- エントリ数は 2 にした（FIFO）。church は同じ箇所に 2 つの型が交互に来るので、1 エントリでは取りこぼす
- ALT で同じテンプレートが `fun_X` と `fun_alt_X` の両方に出力されても、`crctmpN` と同じ単位でキャッシュを共有する（結果はテンプレートとキーだけで決まるので正しい）
- `toC_crc_dyn`（monotonic の dyn 分岐）は対象外にした。下の 5 ベンチでは出力箇所が 0 だった

**試作 1 の効果**（全 mutant の PROFILE の合計。時間は `GC_INITIAL_HEAP_SIZE=64MB` で K0/K1/K2 を交互に 5 回ずつ計測した中央値。データは `logs/20260927-13:25:18`（キャッシュなし）、`13:27:33`（1 エントリ）、`13:29:25`（2 エントリ））:

| ベンチ | alloc_crc 削減（1 エントリ） | 同（2 エントリ） | 時間比（2 エントリ/なし） |
|---|---|---|---|
| loop | 88.0% | 88.0% | 0.78 |
| church-65536 | 53.5% | 86.4% | 0.74 |
| tak | 94.6% | 94.6% | 0.98 |
| array | 97.8% | 97.8% | 0.99 |
| quicksort | 0% | 0% | 1.00 |

- loop #19 は 87.3 → 73.3ms。テンプレートは 1 回の実行で合計 5 回しか外れない（最初の未解決の 1 回と、解決後の登録の 1 回）。残りの `alloc` 100 万回と `normalize_tv` 200 万回は、上のプロキシによるもので、テンプレートではない
- quicksort のテンプレートは全部キーが実行時の型変数の `marray_crc`（`has_tv = 1`）で、キャッシュに載らない
- `dune runtest`、`compile_test/mutation_test.sh`、`compile_test/dotests.sh` はすべて通った
- array #51 だけ 9.0 → 10.5ms と毎回遅くなった。差分は 1 回の実行で約 100 回しか通らない `create_x` のキャッシュのコードだけなので、コード配置の影響と思われる（未確認）

**残りの差の内訳**（loop #19 の生成 C を手で書き換え、単独ビルド・5 回の最良値で積み重ねて計測。v1 以降は型が解決済みだと分かっている前提の書き換えなので、実装するなら解決済みかどうかの実行時の分岐が要る）:

| 版 | 外したもの | 時間 |
|---|---|---|
| 試作 1 のコード | — | 71.4ms |
| d | プロキシの C_TV の coercion を最初から正規化済みにする | 55.8 |
| v1 | + 解決済みのテンプレートを静的な高速経路にする（`apply_coerce_proj`、`&crc_inj_INT`） | 50.2 |
| v2 | + クロージャの環境から型引数 3 つを外す | 41.7 |
| v3 | + プロキシを経由せず、呼ぶたびの `compose(int?, k)` もやめる | 33.0 |
| v4 | + id の中の `int?;int!` を汎用の `apply_coerce` から高速経路にする | 28.2 |
| 参考: #28（f が `?`） | | 30.4 |

**今後の候補**:
- （libC）C_TV の crc に、`normalize_tv` の結果を覚えさせる。解決済みなら crc 自身に書き戻すか `norm` ポインタとして持たせる。あるいは、プロキシを適用するときに中の coercion を正規化したものへ差し替える。上の d に当たり、効果が最も大きい（約 15ms）
- （toC）形が決まっているテンプレート（`X?p`、`X!`）は、キャッシュを引く代わりに「`tv` が `BASE_INT` なら `apply_coerce_proj(v, G_INT, …)`」のように、型変数の中身で分岐する高速経路を出力する。試作 1 より安く済む可能性がある（v1）
- （libC）プロキシに「前回の継続 k とその合成結果」を 1 エントリ覚えさせ、呼ぶたびの compose をなくす（v3 の一部）
- （libC）汎用の `apply_coerce` に、基底型の射影と注入（`int?;int!` など）の高速経路を足す（v4）
- 型引数の受け渡し（v2、約 8.5ms）が、この実装で多相に固有なコスト。型変数は DTI とキャッシュのキーに必要なので単純には外せない。カリー化した部分適用のたびにクロージャを割り当てること自体を減らす（uncurry する）ほうが効きそう。時間の大半がコピーではなく割り当て量（GC）だというのは未確認
- 型の hash consing（上の「型のhash consing」の節）との関係: キーを生のポインタではなく解決後の型の正規ノードにすれば、「呼ぶたびに新しい型変数が、毎回同じ型に解決される」場合もヒットするようになる。ただし、そのテンプレートの `alloc_crc` より前に解決されている必要があり、今のベンチでは伸びしろは小さい見込み

## テストの TODO（コメントアウトされたまま復活していないケース）

以下のテストファイルに、期待値の記述が難しい／未対応機能のためコメントアウトされたままの `(* TODO: ... *)` ケースが残っている。個々の内容は各ファイルを参照。

- `test/test_pp.ml:145,165,168,171,172`
- `test/test_typing.ml:165`
- `test/test_translate.ml:27,40`

---

## 完了済み

過去に完了した TODO は随時この節から削除し、詳細は [history.md](history.md) に記録する（現時点でこの節は空）。
