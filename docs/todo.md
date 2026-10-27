# todo — 残作業

[CLAUDE.md](../CLAUDE.md) から参照される用途別ドキュメントの一つ。「次に何をやるか」をここに集約する。
経緯は [history.md](history.md)、使い方は [howto.md](howto.md) を参照。

新しく着手する前に、まず `git log` と `dune runtest`/`compile_test/dotests.sh` を実行して以下がまだ有効か確認すること（実装は git log の方が正しい）。
このリストは `grep -rn "TODO\|FIXME\|yet"` で拾えるものを中心に棚卸ししたもの（初出 2026-08-08、行番号は 2026-09-19 時点のものに更新済み）。

---

## 型のhash consing
mref, marrayのcoercionのhash consing導入に必須
単純に実装しようとすると、DTIの実装の変更が必須

- 背景: monotonic の `C_REF`/`C_ARRAY` の crc は `ty*` をキーに持ち、`intern_table` はポインタで比較する。`unify_meet` は複合型を毎回新しく確保し、DTI で解決された型も型変数ごとに別ノードになるため、型を正規化しないとキーが一致せず intern が効かない。現状は `new_mref`/`new_marray` で `has_tv = 1` に固定しており（安全側）、mref/marray の crc は intern も compose cache も使われない
- 一度試した実装（取り消し済み）: `ty` に `has_tv` を持たせ、`has_tv == 0` の型を crc と同じ方式の表で intern する（`alloc_ty`、static な型は `set_static_tys` で登録）
- 問題点: `dti` は複合型の子を `newty()` で作って後から上書きし、基本型にも `*tv = tyint` のコピーで解決する。そのため親の `has_tv` が DTI 後も 1 のまま残り、子も正規ノードにならない。crc の `recompute_has_tv` のように1段見るだけでは足りず（`X := [Y]`, `Y := Y1 -> Y2` など2段以上ネストすると 0 に落ちない）、毎回部分木を再帰的に辿る必要がある
- toC 側も揃っていない: crc は局所的なもの（crctmp）も `alloc_crc` を通すが、ty の `SetTy` は `GC_MALLOC` して直接代入するだけで生成の入口がない。型を hash cons するなら crc と同じ「テンプレート + `alloc_ty`」に揃えるのがよい（`create_new_ty` がタプル配列をコピーすれば `heap_tuple_arr` も不要）
- DTI 側の案: 型変数を解決するときに中身を上書きせず `SUBSTITUTED` にして正規ノードを指させれば、子が常に正規ノードになり、再帰的な辿り直しが要らなくなる。ただし `ty_find` の回数が増えるので、その性能とのトレードオフになる

## 小さい heap での計測アーティファクト（仕組みは判明、既定 8MB で回避）

ML 側のベンチ driver は 1 プロセスで全 mutant を順に計測する（`Bench_compiler.generate_bench_sources`）。初期 heap が小さいと、GC の回数が型や cast と無関係な理由で変わり、計測値が大きく動く。ベンチの既定 heap は 8MB（`Bench_config.default_heap_size`、`--heap-size` で変更可、grift 側にも `-m` で同じ値）。

**2026-09-28 に分かったこと**（診断 driver で mutant を単独実行し、GC 回数・GC 後の生存量・ページフォルトを計測）:
- Boehm は heap が小さいうちは「生存データ量 ÷ free_space_divisor」を確保するごとに GC する。そのため、保守的 GC が古い配列を偽参照で残す（生存量が増える）と、GC の間隔が広がり回数が減って**速くなる**。以前ここに書いた「残ったデータが原因とも言い切れない」はこれで説明がつく（残る方が GC が少ない）。
- 4MB・array（入力を 500 100000 に増やし配列 1 本 800KB）: 最も静的な mutant などは GC 250 回/実行（約 80ms）、`create_x (n: ?)` を含む mutant などは 200 回以下（約 47ms）に分かれ、cast 数と無関係に時間が 2 値になった。GC 後の生存量は、遅い側が約 10KB、速い側が約 800KB（配列 1 本）。typed/untyped で cast 数が同じ mutant でも側が入れ替わる。8MB では全 mutant が GC 100 回にそろい解消（16MB でも 50 回にそろう）。以前 4MB で再現しなかったのは、配列が 400KB（heap の 1/10）だったため。
- fsm の tvs_opt on/off の逆転（off が約 6% 速い）も同じ仕組みで、4MB では off の生存量がわずかに多く GC が 6% 少なかった。8MB では GC 回数がそろい（322 対 326）、off が 3% 遅いという仕事量どおりの結果になる。
- 1MB は GC がさらに多く、同じバイナリでも別プロセスで GC 回数が変わる（fft で最大 118 回、時間で最大 28% の差）。
- 逆に 16MB 以上では、1 回の確保が少ない church（約 2.3MB/回）が warmup 5 回で heap を一周しきれず、計測中にもページフォルト（約 600 回/実行）が入り、最も静的な mutant が 1.5〜2 倍遅く測られる。8MB なら warmup 中に一周し終わる。
- 以上から既定を 8MB にした。array 以外のベンチ（loop/tak/blacksholes/n_body/fft/quicksort/fsm）は 1〜64MB の範囲で、「最も静的な mutant に対する比」の変化が別プロセス間のばらつき（5〜12%、短い church/quicksort は 20〜50%）の範囲に収まった。

以下は 1MB 時代の記録。

- 症状: `logs/20260926-19:17:54` の array で、hash あり/なしの幾何平均比が 1.7 倍。heap は 2.7MB で頭打ちのまま、hash ありだけ GC 回数が mutant あたり約 335 回から 657〜1000 回に増え、プロセスの最後までその状態が続く。
- 再現性: clang 18.1.8 + libgc 7.6.4 はホストも Docker も同じ。それでも同じバイナリを繰り返し実行すると、比が 1.7 になる回と 1.0 付近の回がある（2026-09-27、Docker で 1MB を 6 回実行して 2 回再現。ホストでは 1 回試して再現せず）。アドレス配置（ASLR）への依存が疑われる。mutant 11 と 13 だけをリンクした最小構成では再現しなかった。
- 分かっていること（診断用 driver: `logs/20260927-11:57:52/bench/*_diag*.c`）:
  - 各 mutant の後に `GC_gcollect()` を呼んでも、hash あり/なしの両方で 400KB 単位（array の配列 1 本 = 5 万要素 × 8B）、最大 1.2MB のデータが回収されずに残る。残っているのは intern 表ではなく、以前の実行の配列と思われる。
  - その前に 128KB 分のスタックをゼロクリアしても、残る量は変わらない。つまりスタック上の古い値が原因ではない。静的領域・レジスタ・heap 内の別オブジェクトのどれから参照されているかは未調査。
  - hash なしでも同程度に残るのに、GC 回数は増えない。そのため「残ったデータが原因」とも言い切れていない。
  - mutant 間に `GC_gcollect()` を挟むと 8 回とも比は 0.94〜1.10 に収まった。ただし hash ありの GC 回数が 3 割ほど増える mutant は 70 個中 5〜9 個残った。挟まない版も多くの回で 1 付近なので、効果は判断できない。
- heap サイズを変えた比較（Docker、array、各 6 回）:

  | 初期 heap | H/h（6 回分） | hash ありの GC 回数 最大/中央値 |
  |---|---|---|
  | 1MB | 1.02 1.05 1.71 1.06 1.73 1.02 | 1.50〜2.99 |
  | 4MB | 1.01〜1.02 | 1.00 |
  | 8MB | 1.00〜1.01 | 1.01 |
  | 16MB | 0.99〜1.02 | 1.00 |

- 残作業:
  - 何が配列を参照し続けているのかを特定する（Boehm の `GC_DEBUG` + `GC_generate_random_backtrace` などを使う）。
  - 大きな配列を `GC_MALLOC_IGNORE_OFF_PAGE` で確保すると、内部ポインタによる偽参照が減るかどうかも試す価値がある。

## mutant のサンプリングがホスト（OCaml 4.14）と Docker（OCaml 5.2）で異なる

スロット数が `mutation_slot_threshold`（6）以上の対象は `Mutate.sample_subsets_by_length` で部分集合を抽出する。種は `(n, samples_per_slot)` から作る `Random.State` なので同じ環境なら毎回同じだが、OCaml 5.0 で乱数生成器のアルゴリズムが変わったため、ホスト（4.14.1）と Docker（5.2.0）では同じ `mutant_index` が別のスロット選択を指す（2026-09-29 確認: `logs/fsm`（09-27）と `logs/final` の fsm（09-29）はどちらも Docker で 650 件すべて一致。ホストで生成したものとは 1 番と最後の番号以外が違う）。

- 影響: ホストで流す `compile_test/mutation_test.sh` / `test/check_mutants.exe` / ホストでの `bench.exe` は、Docker で計測した mutant とは別の mutant を検査している。loop（5 スロット）と tak（4 スロット）は全列挙なので影響しない。
- 当面の対策: 計測した mutant そのものを検査したいときは Docker の中で流す。ホストのログと Docker のログを `mutant_index` で突き合わせない。
- 恒久対策の案: 自前の小さな PRNG（xorshift など）に置き換えて OCaml のバージョンに依存しないようにする。ただし抽出される mutant が変わり、`logs/final` と対応しなくなるので、論文用の計測が終わってから行う。

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

## monotonic ref/array coercion の `has_tv` が応急処置のまま

`libC/crc.c` の `new_mref`/`new_marray` は、キーの型 `u` が型変数を含むかを見ずに、安全側に倒して常に `has_tv = 1` にしている（`new_mref_tv`/`new_marray_tv` に 1 を渡す）。has_tv = 0 になるのは、toC が出力した static crc（型変数を含まないもの）どうしを `compose` したときだけ。そのため実行時に作る mref/marray の crc は intern されず、compose cache にも載らない。

`new_mref` の時点で `u` を `ty_find` しながら辿り、型変数が残っていなければ `has_tv = 0` にすれば、実行時の mref/marray crc も hash-consing の対象にできる。型を辿るコストとの兼ね合いなので、ベンチで効果を確かめてから入れる。

その際、intern 表は mref/marray のキーを型のポインタで比較する（`hash_crc`/`eq_crc`）ので、構造が同じでもポインタが違う型は共有されない。`compose_mkey` と同じ発想で、has_tv = 0 のキーを代表のポインタに寄せる（Dyn・base 型なら `ty.c` の static な `tydyn`/`tyint` などを使う。複合型まで寄せるなら型の hash-consing が必要）と効果が上がる。複合型まで寄せる方法は、上の「型のhash consing」の節を参照。

## alt モードの funcD 入口の恒等判定（I6）を呼び出し側の情報で省く

I6（`lib/backend/toC.ml` の `toC_fundef`）は、alt モードのすべての `fun_<name>`（FundefD）の先頭で `k == &crc_id` を判定し、恒等なら双子の `fun_alt_<name>`（FundefM）に乗り換える。呼び出し側で `k` が恒等でないと静的に分かっている場合（`k` が static な非恒等 crc、`CComp` の結果が非恒等と分かる場合など）でも、毎回この判定を通る（-O3 では cmp+分岐 1 回で、乗り換え先はインライン展開か末尾呼び出しの jmp になる）。

- 判定なしの入口（例: `fun_<name>_k`）を別に出力し、`k` が非恒等と静的に分かる AppDDir/AppDCls ではそちらを呼ぶ。クロージャ経由の呼び出しでは `fun` 構造体に入口を1つ足す必要がある
- 逆に、恒等かどうかを呼び出し側で判定して `funcM`/`funcD` を呼び分ける形（`libC/app.c` の `fun_wrapped_call_funcD` がランタイムでやっているのと同じ）も比較対象。こちらは呼び出し箇所ごとにコードが増え、C ランタイム（app.c・stdlib）からの `funcD` 呼び出しには効かない

どちらも、現状との差は判定 1 回分なので、ベンチ（特に関数呼び出しの多い tak/fib/church）で効果を測ってから決める。

## typed ベンチの original / GTP_benchmark に返り値と let の型注釈がない

`samples/src_gradti/typed/grift_benchmark/` は、Grift 版が型注釈を書いている箇所（関数の返り値・`let` 束縛）すべてに同じ注釈を付けてある（v2.0 の `4ad7bba`）。引数を Dyn 化した mutant で、推論される結果の型に `?` が漏れ出さないようにするため。`typed/original/` では `loop.ml` だけが同じ形になっていて、残りの church-2/church-4/church-65536/easy/evenodd/explosion-DTI/fib/fold/incsum/map/mklist/zipwith と `typed/GTP_benchmark/fsm.ml` は、関数の引数にしか注釈がない箇所が残っている。Grift 版が無いので「Grift と同じ箇所」という基準は使えず、`loop.ml` と同様に、返り値の型と `let` 束縛すべてに明示的な注釈を付ける。スロット数は変わらない（注釈を足しても slot は増えない）ことを、typed 軸の前処理（スロット対応）と `test/check_mutants.ml --typed` で確かめる。

## testC（C ランタイムの単体テスト）が手薄

`testC/` は Unity で `compose`（libC/crc.c）の結果を手書きのケースと突き合わせるだけで、`coerce`/`apply_coerce` 系（capp.c/capp.h）、`make_s_coercion*`、hash-consing（intern 表・compose cache）、monotonic ref/array（`read_to_dyn`/`write_from_dyn`/`consume`）、型変数の具体化（DTI）などは単体では検査していない。また `testC/dotests.sh` はどこからも呼ばれておらず（CI・`dune runtest`・`compile_test/` のいずれにも入っていない）、ビルド時のフラグも付けないので MONOTONIC/HASH/EAGER 等の構成ではテストしていない。ケースを増やし、構成ごとに回し、`dune runtest` か CI から呼ぶようにする。

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
- `lib/utils/resources.ml:19` — `LSDTI_ROOT_DIR` による project root の上書きがコメントアウトされているのに、root が見つからないときのエラーメッセージは「`LSDTI_ROOT_DIR` を設定せよ」と案内している。上書きを復活させるか、メッセージを `dune install` を促すものに直す。
- `libC/capp.c` の `coerce` 内（monotonic ref/array を即時に変換した直後）の `consume()` 2 か所は、toC が出力する Subst/Put と違って `consume_pending()` になっていない。意味は同じなので、揃えるかどうかは任意。
- `libC/crc.c` の compose cache は GC のスキャン対象外で、「has_tv == 0 の crc は intern 済みか static」という不変条件をコメントだけで守っている（`ensure_compose_cache`）。has_tv == 0 の crc を `alloc_crc` 以外の経路で作るコードを足すと黙って壊れるので、デバッグビルドで検査する仕組みを検討する。
- `compile_test/dotests.sh` のオプション一覧に hash-consing（`-h`）を有効にした組み合わせがない。HASH モードは `compile_test/mutation_test.sh` の 9 プログラムでしか検証されていない。

## monotonic ref/array の deref/subst/get/put（`Some u` 経路）の追加最適化

`lib/backend/toC.ml` の `make_s_coercion_call`（静的型 u に合わせて、実行時型 rtti を辿る crc 生成コードをコンパイル時に展開する）に残っている改善候補（2026-09-27 に検討）。

- **ref/array 要素の読み出しは実質恒等かもしれない**: `TyRef`/`TyArray` の `to_mref`/`to_marray` は、格納されている ref の実行時型と静的型 T の `meet` を取る。monotonic の不変条件（外側の実行時型は、どのビューの静的型と比べても同じかより精密で、格納値自身の実行時型はさらにそれと同じかより精密）が成り立つなら、この meet は何も変えないので、`coerce` を呼ばずに値をそのまま返せる。ただし、型変数（`TYVAR`/`SUBSTITUTED`）が絡む場合（DTI で後から解決される型を含むとき）にも成り立つかは未確認。確認できれば、読み出し側の `TyRef`/`TyArray` 分岐を削れる
- **複合型分岐の `rtti == DYN` の枝がデッドかどうか**: `Some u` になるのは u が Dyn を含む非静的型のとき（`translate.ml` の `is_static_type`）で、上の不変条件なら rtti の最外は u と同じ型構成子になるはず。`TyList`/`TyTuple`/`TyFun` の `DYN` 分岐（`dyn_branch`）が実際に通るかは、上と同じく型変数絡みを含めた確認が要る
- **「u 専用の読み書き関数」を生成する案は効果が小さい見込み**: `read_to_dyn`/`write_from_dyn`（`libC/capp.h`）を一般の u に広げる案を検討した。crc を割り当てずに済むのは、値がその場で決まる即値（Dyn・基底型）の位置だけで、そこは既存の関数ですでにカバーされている。関数や lazy なリスト・タプルは遅延ラッパーが必要なので、crc（相当）の割り当ては避けられない。静的型が基底型の場合は `None` 経路（直接アクセス）になるので、トップレベルで基底型専用の関数が呼ばれることもない。やるなら、ベンチで `make_s_coercion_call` 経路の割合を見てから判断する

## `?` 型の配列・ref を読んだ直後の射影（array/quicksort で cast 数が Grift の 1.5〜1.7 倍）

2026-09-27 に調査・試作した。効果は確認できたが、論文で説明しにくいので一旦差し戻した。後で「さらなる最適化」として実装する。

**現象**（logs/20260926-19:17:54、untypedALHMT と GRIFTCM の比較）: array の mutant（#26/#36/#52/#70）は当方 15.0M に対して Grift 10.0M。quicksort の mutant（#4 は 709,105 に対して 406,705、#15/#37/#100 も同様）。

**原因**: array #26 の `create_y (x: ?)` のループでは、`result.(k) <- x.(k)` 1 回ごとに次の 3 つの cast を実行している。
1. `apply_coerce_proj(x, G_AR)`：`x : ?` を配列へ射影する
2. `read_to_dyn`：静的な要素型 `?` で読むため、実行時型 int の要素を inject する
3. `apply_coerce_proj(_, G_INT)`：`? ⇒ int`

Grift（`rt_dyn_mvec_ref`）は 2 と 3 だけを数える。Grift の cast-profiler はコンパイル時に挿入した inject/project の箇所だけを数え、動的な vector-ref の中で行う配列のタグ検査は数えない。したがって、差の 5M は表面上は計数の定義の違いである。ただし当方には、次の 2 つの実際の無駄がある。
- **inject → project の往復**: 実行時型が int なら `int ⇒ ? ⇒ int` は合成すると恒等だが、毎回タグを付けて外している（Grift も同じ往復をしている）
- **支配された同じ射影の再実行**: 関数冒頭の `Array.length x` で `x` の `?⇒Array` 射影はすでに成功しているのに、ループ内の `x.(i)` のたびに同じ射影をやり直している

**試作した実装**（いずれも `lib/backend/toC.ml` と `libC/capp.h` のみで完結する）:
- **読み出しと射影の融合**: Cls 上で `let t = y.(z)@? in (let c = <coercion> in)* let w = t<c> in rest` の形を探す。条件は、c が `fast_proj` に登録された基底型の射影であり、t が rest で使われていないこと。見つかったら `w = read_to_ground(elem, u, G, rid, pol)` の 1 回に置き換える（`Deref (_, Some TyDyn)` も同様）。`read_to_ground` は次のように振る舞う。
  - 実行時型 u が G なら値をそのまま返す（PROFILE では cast 1 回として数える）
  - u が Dyn なら `apply_coerce_proj` だけを行う
  - それ以外（別の基底型・TYVAR 等）は `apply_coerce_proj(read_to_dyn(v, u), ...)` に戻すので、blame ラベルも含めて意味は変わらない
- **支配された射影の除去**（`elim_redundant_proj`）: toC の前に Cls → Cls の変換を 1 回かける。純粋なタグ検査だけの射影（`fast_proj`/`fast_proj_tp`）について、同じ変数への同じ種類の射影が支配位置の let ですでに束縛されていれば、`Let (w, Var 既存の結果)` に置き換える。Cls の変数は単一代入なので、avail を let 連鎖に沿って下へ流すだけでよい。If/Match/For/While の内側で束縛したものは外へ持ち出さない

**試作での効果**（PROFILE の cast 数。時間は修正前後のバイナリを交互に 40 回ずつ走らせた最小値で、プロセス起動を含む）:

| mutant | 修正前 | 試作 | Grift |
|---|---|---|---|
| array #26 | 15,000,602 | 5,000,502 | 10,000,702 |
| array #36/#52/#70 | 15.0M | 5.0M | 10.0M |
| quicksort #4 | 709,105 | 406,705 | 406,705 |
| quicksort #15 | 735,671 | 426,630 | 433,271 |
| quicksort #37 | 788,801 | 473,119 | 466,477 |
| quicksort #100 | 1,932,468 | 1,112,814 | 1,322,160 |

- 時間は array #26 が 15.6 → 12.1ms、#70 が 16.1 → 12.7ms。quicksort は誤差の範囲で、cast 以外が支配的だった
- `blame_check` は array #26 で 10,000,300 → 200 になった
- `dune runtest`、`compile_test/dotests.sh`、`compile_test/mutation_test.sh` はすべて通った。回帰テストとして `compile_test/original/array/` に `dyn_read.ml` と `dyn_read_blame.ml` を置いた（試作と一緒に削除済み）。前者の期待値は `68456`、後者は `a.(0) + 1` の射影位置（line 1, character 25–30）で blame する。どちらも `skip_static` を付ける

**残る論点**:
- 書き込み側の対称な融合（`Put (_, _, v, Some TyDyn)` の v が直前の基底型 inject だけでできている場合の `write_from_ground`）は未試作。今回のベンチでは効かなかった
- quicksort の partition の `x = a.(r)`（`?`）をループ内で毎回 `? ⇒ int` 射影している。最初の射影がループ内にあって支配関係がないので、上の除去では拾えず、ループ不変式の巻き上げ（LICM）が必要になる。Grift も同じく毎回射影しているので、cast 数は一致している
- quicksort で時間が縮まらない主因は、`swap a` を呼ぶたびに `? ⇒ int array` の coercion を新しく割り当てていること（new_crc 91,023）と思われる。これは normalize_tv/alloc_crc 側の課題
- 論文での位置づけ: 融合は「静的に隣接した coercion の合成を、実行時型が分かる読み出しの時点で行う」ものと説明できる。除去は一般的な CSE なので、DTI/space-efficiency の本筋とは分けて書く必要がある

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
