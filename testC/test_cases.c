#include <gc.h>
#include "test_common.h"
#include "unity.h"
#include "../libC/crc.h"
#include "../libC/ty.h"

// このファイルは compose() (../libC/crc.c) が実装している coercion 合成規則を
// 直接検証するテストケース集。
//
// 現行の crc 表現 (../libC/crc.h) は、旧実装のように proj/inj を別ノード
// (SEQ_PROJ / SEQ_INJ / SEQ_PROJ_INJ / TV_PROJ / ... ) として持つのではなく、
// 各ノード (crckind = C_ID/C_FUN/C_LIST/C_TUPLE/C_REF/C_ARRAY/C_TV/C_BOT) が
// has_proj/has_inj フラグと proj のラベル (p_proj, rid_proj) を直接持つ
// フラットな構造になっている。そのため、テストデータも
//   1. "中身" (has_proj = has_inj = 0 の coercion) を作る
//   2. with_proj / with_inj でラベル付きの proj / inj を被せる
// という2段階で組み立てる (test_common.h 参照)。
//
// ラベル (blame id) は old test と同様 p=0, q=1, r=2, s=3 とし、
// polarity は常に 1 とする (compose() 自体は polarity/rid の値を素通しする
// だけなので、値そのものに意味はなく、どこから来たかを追跡できれば十分)。
enum { P = 0, Q = 1, R = 2, S = 3 };
#define POL 1

extern ComposeTestCase* current_case;
extern void test_executor_bridge();

void run_manual_test_suite() {
    // --- よく使う coercion ---
    // int_p  = (int?p;)id(;int!)   : int <-> dyn を p でラベル付けした恒等 coercion
    // bool_q = (bool?q;)id(;bool!)
    // int_r  = (int?r;)id(;int!)
    // unit_s = (unit?s;)id(;unit!)
    crc *int_p  = with_inj(with_proj(new_ground(G_INT, 0), POL, P));
    crc *bool_q = with_inj(with_proj(new_ground(G_BOOL, 0), POL, Q));
    crc *int_r  = with_inj(with_proj(new_ground(G_INT, 0), POL, R));
    crc *unit_s = with_inj(with_proj(new_ground(G_UNIT, 0), POL, S));

    // proj のみ / inj のみの断片
    crc *int_p_proj  = with_proj(new_ground(G_INT, 0), POL, P);   // int?p;id
    crc *int_r_proj  = with_proj(new_ground(G_INT, 0), POL, R);   // int?r;id
    crc *int_id_inj  = with_inj(new_ground(G_INT, 0));            // id;int!

    // comp = int_p -> unit_s  (関数 coercion, 中身自体は proj/inj なし)
    crc *comp = new_fun(int_p, unit_s);

    ComposeTestCase cases[] = {
        // ============================================================
        // 恒等則
        // ============================================================
        {   "s ;; id = s",
            comp,
            new_id(),
            comp,
        },
        {   "id ;; s = s",
            new_id(),
            comp,
            comp,
        },

        // ============================================================
        // BOT: 一度 ⊥ になったら右から何を合成しても変わらない
        // (internal_compose: case C_BOT: return c1;)
        // ============================================================
        {   "bot(p) ;; s = bot(p)",
            new_bot(POL, P, 0),
            comp,
            new_bot(POL, P, 0),
        },
        {   "(int?p;)bot(q) ;; s = (int?p;)bot(q)",
            new_guarded_bot(G_INT, 0, POL, P, POL, Q, 0),
            comp,
            new_guarded_bot(G_INT, 0, POL, P, POL, Q, 0),
        },
        {   "(int?p;)occ_bot(q) ;; s = (int?p;)occ_bot(q)",
            new_guarded_bot(G_INT, 0, POL, P, POL, Q, 1),
            comp,
            new_guarded_bot(G_INT, 0, POL, P, POL, Q, 1),
        },

        // ============================================================
        // proj (has_inj=0) 同士 / proj と inj の合流
        // ============================================================
        {   "int?p;id ;; id;int! = int?p;id;int!",
            int_p_proj,
            int_id_inj,
            int_p,
        },
        {   "int?p;id ;; bot(q) = (int?p;)bot(q)",
            int_p_proj,
            new_bot(POL, Q, 0),
            // rewrite_proj は proj 側 (int?p) だけを被せ、bot の中身
            // (g/size, ここでは未設定=0) はそのまま引き継ぐ
            new_guarded_bot(0, 0, POL, P, POL, Q, 0),
        },

        // ============================================================
        // inj (has_proj=0) と ground coercion の合成
        // ============================================================
        {   "id;int! ;; int?p;id = id",
            int_id_inj,
            int_p_proj,
            new_id(),
        },
        {   "id;int! ;; int?p;id;int! = id;int!",
            int_id_inj,
            int_p,
            int_id_inj,
        },
        {   "id;int! ;; (int?p;)bot(q) = bot(q)",
            int_id_inj,
            new_guarded_bot(G_INT, 0, POL, P, POL, Q, 0),
            new_bot(POL, Q, 0),
        },
        {   "id;int! ;; (bool?q;)bot(r) = bot(q)  [型不一致なので guard 自身の label を blame]",
            int_id_inj,
            new_guarded_bot(G_BOOL, 0, POL, Q, POL, R, 0),
            new_bot(POL, Q, 0),
        },

        // ============================================================
        // proj_inj (has_proj=1,has_inj=1) 同士の合成
        // ============================================================
        {   "int?p;id;int! ;; int?r;id = int?p;id",
            int_p,
            int_r_proj,
            int_p_proj,
        },
        {   "int?p;id;int! ;; int?r;id;int! = int?p;id;int!",
            int_p,
            int_r,
            int_p,
        },
        {   "int?p;id;int! ;; (int?r;)bot(s) = (int?p;)bot(s)  [型一致]",
            int_p,
            new_guarded_bot(G_INT, 0, POL, R, POL, S, 0),
            new_guarded_bot(G_INT, 0, POL, P, POL, S, 0),
        },
        {   "int?p;id;int! ;; (bool?q;)bot(r) = (int?p;)bot(q)  [型不一致]",
            int_p,
            new_guarded_bot(G_BOOL, 0, POL, Q, POL, R, 0),
            new_guarded_bot(G_INT, 0, POL, P, POL, Q, 0),
        },

        // ============================================================
        // list: 子要素を再帰的に compose する / 両方 id に潰れたら
        // C_LIST ではなく id{G_LI} に潰れる
        // ============================================================
        {   "[int?p;id] ;; [id;int!] = [int?p;id;int!]",
            new_list(int_p_proj),
            new_list(int_id_inj),
            new_list(int_p),
        },
        {   "(int?p;)[id](;!) ;; (q?;)[id](;!) = int?p;id{list};int!  [両方の中身が id に潰れる]",
            with_inj(with_proj(new_list(new_id()), POL, P)),
            with_inj(with_proj(new_list(new_id()), POL, Q)),
            with_inj(with_proj(new_ground(G_LI, 0), POL, P)),
        },

        // ============================================================
        // ref: c1 (読み出し側) は素直に compose(a.c1, b.c1)、
        // c2 (書き込み側) は反変で compose(b.c2, a.c2) と「引数の順序が
        // 逆」になる。この非対称性を、proj のみ/inj のみの断片を
        // 組み合わせて (順序を間違えると結果が全く変わる) 検証する。
        // ============================================================
        {   "ref(int?p;id, id;int!) ;; ref(id;int!, int?p;id) : c1もc2も int?p;id;int! になる",
            new_ref(int_p_proj, int_id_inj),
            new_ref(int_id_inj, int_p_proj),
            new_ref(int_p, int_p),
        },
        {   "(int?p;)ref(id,id)(;!) ;; (q?;)ref(id,id)(;!) = int?p;id{ref};int!  [両方 id に潰れる]",
            with_inj(with_proj(new_ref(new_id(), new_id()), POL, P)),
            with_inj(with_proj(new_ref(new_id(), new_id()), POL, Q)),
            with_inj(with_proj(new_ground(G_RF, 0), POL, P)),
        },
        {   "(int?p;)ref(id,id)(;!) ;; (q?;)int(;!) : g が RF でないので mismatch bot",
            with_inj(with_proj(new_ref(new_id(), new_id()), POL, P)),
            with_inj(with_proj(new_ground(G_INT, 0), POL, Q)),
            new_guarded_bot(G_RF, 0, POL, P, POL, Q, 0),
        },

        // ============================================================
        // kind の不一致: どちらの proj/inj にも救われず即 bot になるケース
        // ============================================================
        {   "s1->s2(pure) ;; [t](pure) : FUN と LIST は型が違うので bot",
            new_fun(new_id(), new_id()),
            new_list(new_id()),
            new_bot(0, 0, 0),
        },
        {   "int?p;id;int! ;; (q?;)[id](;!) : id{int} と LIST は型が違うので bot",
            int_p,
            with_inj(with_proj(new_list(new_id()), POL, Q)),
            new_guarded_bot(G_INT, 0, POL, P, POL, Q, 0),
        },
    };

    int num_static_cases = sizeof(cases) / sizeof(cases[0]);
    for (int i = 0; i < num_static_cases; i++) {
        current_case = &cases[i];
        RUN_TEST(test_executor_bridge);
    }

    // ---- 型変数がからむケースは ty* を個別に生成しながら実行する ----

    {
        ty *x = newty();
        ComposeTestCase c = {
            "X?p ;; X!q = ?pX!q",
            with_proj(new_tv(x), POL, P),
            with_tv_inj(new_tv(x), POL, Q),
            with_tv_inj(with_proj(new_tv(x), POL, P), POL, Q),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }
    {
        // X?p ;; (int?r;)bot(q)[guard=int] : X は int に DTI され、
        // 結果は (int?p;)bot(q) (proj 側は X の proj ラベル p を引き継ぐ)
        ty *x = newty();
        ComposeTestCase c = {
            "X?p ;; (int?r;)bot(q) = (int?p;)bot(q)  [X は int に確定]",
            with_proj(new_tv(x), POL, P),
            new_guarded_bot(G_INT, 0, POL, R, POL, Q, 0),
            new_guarded_bot(G_INT, 0, POL, P, POL, Q, 0),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
        TEST_ASSERT_EQUAL_UINT8_MESSAGE(BASE_INT, x->tykind, "X should be resolved to int via dti");
    }
    {
        // X!p ;; int?r;id = id  (X は int に確定するが、両側とも proj/inj が
        // 残らないので最終的には id)
        ty *x = newty();
        ComposeTestCase c = {
            "X!p ;; int?r;id = id",
            with_tv_inj(new_tv(x), POL, P),
            int_r_proj,
            new_id(),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
        TEST_ASSERT_EQUAL_UINT8_MESSAGE(BASE_INT, x->tykind, "X should be resolved to int via dti");
    }
    {
        // X!p ;; bool?q;id;bool! = id;bool!
        ty *x = newty();
        ComposeTestCase c = {
            "X!p ;; bool?q;id;bool! = id;bool!",
            with_tv_inj(new_tv(x), POL, P),
            bool_q,
            with_inj(new_ground(G_BOOL, 0)),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
        TEST_ASSERT_EQUAL_UINT8_MESSAGE(BASE_BOOL, x->tykind, "X should be resolved to bool via dti");
    }
    {
        // X!p ;; (unit?s;)bot(q) = bot(q)
        ty *x = newty();
        ComposeTestCase c = {
            "X!p ;; (unit?s;)bot(q) = bot(q)",
            with_tv_inj(new_tv(x), POL, P),
            new_guarded_bot(G_UNIT, 0, POL, S, POL, Q, 0),
            new_bot(POL, Q, 0),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
        TEST_ASSERT_EQUAL_UINT8_MESSAGE(BASE_UNIT, x->tykind, "X should be resolved to unit via dti");
    }
    {
        // X!p ;; Y?q (どちらも未解決) = id  (X は Y に unify される)
        ty *x = newty();
        ty *y = newty();
        ComposeTestCase c = {
            "X!p ;; Y?q = id",
            with_tv_inj(new_tv(x), POL, P),
            with_proj(new_tv(y), POL, Q),
            new_id(),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
        TEST_ASSERT_EQUAL_UINT8_MESSAGE(TYVAR, y->tykind, "Y should remain a fresh tyvar");
    }
    {
        // X!p ;; ?qY!r = Y!r  (X は Y に unify され、外側は右側の proj/inj を引き継ぐ)
        ty *x = newty();
        ty *y = newty();
        ComposeTestCase c = {
            "X!p ;; ?qY!r = Y!r",
            with_tv_inj(new_tv(x), POL, P),
            with_tv_inj(with_proj(new_tv(y), POL, Q), POL, R),
            with_tv_inj(new_tv(y), POL, R),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }
    {
        // X?p ;; s1->s2 (X がドメインに再帰的に出現) = occurs check で ⊥
        ty *x = newty();
        crc *domain_with_x = new_tv(x);
        crc *fn = with_inj(with_proj(new_fun(domain_with_x, new_id()), POL, R));
        ComposeTestCase c = {
            "X?p ;; (r?;)(X->id)(;!) = occurs bot",
            with_proj(new_tv(x), POL, P),
            fn,
            new_guarded_bot(G_FN, 0, POL, P, POL, R, 1),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }

    // ============================================================
    // proj_inj な TV (?pX!q) 同士 / TV とグラウンド型との合成
    // ============================================================
    {
        // bool?q;id;bool! ;; X?p (proj のみの tv) = bool?q;id  [X は bool に確定]
        ty *x = newty();
        ComposeTestCase c = {
            "bool?q;id;bool! ;; X?p = bool?q;id",
            bool_q,
            with_proj(new_tv(x), POL, P),
            with_proj(new_ground(G_BOOL, 0), POL, Q),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
        TEST_ASSERT_EQUAL_UINT8_MESSAGE(BASE_BOOL, x->tykind, "X should be resolved to bool via dti");
    }
    {
        // bool?q;id;bool! ;; ?pX!r = bool?q;id;bool!  [X は bool に確定]
        ty *x = newty();
        ComposeTestCase c = {
            "bool?q;id;bool! ;; ?pX!r = bool?q;id;bool!",
            bool_q,
            with_tv_inj(with_proj(new_tv(x), POL, P), POL, R),
            bool_q,
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }
    {
        // ?pX!q ;; int?r;id = int?p;id  [X は int に確定、proj ラベルは X 側の p を引き継ぐ]
        ty *x = newty();
        ComposeTestCase c = {
            "?pX!q ;; int?r;id = int?p;id",
            with_tv_inj(with_proj(new_tv(x), POL, P), POL, Q),
            int_r_proj,
            int_p_proj,
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }
    {
        // ?pX!q ;; int?r;id;int! = int?p;id;int!
        ty *x = newty();
        ComposeTestCase c = {
            "?pX!q ;; int?r;id;int! = int?p;id;int!",
            with_tv_inj(with_proj(new_tv(x), POL, P), POL, Q),
            int_r,
            int_p,
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }
    {
        // ?pX!q ;; (int?r;)bot(s) = (int?p;)bot(s)
        ty *x = newty();
        ComposeTestCase c = {
            "?pX!q ;; (int?r;)bot(s) = (int?p;)bot(s)",
            with_tv_inj(with_proj(new_tv(x), POL, P), POL, Q),
            new_guarded_bot(G_INT, 0, POL, R, POL, S, 0),
            new_guarded_bot(G_INT, 0, POL, P, POL, S, 0),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }
    {
        // ?pX!q ;; Y?r (両方未解決 tv) = Y?p
        ty *x = newty();
        ty *y = newty();
        ComposeTestCase c = {
            "?pX!q ;; Y?r = Y?p",
            with_tv_inj(with_proj(new_tv(x), POL, P), POL, Q),
            with_proj(new_tv(y), POL, R),
            with_proj(new_tv(y), POL, P),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }
    {
        // ?pX!q ;; ?rY!s (両方 proj_inj な未解決 tv) = ?pY!s
        ty *x = newty();
        ty *y = newty();
        ComposeTestCase c = {
            "?pX!q ;; ?rY!s = ?pY!s",
            with_tv_inj(with_proj(new_tv(x), POL, P), POL, Q),
            with_tv_inj(with_proj(new_tv(y), POL, R), POL, S),
            with_tv_inj(with_proj(new_tv(y), POL, P), POL, S),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }

    // ============================================================
    // tuple: 配列を組み立てる必要があるのでここで個別に構築する
    // ============================================================
    {
        // (int?p;id, id) ;; (id;int!, id) = (int?p;id;int!, id)
        // 1要素目だけ int_p に合成され、2要素目は id のままなので
        // tuple 全体としては id には潰れず C_TUPLE のまま残る。
        crc **arr_a = GC_MALLOC(sizeof(crc*) * 2);
        arr_a[0] = int_p_proj;
        arr_a[1] = new_id();
        crc **arr_b = GC_MALLOC(sizeof(crc*) * 2);
        arr_b[0] = int_id_inj;
        arr_b[1] = new_id();
        crc **arr_exp = GC_MALLOC(sizeof(crc*) * 2);
        arr_exp[0] = int_p;
        arr_exp[1] = new_id();
        ComposeTestCase c = {
            "(int?p;id, id) ;; (id;int!, id) = (int?p;id;int!, id)",
            new_tuple(2, arr_a),
            new_tuple(2, arr_b),
            new_tuple(2, arr_exp),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }
    {
        // (p?;)(id,id)(;!) ;; (q?;)(id,id)(;!) : 全要素が id に潰れるので
        // tuple 全体が id{G_TP, size=2} に潰れる
        crc **arr_a = GC_MALLOC(sizeof(crc*) * 2);
        arr_a[0] = new_id(); arr_a[1] = new_id();
        crc **arr_b = GC_MALLOC(sizeof(crc*) * 2);
        arr_b[0] = new_id(); arr_b[1] = new_id();
        ComposeTestCase c = {
            "(p?;)(id,id)(;!) ;; (q?;)(id,id)(;!) = id{tuple2}",
            with_inj(with_proj(new_tuple(2, arr_a), POL, P)),
            with_inj(with_proj(new_tuple(2, arr_b), POL, Q)),
            with_inj(with_proj(new_ground(G_TP, 2), POL, P)),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }
    {
        // サイズ不一致 (2要素 vs 3要素) は bot、bot.size には LHS 自身の
        // サイズ (2) が残る
        crc **arr_a = GC_MALLOC(sizeof(crc*) * 2);
        arr_a[0] = new_id(); arr_a[1] = new_id();
        crc **arr_b = GC_MALLOC(sizeof(crc*) * 3);
        arr_b[0] = new_id(); arr_b[1] = new_id(); arr_b[2] = new_id();
        ComposeTestCase c = {
            "(p?;)(id,id)(;!) ;; (q?;)(id,id,id)(;!) : サイズ不一致で bot",
            with_inj(with_proj(new_tuple(2, arr_a), POL, P)),
            with_inj(with_proj(new_tuple(3, arr_b), POL, Q)),
            new_guarded_bot(G_TP, 2, POL, P, POL, Q, 0),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }
    {
        // X?p ;; (r?;)(X,id)(;!) : tuple の要素に X 自身が出現するので
        // occurs check により bot になる。size は tuple のサイズ(2)を保持する。
        ty *x = newty();
        crc **arr = GC_MALLOC(sizeof(crc*) * 2);
        arr[0] = new_tv(x);
        arr[1] = new_id();
        crc *tpl = with_inj(with_proj(new_tuple(2, arr), POL, R));
        ComposeTestCase c = {
            "X?p ;; (r?;)(X,id)(;!) = occurs bot (size=2)",
            with_proj(new_tv(x), POL, P),
            tpl,
            new_guarded_bot(G_TP, 2, POL, P, POL, R, 1),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }
    {
        // X?p ;; (r?;)ref(X,id)(;!) : ref の中に X 自身が出現するので occurs bot
        ty *x = newty();
        crc *rf = with_inj(with_proj(new_ref(new_tv(x), new_id()), POL, R));
        ComposeTestCase c = {
            "X?p ;; (r?;)ref(X,id)(;!) = occurs bot",
            with_proj(new_tv(x), POL, P),
            rf,
            new_guarded_bot(G_RF, 0, POL, P, POL, R, 1),
        };
        current_case = &c;
        RUN_TEST(test_executor_bridge);
    }

    // ============================================================
    // 型変数の合一 (union-find) が compose() の呼び出しをまたいで
    // 正しく維持されることの確認。
    //
    // X!p ;; Y?q = id を合成すると、内部的には X が SUBSTITUTED として
    // Y を指すようになる (X 自身が DTI で解決されるわけではない)。
    // その後、X を直接参照する別の coercion を合成しても、ty_find 経由で
    // 正しく Y へたどり着き、Y の方が実際に解決される。
    // ============================================================
    {
        ty *x = newty();
        ty *y = newty();
        ComposeTestCase step1 = {
            "(union-find setup) X!p ;; Y?q = id",
            with_tv_inj(new_tv(x), POL, P),
            with_proj(new_tv(y), POL, Q),
            new_id(),
        };
        current_case = &step1;
        RUN_TEST(test_executor_bridge);
        TEST_ASSERT_EQUAL_UINT8_MESSAGE(SUBSTITUTED, x->tykind, "X should now be substituted to Y");
        TEST_ASSERT_EQUAL_UINT8_MESSAGE(TYVAR, y->tykind, "Y should still be a fresh tyvar");

        // X を直接参照する新しい coercion (X?r) を int_p_proj と合成する。
        // ty_find(X) = Y に解決されるので、実際に int に確定するのは Y の方。
        ComposeTestCase step2 = {
            "X?r ;; int?p;id = int?r;id  [X は substituted 先の Y 経由で解決される]",
            with_proj(new_tv(x), POL, R),
            int_p_proj,
            with_proj(new_ground(G_INT, 0), POL, R),
        };
        current_case = &step2;
        RUN_TEST(test_executor_bridge);
        TEST_ASSERT_EQUAL_UINT8_MESSAGE(SUBSTITUTED, x->tykind, "X itself should remain substituted, not directly resolved");
        TEST_ASSERT_EQUAL_UINT8_MESSAGE(BASE_INT, y->tykind, "Y (the substitution target) should be the one resolved to int");
    }
}
