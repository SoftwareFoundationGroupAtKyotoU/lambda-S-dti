#include <stdlib.h>
#include <stdio.h>
#include <gc.h>
#include "unity.h"
#include "test_common.h"
#include "../libC/crc.h"

// --- 中身 (has_proj = has_inj = 0) の生成 ---

// 恒等 coercion は必ずライブラリ本体のシングルトン &crc_id を使う。
// compose() 内部では「本当に何の制約もない id」かどうかを g/size を見ずに
// ポインタ一致 (c == &crc_id) で判定している箇所がある (例: C_ID vs C_ID の
// 比較で c1->has_inj==1 のとき c1->crcdat.id.g と c2->crcdat.id.g を比較する
// が、これは c2 が crc_id そのものであるケースを compose() の入り口で
// 弾いた後の話を前提にしている)。そのため、テスト用に別途 GC_MALLOC した
// 「id 相当」の構造体を子要素として渡すと、g/size が未設定 (0) のまま
// 比較されて誤ったコンポーズ結果になることがある。
crc* new_id(void) {
    return &crc_id;
}
crc* new_ground(ground_ty g, uint16_t size) {
    crc* c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = C_ID;
    c->crcdat.id.g = g;
    c->crcdat.id.size = size;
    return c;
}
crc* new_fun(crc* c1, crc* c2) {
    crc* c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = C_FUN;
    c->has_tv = c1->has_tv | c2->has_tv;
    c->crcdat.fun_crc.c1 = c1;
    c->crcdat.fun_crc.c2 = c2;
    return c;
}
crc* new_list(crc* c) {
    crc* retc = (crc*)GC_MALLOC(sizeof(crc));
    retc->crckind = C_LIST;
    retc->has_tv = c->has_tv;
    retc->crcdat.lst_crc = c;
    return retc;
}
crc* new_ref(crc* c1, crc* c2) {
    crc* c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = C_REF;
    c->has_tv = c1->has_tv | c2->has_tv;
    c->crcdat.ref_crc.c1 = c1;
    c->crcdat.ref_crc.c2 = c2;
    return c;
}
crc* new_tuple(uint16_t size, crc** crcs) {
    crc* c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = C_TUPLE;
    uint8_t has_tv = 0;
    for (int i = 0; i < size; i++) has_tv |= crcs[i]->has_tv;
    c->has_tv = has_tv;
    c->crcdat.tpl_crc.size = size;
    c->crcdat.tpl_crc.crcs = crcs;
    return c;
}
crc* new_tv(ty* tv) {
    crc* c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = C_TV;
    c->has_tv = 1;
    c->crcdat.tv.tv_ptr = tv;
    return c;
}

// --- proj / inj のラップ ---

crc* with_proj(const crc* base, uint8_t p, uint32_t rid) {
    crc* c = (crc*)GC_MALLOC(sizeof(crc));
    *c = *base;
    c->has_proj = 1;
    c->p_proj = p;
    c->rid_proj = rid;
    return c;
}
crc* with_inj(const crc* base) {
    crc* c = (crc*)GC_MALLOC(sizeof(crc));
    *c = *base;
    c->has_inj = 1;
    return c;
}
crc* with_tv_inj(const crc* base, uint8_t p, uint32_t rid) {
    crc* c = (crc*)GC_MALLOC(sizeof(crc));
    *c = *base;
    c->has_inj = 1;
    c->crcdat.tv.p_inj = p;
    c->crcdat.tv.rid_inj = rid;
    return c;
}

// --- BOT ---

crc* new_bot(uint8_t p_bot, uint32_t rid_bot, uint8_t is_occur) {
    crc* c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = C_BOT;
    c->crcdat.bot.kind_bot = is_occur;
    c->crcdat.bot.p_bot = p_bot;
    c->crcdat.bot.rid_bot = rid_bot;
    return c;
}
crc* new_guarded_bot(ground_ty g, uint16_t size, uint8_t p_proj, uint32_t rid_proj,
                      uint8_t p_bot, uint32_t rid_bot, uint8_t is_occur) {
    crc* c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = C_BOT;
    c->has_proj = 1;
    c->p_proj = p_proj;
    c->rid_proj = rid_proj;
    c->crcdat.bot.g = g;
    c->crcdat.bot.size = size;
    c->crcdat.bot.kind_bot = is_occur;
    c->crcdat.bot.p_bot = p_bot;
    c->crcdat.bot.rid_bot = rid_bot;
    return c;
}

// --- デバッグ出力 ---

void dump_crc(const char* label, crc* c) {
    if (!c) { printf("%s = NULL\n", label); return; }
    printf("%s = {kind=%d has_proj=%d p_proj=%d rid_proj=%d has_inj=%d",
           label, c->crckind, c->has_proj, c->p_proj, c->rid_proj, c->has_inj);
    switch (c->crckind) {
        case C_ID:
            printf(" id.g=%d id.size=%d", c->crcdat.id.g, c->crcdat.id.size);
            break;
        case C_TV:
            printf(" tv.p_inj=%d tv.rid_inj=%d tv.tv_ptr=%p (tykind=%d)",
                   c->crcdat.tv.p_inj, c->crcdat.tv.rid_inj,
                   (void*)c->crcdat.tv.tv_ptr, c->crcdat.tv.tv_ptr->tykind);
            break;
        case C_BOT:
            printf(" bot.g=%d bot.size=%d bot.kind_bot=%d bot.p_bot=%d bot.rid_bot=%d",
                   c->crcdat.bot.g, c->crcdat.bot.size, c->crcdat.bot.kind_bot,
                   c->crcdat.bot.p_bot, c->crcdat.bot.rid_bot);
            break;
        default: break;
    }
    printf("}\n");
    switch (c->crckind) {
        case C_FUN:
            dump_crc("  .c1", c->crcdat.fun_crc.c1);
            dump_crc("  .c2", c->crcdat.fun_crc.c2);
            break;
        case C_LIST:
            dump_crc("  .child", c->crcdat.lst_crc);
            break;
        case C_REF:
            dump_crc("  .c1", c->crcdat.ref_crc.c1);
            dump_crc("  .c2", c->crcdat.ref_crc.c2);
            break;
        default: break;
    }
}

// --- 比較 ---

void assert_crc_recursive(crc* act, crc* exp, const char* path) {
    if (!exp) { TEST_ASSERT_NULL_MESSAGE(act, path); return; }
    TEST_ASSERT_NOT_NULL_MESSAGE(act, path);

    char msg[256];
    #define CHK_8(field) \
        snprintf(msg, sizeof(msg), "%s | Field: %s", path, #field); \
        TEST_ASSERT_EQUAL_UINT8_MESSAGE(exp->field, act->field, msg);
    #define CHK_ID(field) \
        snprintf(msg, sizeof(msg), "%s | Field: id.%s", path, #field); \
        TEST_ASSERT_EQUAL_UINT16_MESSAGE(exp->crcdat.id.field, act->crcdat.id.field, msg);
    #define CHK_BOT(field) \
        snprintf(msg, sizeof(msg), "%s | Field: bot.%s", path, #field); \
        TEST_ASSERT_EQUAL_UINT32_MESSAGE(exp->crcdat.bot.field, act->crcdat.bot.field, msg);
    #define CHK_TV(field) \
        snprintf(msg, sizeof(msg), "%s | Field: tv.%s", path, #field); \
        TEST_ASSERT_EQUAL_UINT32_MESSAGE(exp->crcdat.tv.field, act->crcdat.tv.field, msg);

    CHK_8(crckind);
    CHK_8(has_proj);
    CHK_8(p_proj);
    snprintf(msg, sizeof(msg), "%s | Field: rid_proj", path);
    TEST_ASSERT_EQUAL_UINT32_MESSAGE(exp->rid_proj, act->rid_proj, msg);
    CHK_8(has_inj);

    char next_path[512];
    switch (act->crckind) {
        case C_ID:
            CHK_ID(g);
            CHK_ID(size);
            return;
        case C_TV:
            // tv_ptr 自体の同一性/構造は (元々のテストの粒度に合わせて) 比較しない。
            // dti により実装内部で生成される型変数のポインタは予測できないため。
            CHK_TV(p_inj);
            CHK_TV(rid_inj);
            return;
        case C_BOT:
            // bot.g / bot.size は「外側に proj ガードが付いている (has_proj=1)」
            // ときだけ compose_s_bot() 内で実際に参照される値。has_proj=0 の
            // ときは元になった bottom から無条件にコピーされるだけの不定値に
            // なりうる (rewrite_proj は proj 情報だけ書き換えて crcdat は素通し
            // するため) ので、has_proj=1 のときだけ検証する。
            if (act->has_proj) {
                CHK_8(crcdat.bot.g);
                snprintf(msg, sizeof(msg), "%s | Field: bot.size", path);
                TEST_ASSERT_EQUAL_UINT16_MESSAGE(exp->crcdat.bot.size, act->crcdat.bot.size, msg);
            }
            CHK_8(crcdat.bot.kind_bot);
            CHK_8(crcdat.bot.p_bot);
            CHK_BOT(rid_bot);
            return;
        case C_FUN:
            snprintf(next_path, sizeof(next_path), "%s -> FUN.c1", path);
            assert_crc_recursive(act->crcdat.fun_crc.c1, exp->crcdat.fun_crc.c1, next_path);
            snprintf(next_path, sizeof(next_path), "%s -> FUN.c2", path);
            assert_crc_recursive(act->crcdat.fun_crc.c2, exp->crcdat.fun_crc.c2, next_path);
            return;
        case C_LIST:
            snprintf(next_path, sizeof(next_path), "%s -> LIST.child", path);
            assert_crc_recursive(act->crcdat.lst_crc, exp->crcdat.lst_crc, next_path);
            return;
        case C_TUPLE: {
            snprintf(msg, sizeof(msg), "%s | Field: tpl.size", path);
            TEST_ASSERT_EQUAL_UINT16_MESSAGE(exp->crcdat.tpl_crc.size, act->crcdat.tpl_crc.size, msg);
            for (int i = 0; i < act->crcdat.tpl_crc.size; i++) {
                snprintf(next_path, sizeof(next_path), "%s -> TUPLE[%d]", path, i);
                assert_crc_recursive(act->crcdat.tpl_crc.crcs[i], exp->crcdat.tpl_crc.crcs[i], next_path);
            }
            return;
        }
        case C_REF:
            snprintf(next_path, sizeof(next_path), "%s -> REF.c1", path);
            assert_crc_recursive(act->crcdat.ref_crc.c1, exp->crcdat.ref_crc.c1, next_path);
            snprintf(next_path, sizeof(next_path), "%s -> REF.c2", path);
            assert_crc_recursive(act->crcdat.ref_crc.c2, exp->crcdat.ref_crc.c2, next_path);
            return;
        case C_ARRAY:
            snprintf(next_path, sizeof(next_path), "%s -> ARRAY.c1", path);
            assert_crc_recursive(act->crcdat.array_crc.c1, exp->crcdat.array_crc.c1, next_path);
            snprintf(next_path, sizeof(next_path), "%s -> ARRAY.c2", path);
            assert_crc_recursive(act->crcdat.array_crc.c2, exp->crcdat.array_crc.c2, next_path);
            return;
    }
}
