#ifndef TEST_COMMON_H
#define TEST_COMMON_H

#include "../libC/crc.h"
#include "../libC/ty.h"

// テストケース1つ分の構造
typedef struct {
    const char* label;
    crc* input_a;
    crc* input_b;
    crc* expected;
} ComposeTestCase;

// --- 生成ヘルパー（test_helpers.cで実装） ---
// 現行の crc 表現は「proj / inj をノードでラップする」のではなく、
// 各ノードが has_proj / has_inj フラグを直接持つフラット構造になっている。
// そのため、まず「中身」(proj も inj も付いていない coercion) を作り、
// 続けて with_proj / with_inj でラップする、という2段階でテストデータを組み立てる。

crc* new_id(void);                              // 恒等 coercion (has_proj=has_inj=0)
crc* new_ground(ground_ty g, uint16_t size);     // id{g,size} の中身 (has_proj=has_inj=0)
crc* new_fun(crc* c1, crc* c2);                  // s1->s2 の中身
crc* new_list(crc* c);                           // [s] の中身
crc* new_ref(crc* c1, crc* c2);                  // ref(s1,s2) の中身
crc* new_tuple(uint16_t size, crc** crcs);       // s1*s2*...*sn の中身
crc* new_tv(ty* tv);                             // X の中身 (has_proj=has_inj=0)

crc* with_proj(const crc* base, uint8_t p, uint32_t rid);  // (G?p;)base
crc* with_inj(const crc* base);                            // base(;G!)
crc* with_tv_inj(const crc* base, uint8_t p, uint32_t rid); // base(;G!) だが TV 用 (tv.p_inj/rid_inj を設定)

// 素の ⊥ (外側に proj ガードを持たない): has_proj=0
crc* new_bot(uint8_t p_bot, uint32_t rid_bot, uint8_t is_occur);
// ガード付きの (G?p;)⊥q : 外側の proj (p, rid_proj, g/size) と、実際に blame される
// 内側のラベル (p_bot, rid_bot) をまとめて設定する
crc* new_guarded_bot(ground_ty g, uint16_t size, uint8_t p_proj, uint32_t rid_proj,
                      uint8_t p_bot, uint32_t rid_bot, uint8_t is_occur);

void assert_crc_recursive(crc* act, crc* exp, const char* path);
void dump_crc(const char* label, crc* c);

// テストデータ実行用（test_cases.cで実装）
void run_manual_test_suite();

#endif
