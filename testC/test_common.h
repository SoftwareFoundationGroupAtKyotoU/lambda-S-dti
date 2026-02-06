#ifndef TEST_COMMON_H
#define TEST_COMMON_H

#include "../libC/crc.h"

// テストケース1つ分の構造
typedef struct {
    const char* label;
    crc* input_a;
    crc* input_b;
    crc* expected;
} ComposeTestCase;

// ヘルパー関数（test_helpers.cで実装）
crc* new_id();
crc* new_fun(crc* c1, crc* c2);
crc* new_list(crc* child);
crc *new_bot(const uint8_t p, const uint32_t rid, const uint8_t is_occur);
crc* new_seq_proj(const crc *base_proj, crc *s_new);
crc* new_seq_inj(crc *s_new, const crc *base_inj);
crc* new_seq_proj_inj(const crc *base_proj, crc *s_new, const crc *base_inj);
crc *new_seq_proj_bot(const crc *base_proj, crc *bot);
crc* new_tv_proj(const crc *base_proj, ty *tv);
crc* new_tv_inj(ty *tv, const crc *base_inj);
crc* new_tv_proj_inj(const crc *base_proj, ty *tv, const crc *base_inj);
crc* new_tv_proj_occur(const crc* base_proj, const uint8_t bot_p, const uint32_t bot_rid);

void assert_crc_recursive(crc* act, crc* exp, const char* path);

// テストデータ実行用（test_cases.cで実装）
void run_manual_test_suite();

#endif