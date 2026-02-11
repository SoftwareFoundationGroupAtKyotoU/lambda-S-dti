#include "unity.h"
#include "test_common.h"

// 外部（test_cases.c）から使われるグローバル変数
ComposeTestCase* current_case = NULL;

// Unityから呼ばれる「1回分」のテスト実行関数
void test_executor_bridge() {
    // 1. 実行
    crc* actual = compose(current_case->input_a, current_case->input_b);

    // 2. 検証（再帰アサーション）
    assert_crc_recursive(actual, current_case->expected, current_case->label);
}

void setUp(void) {}
void tearDown(void) {}

int main(void) {
    UNITY_BEGIN();

    // テストスイート（test_cases.c）を呼び出す
    run_manual_test_suite();

    return UNITY_END();
}