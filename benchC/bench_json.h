#ifndef JSONL_UPDATER_H
#define JSONL_UPDATER_H

// 外部ライブラリcJSONが必要なので、cJSONのヘッダーもインクルード
// ただし、cJSONをプロジェクトに組み込む方法によって不要な場合もある。
// 依存関係を明示するためにここでは含めるか、cJSONのセットアップに委ねる。
// #include "cJSON.h" 

// 外部プログラムからアクセスする必要がある定数やマクロがあればここに定義

// JSONLファイル更新関数の宣言
// 
// @param input_filename 元のJSONLファイル名
// @param output_filename 結果を書き出すファイル名
// @param times_data 全てのデータを含む一次元配列 (double* 型)
// @param num_entries データの行数 (JSONLの行数)
// @param num_times データの一行の要素数 (列数)
// @return 成功時に 0、失敗時に 1 を返す。
int update_jsonl_file(
    const char *input_filename, 
    const double *times_data, 
    int num_entries, 
    int num_times
);

// プロファイル計測結果を JSONL に反映する。
// metric_names[j] をキー、metrics_flat[i*num_metrics + j] を値として
// 各行 (mutant i) に上書き追加する。
//
// @param metric_names  num_metrics 個のキー名
// @param metrics_flat  num_entries * num_metrics の行優先フラット配列
// @param num_metrics   1 行あたりのメトリクス数
// @param num_entries   mutant 数 (JSONL 行数)
int update_jsonl_file_profile(
    const char *input_filename,
    char **metric_names,
    const long long *metrics_flat,
    int num_metrics,
    int num_entries
);

#endif // JSONL_UPDATER_H