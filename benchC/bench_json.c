#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <cjson/cJSON.h> 
// ... 必要なヘッダー (rename/removeのための<stdio.h>または<unistd.h>など)

#define MAX_LINE_LENGTH 1048576

// 配列からcJSON配列を作成するヘルパー関数
// times_dataは一次元配列として渡され、num_times個のデータを作成
cJSON *create_time_array_dynamic(
    const double *times_row, // 特定の行の先頭ポインタ
    int num_times
) {
    cJSON *array = cJSON_CreateArray();
    if (array == NULL) return NULL;

    for (int j = 0; j < num_times; j++) {
        // ポインタ times_row から j番目の要素にアクセス
        cJSON_AddItemToArray(array, cJSON_CreateNumber(times_row[j]));
    }
    return array;
}

// ------------------------------------------------------------------
// メイン更新関数（一時ファイル処理を内包）
// ------------------------------------------------------------------

int update_jsonl_file_dynamic_size(
    const char *input_filename, 
    const double *times_data, 
    const int *counts_data,
    int num_entries, 
    int num_times
) {
    FILE *fp_in = NULL;
    FILE *fp_out = NULL;
    char line[MAX_LINE_LENGTH];
    int status = 0;
    
    // 一時ファイル名の生成
    size_t temp_name_len = strlen(input_filename) + 5;
    char *temp_filename = (char *)malloc(temp_name_len);
    if (temp_filename == NULL) {
        perror("Memory allocation failed");
        return 1;
    }
    snprintf(temp_filename, temp_name_len, "%s.tmp", input_filename);
    
    // --- STEP 1: ファイルを開く ---
    
    fp_in = fopen(input_filename, "r");
    if (fp_in == NULL) {
        printf("Error opening input file: %s\n", input_filename);
        status = 1;
        goto cleanup_temp_name;
    }
	fseek(fp_in, 0, SEEK_END);
	long file_size = ftell(fp_in);
	fseek(fp_in, 0, SEEK_SET); // ポインタを先頭に戻す
	printf("DEBUG: Input file size: %ld bytes\n", file_size);
	if (file_size == 0) {
    	printf("DEBUG: File is empty or non-existent.\n");
	}

    fp_out = fopen(temp_filename, "w"); // 一時ファイルを書き込みモードで開く
    if (fp_out == NULL) {
        perror("Error opening temporary file");
        fclose(fp_in);
        status = 1;
        goto cleanup_temp_name;
    }

    // --- STEP 2: 1行ずつ処理し、一時ファイルに書き出す ---
    
	printf("DEBUG: Starting file read loop.\n");
    while (fgets(line, sizeof(line), fp_in)) {
        // ... (JSONパース、インデックス取得、配列ポインタ計算、cJSONの更新、文字列化のロジック) ...
        // 前回の回答で定義されたメインループの処理をここに挿入します
        
        cJSON *root = NULL;
        char *json_string_out = NULL;
        
        line[strcspn(line, "\n")] = 0;
        root = cJSON_Parse(line);

		if (root == NULL) {
        	// パースエラーが発生した場合、エラーメッセージを出力する
        	const char *error_ptr = cJSON_GetErrorPtr();
        	if (error_ptr != NULL) {
        	    fprintf(stderr, "Parsing ERROR (near: %s):\n", error_ptr);
        	    fprintf(stderr, "JSON line that failed: %s\n", line);
        	} else {
        	    fprintf(stderr, "Parsing FAILED for unknown reason.\n");
        	}
		
        	// 以下の cJSON_Delete(root) や書き込みロジックはスキップされるので問題なし
    	} else {
            cJSON *index_item = cJSON_GetObjectItemCaseSensitive(root, "mutant_index");
            int array_index = cJSON_IsNumber(index_item) ? index_item->valueint - 1 : -1;
            
            if (array_index >= 0 && array_index < num_entries) {
                const double *times_row_ptr = times_data + (array_index * num_times);
                cJSON *new_times_array = create_time_array_dynamic(times_row_ptr, num_times);
                if (new_times_array) {
                    cJSON_ReplaceItemInObject(root, "times_sec", new_times_array);
                }
                cJSON *new_mem_item = cJSON_CreateNumber(counts_data[array_index]);
                if (new_mem_item) {
                    cJSON_ReplaceItemInObject(root, "mem", new_mem_item);
                }
            }
            
            json_string_out = cJSON_PrintUnformatted(root); 
            if (json_string_out) {
                fprintf(fp_out, "%s\n", json_string_out); 
                free(json_string_out);
            }
            cJSON_Delete(root);
        }
    }
	printf("DEBUG: Finished file read loop.\n");
    
    // 処理中にエラーが発生しなかった場合、ファイルを閉じる
    fclose(fp_in);
    fclose(fp_out);

    // --- STEP 3: リネーム処理 ---
    
    // 元のファイルを削除
    if (remove(input_filename) != 0) {
        perror("Failed to remove original file. Check permissions.");
        status = 2; // リネーム処理失敗
        goto cleanup_temp_name;
    }

    // 一時ファイルをリネーム
    if (rename(temp_filename, input_filename) != 0) {
        perror("Failed to rename temporary file.");
        status = 3; // リネーム処理失敗
        goto cleanup_temp_name;
    }
    
    printf("File successfully updated: %s\n", input_filename);
    status = 0; // 成功

cleanup_temp_name:
    free(temp_filename);
    return status;
}