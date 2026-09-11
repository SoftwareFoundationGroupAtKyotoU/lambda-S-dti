#ifndef TYPES_H
#define TYPES_H

#include <stdint.h>

// CAST : λBのとき
// EAGER : lstのcoercionをeagerに
// ALT : λSのid特化バージョン
// STATIC: fully static 決め打ちバージョン

// CASTとALTが同時に定義されることはない

#ifndef STATIC
typedef struct range {
	char *filename;
	uint32_t startline;
	uint32_t startchr;
	uint32_t endline;
	uint32_t endchr;
} range;

typedef enum ground_ty : uint8_t {
	G_FN,
	G_LI,
	G_TP,
	G_RF,
	G_AR,
	G_INT,
	G_BOOL,
	G_FLOAT,
	// up to here is used for tag in dynamic value
	G_UNIT,
} ground_ty;

// NOTE: rewrite if you change the definition of tykind
#define N_GROUND_TY (G_UNIT + 1)

typedef struct ty ty;

#endif //not STATIC

typedef intptr_t value;

typedef struct fun fun;

typedef struct lst lst;

#if defined(EAGER) || defined(STATIC)
typedef struct tpl_raw tpl;
#else
typedef struct tpl_header tpl;
#endif

#ifdef STATIC
typedef value *ref;
#else
typedef struct ref ref;
#endif

#if defined(MONOTONIC) || defined(STATIC)
typedef struct arr_raw arr;
#else
typedef struct arr_header arr;
#endif

#if !defined(CAST) && !defined(STATIC)
typedef struct crc crc;
#endif //not CAST && not STATIC

#ifndef STATIC
extern range *range_list;
#endif //STATIC

#ifdef PROFILE
extern int current_inference; // dti関数の呼び出し回数
extern int current_cast;      // cast/coerce関数およびハードコードされたcastの総回数
extern int current_longest;   // longest proxy chain
extern int current_compose;   // compose関数の呼び出し回数
extern int compose_cached;    // compose memo cacheにヒットした回数
extern int current_alloc;     // alloc関数の呼び出し回数。実行時にどれだけのcoercionを生成しようとしたか
extern int new_crc_num;       // 新しいコアーションを実際に生成した回数
extern int alloc_hash;        // coercion hash tableにヒットした回数
extern int find_ty_num;       // ty_findでポインタをたどった総歩数

extern int ty_find_calls;      // ty_find の呼び出し回数
extern int ty_find_max_chain;  // ty_find 1 回での最長ポインタ鎖
extern int normalize_tv_num;   // normalize_tv の呼び出し回数
extern int compose_max_depth;  // compose の再帰深さの最大
// extern long long tyapp_num;    // 型適用でクロージャを複製した回数
// extern long long fun_alloc_num;   // クロージャ（fun）を GC_MALLOC した回数
extern int blame_check_num;    // toplevel_coerce_proj / _proj_tp の動的タグ検査回数
extern int coerce_kind[8];     // coerce() に渡った crc_kind の内訳
extern int dti_by_ground[9];   // dti() が解決した ground_type の内訳
#endif //PROFILE

#endif //TYPES_H