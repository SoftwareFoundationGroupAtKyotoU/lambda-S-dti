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
	G_NONE, // this is dummy in the present implementation
	G_INT,
	G_BOOL,
	G_UNIT,
	G_AR,
	G_LI,
} ground_ty;

typedef struct ty ty;

#endif //not STATIC

typedef intptr_t value;

typedef struct fun fun;

typedef struct lst lst;

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
extern int find_ty_num;       // ty_findでポインタをたどった回数
#endif //PROFILE

#endif //TYPES_H