#ifndef TYPES_H
#define TYPES_H

#include <stdint.h>

// CAST : λBのとき
// EAGER : lstのcoercionをeagerに
// ALT : λSのid特化バージョン
// CASTとALTが同時に定義されることはない

typedef struct range {
	char *filename;
	uint32_t startline;
	uint32_t startchr;
	uint32_t endline;
	uint32_t endchr;
	// int polarity;
} range;

typedef enum ground_ty : uint8_t {
	G_INT,
	G_BOOL,
	G_UNIT,
	G_AR,
	G_LI,
} ground_ty;

typedef struct ty ty;

typedef union value value;

typedef struct fun fun;

typedef struct lst lst;

typedef struct dyn dyn;

#ifndef CAST
typedef struct crc crc;
#endif

extern range *range_list;

#endif