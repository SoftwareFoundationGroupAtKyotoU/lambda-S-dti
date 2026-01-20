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

typedef struct dyn dyn;
#endif

typedef union value value;

typedef struct fun fun;

typedef struct lst lst;

#if !defined(CAST) && !defined(STATIC)
typedef struct crc crc;
#endif

#ifndef STATIC
extern range *range_list;
#endif

#endif