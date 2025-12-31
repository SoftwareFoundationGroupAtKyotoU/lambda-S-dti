#ifndef TYPES_H
#define TYPES_H

// CAST : λBのとき
// EAGER : lstのcoercionをeagerに
// ALT : λSのid特化バージョン
// CASTとALTが同時に定義されることはない

typedef struct ran_pol {
	char *filename;
	int startline;
	int startchr;
	int endline;
	int endchr;
	int polarity;
} ran_pol;

typedef enum ground_ty {
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

#endif