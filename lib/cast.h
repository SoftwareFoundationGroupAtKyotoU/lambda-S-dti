#ifndef CAST_H
#define CAST_H

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
} ground_ty;

typedef struct ty ty;

typedef struct ty {
	enum tykind {
		DYN,
		BASE_INT,
		BASE_BOOL,
		BASE_UNIT,
		TYFUN,
		TYVAR,
		SUBSTITUTED,
	} tykind;
	union tydat {
		ty *tv;
		struct tyfun {
			ty *left;
			ty *right;
		} tyfun;
	} tydat;
	
} ty;

typedef struct crc crc;

typedef struct crc {
	enum crckind {
		INJ,
		PROJ,
		INJ_TV,
		PROJ_TV,
		PROJ_INJ_TV,
		FUN,
		ID,
		SEQ,
		BOT
	} crckind;
	union crcdat {
		ground_ty g;
		ty *tv;
		struct two_crc {
			crc *c1;
			crc *c2;
		} two_crc;
	} crcdat;
	ran_pol r_p;
} crc;

typedef union value value;

typedef struct fun fun;

typedef struct fun {
	enum funkind {
		LABEL,
		POLY_LABEL,
		CLOSURE,
		POLY_CLOSURE,
		WRAPPED,
		// LABEL_WRAP,
		// POLY_LABEL_WRAP,
		// CLOSURE_WRAP,
		// POLY_CLOSURE_WRAP,
	} funkind;
	union fundat {
		value (*label)(value, value);
		value (*poly_label)(value, value, ty**);
		struct closure {
			value (*cls)(value, value, value*);
			value *fvs;
		} closure;
		struct poly_closure {
			value (*pcls)(value, value, value*, ty**);
			value *fvs;
		} poly_closure;
		struct wrap {
			fun *w;
			crc *c_arg;
			crc *c_res;
		// 	ty *u1;
		// 	ty *u2;
		// 	ty *u3;
		// 	ty *u4;
		// 	ran_pol r_p;
		} wrap;
	} fundat;
	ty **tas;
} fun;

typedef struct dyn {
	value *v;
	crc *d;
} dyn;

// typedef union uncoerced_value {
// 	int i_b_u;
// 	// dyn *d;
// 	fun *f;
// 	crc *s;
// } uncoerced_value;

typedef union value {
	// enum valkind {
	// 	UNCOERCED,
	// 	COERCED,
	// } valkind;
	// uncoerced_value u;
	// crc *d;
	int i_b_u;
	dyn *d;
	fun *f;
	crc *s;
} value;

// value cast(value, ty*, ty*, ran_pol);

value coerce(value, crc*);

crc *compose(crc*, crc*);

value app(value, value, value);

extern ty tydyn;
extern ty tyint;
extern ty tybool;
extern ty tyunit;
extern ty tyar;
extern ty *(newty)();

extern crc crc_id;
extern crc crc_inj_INT;
extern crc crc_inj_BOOL;
extern crc crc_inj_UNIT;
extern crc inj_AR;

crc *make_crc_inj_ar(crc*);
crc *make_crc_proj(ground_ty, ran_pol, crc*);
crc *make_crc_fun(crc*, crc*);

extern value (fun_print_int)(value, value);
extern value (fun_print_bool)(value, value);
extern value (fun_print_newline)(value, value);

extern value print_int;
extern value print_bool;
extern value print_newline;
extern int (stdlib)();

#endif