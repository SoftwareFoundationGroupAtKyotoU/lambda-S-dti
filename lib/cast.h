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
	G_LI,
} ground_ty;

typedef struct ty ty;

typedef struct ty {
	enum tykind {
		DYN,
		BASE_INT,
		BASE_BOOL,
		BASE_UNIT,
		TYFUN,
		TYLIST,
		TYVAR,
		SUBSTITUTED,
	} tykind;
	union tydat {
		ty *tv;
		struct tyfun {
			ty *left;
			ty *right;
		} tyfun;
		ty *tylist;
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
		LIST,
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
		crc *one_crc;
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
		LABEL_alt,
		POLY_LABEL_alt,
		CLOSURE_alt,
		POLY_CLOSURE_alt,
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
		struct label_alt {
			value (*l)(value, value);
			value (*l_a)(value);
		} label_alt;
		struct poly_label_alt {
			value (*pl)(value, value, ty**);
			value (*pl_a)(value, ty**);
		} poly_label_alt;
		struct closure_alt {
			struct cls_alt {
				value (*c)(value, value, value*);
				value (*c_a)(value, value*);
			} cls_alt;
			value *fvs;
		} closure_alt;
		struct poly_closure_alt {
			struct pcls_alt {
				value (*pc)(value, value, value*, ty**);
				value (*pc_a)(value, value*, ty**);
			} pcls_alt;
			value *fvs;
		} poly_closure_alt;
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

typedef struct lst lst;

typedef struct lst {
	enum lstkind {
		UNWRAPPED_LIST,
		WRAPPED_LIST
	} lstkind;
	union lstdat {
		struct unwrap_l {
			value *h;
			value *t;
		} unwrap_l;
		struct wrap_l {
			lst *w;
			crc *c;
		} wrap_l;
	} lstdat;
} lst;

typedef struct dyn {
	value *v;
	crc *d;
} dyn;

typedef union value {
	int i_b_u;
	dyn *d;
	fun *f;
	lst *l;
	crc *s;
} value;

// value cast(value, ty*, ty*, ran_pol);

value coerce(value, crc*);

crc *compose(crc*, crc*);

value app(value, value, value);

value app_alt(value, value);

value hd(lst);

value tl(lst);

int did_not_match();

extern ty tydyn;
extern ty tyint;
extern ty tybool;
extern ty tyunit;
extern ty tyar;
extern ty tyli;
extern ty *(newty)();

extern crc crc_id;
extern crc crc_inj_INT;
extern crc crc_inj_BOOL;
extern crc crc_inj_UNIT;
extern crc inj_AR;
extern crc inj_LI;

crc *make_crc_inj_ar(crc*);
crc *make_crc_inj_li(crc*);
crc *make_crc_proj(ground_ty, ran_pol, crc*);
crc *make_crc_fun(crc*, crc*);
crc *make_crc_list(crc*);

#endif