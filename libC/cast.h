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
		DYN, //0
		BASE_INT, //1
		BASE_BOOL, //2
		BASE_UNIT, //3
		TYFUN, //4
		TYLIST, //5
		TYVAR, //6
	} tykind;
	union tydat {
		struct tyfun {
			ty *left;
			ty *right;
		} tyfun;
		ty *tylist;
	} tydat;
} ty;

typedef union value value;

typedef struct fun fun;

typedef struct fun {
	enum funkind {
		LABEL,
		POLY_LABEL,
		CLOSURE,
		POLY_CLOSURE,
		WRAPPED,
	} funkind;
	union fundat {
		value (*label)(value);
		value (*poly_label)(value, ty**);
		struct closure {
			value (*cls)(value, value*);
			value *fvs;
		} closure;
		struct poly_closure {
			value (*pcls)(value, value*, ty**);
			value *fvs;
		} poly_closure;
		struct wrap {
			fun *w;
			ty *u1;
			ty *u2;
			ty *u3;
			ty *u4;
			ran_pol r_p;
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
			ty *u1;
			ty *u2;
			ran_pol r_p;
		} wrap_l;
	} lstdat;
} lst;

typedef struct dyn {
	value *v;
	ground_ty g;
	ran_pol r_p;
} dyn;

typedef union value {
	int i_b_u;
	dyn *d;
	fun *f;
	lst *l;
} value;

value cast(value, ty*, ty*, ran_pol);

value app(value, value);

value hd(lst);

value tl(lst);

int is_NULL(lst*);

int did_not_match();

extern ty tydyn;
extern ty tyint;
extern ty tybool;
extern ty tyunit;
extern ty tyar;
extern ty tyli;
extern ty *(newty)();

#endif