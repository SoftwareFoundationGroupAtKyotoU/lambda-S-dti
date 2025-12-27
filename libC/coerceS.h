#ifndef COERCES_H
#define COERCES_H

#include "coerce.h"

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

value coerce(value, crc*);

value app(value, value, value);

value hd(lst);

value tl(lst);

int is_NULL(lst*);

#endif