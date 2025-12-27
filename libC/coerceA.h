#ifndef COERCEA_H
#define COERCEA_H

#include "coerce.h"

typedef union value value;

typedef struct fun fun;

typedef struct fun {
	enum funkind {
		LABEL_alt,
		POLY_LABEL_alt,
		CLOSURE_alt,
		POLY_CLOSURE_alt,
		WRAPPED,
	} funkind;
	union fundat {
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

// value app_alt(value, value);

value hd(lst);

value tl(lst);

int is_NULL(lst*);

extern value crc_id_value;

#endif