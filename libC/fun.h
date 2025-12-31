#ifndef FUN_H
#define FUN_H

#include "types.h"

typedef struct fun {
	enum funkind {
		LABEL,
		POLY_LABEL,
		CLOSURE,
		POLY_CLOSURE,
		WRAPPED,
	} funkind;
	union fundat {
		#ifdef CAST
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
		#elif defined(ALT)
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
		#else 
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
		#endif
	} fundat;
	ty **tas;
} fun;

#endif