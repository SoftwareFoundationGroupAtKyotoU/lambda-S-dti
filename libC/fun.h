#ifndef FUN_H
#define FUN_H

#include "types.h"

typedef struct fun {
	enum funkind : uint8_t {
		LABEL,
		POLY_LABEL,
		CLOSURE,
		POLY_CLOSURE,
		WRAPPED,
	} funkind;
	#ifdef CAST
	uint8_t polarity;
	uint32_t rid;
	#endif
	union fundat {
		#ifdef CAST
		value (*label)(value);
		struct closure {
			value (*cls)(value, value*);
			value *fvs;
		} closure;
		struct poly {
			ty **tas;
			union f {
				value (*poly_label)(value, ty**);
				struct poly_closure {
					value (*pcls)(value, value*, ty**);
					value *fvs;
				} poly_closure;
			} f;
		} poly;
		struct wrap {
			fun *w;
			ty *u1;
			ty *u2;
		} wrap;
		#elif defined(ALT)
		struct label_alt {
			value (*l)(value, value);
			value (*l_a)(value);
		} label_alt;
		struct closure_alt {
			struct cls_alt {
				value (*c)(value, value, value*);
				value (*c_a)(value, value*);
			} cls_alt;
			value *fvs;
		} closure_alt;
		struct poly {
			ty **tas;
			union f {
				struct poly_label_alt {
					value (*pl)(value, value, ty**);
					value (*pl_a)(value, ty**);
				} poly_label_alt;
				struct poly_closure_alt {
					struct pcls_alt {
						value (*pc)(value, value, value*, ty**);
						value (*pc_a)(value, value*, ty**);
					} pcls_alt;
					value *fvs;
				} poly_closure_alt;
			} f;
		} poly;
		struct wrap {
			fun *w;
			crc *c;
		} wrap;
		#else 
		value (*label)(value, value);
		struct closure {
			value (*cls)(value, value, value*);
			value *fvs;
		} closure;
		struct poly {
			ty **tas;
			union f {
				value (*poly_label)(value, value, ty**);
				struct poly_closure {
					value (*pcls)(value, value, value*, ty**);
					value *fvs;
				} poly_closure;
			} f;
		} poly;
		struct wrap {
			fun *w;
			crc *c;
		} wrap;
		#endif
	} fundat;
} fun;

#endif