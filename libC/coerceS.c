#include <stdio.h>
#include <stdlib.h> //for abort
#include "coerce.h"
#include "coerceS.h"
#include "gc.h"

value coerce(value v, crc *s) {
	// printf("coerce c:%d\n", s->crckind);
	value retv;

	if (s->crckind == ID) { // v<id> -> v
		retv = v;
	} else if (s->crckind == BOT) { // v<bot^p> -> blame p
		blame(s->r_p);
		exit(1);
	} else if (s->crckind == FUN) { // v<s'=>t'>
		if (v.f->funkind == WRAPPED) { // u<<s=>t>><s'=>t'>
			crc *c1 = compose(s->crcdat.two_crc.c1, v.f->fundat.wrap.c_arg);
			crc *c2 = compose(v.f->fundat.wrap.c_res, s->crcdat.two_crc.c2);
			if (c1->crckind == ID && c2->crckind == ID) {    // u<<s=>t>><s'=>t'> -> u<id> -> u
				retv.f = v.f->fundat.wrap.w;
			} else {										 // u<<s=>t>><s'=>t'> -> u<s';;s=>t;;t'> -> u<<s';;s=>t;;t'>>
				retv.f = (fun*)GC_MALLOC(sizeof(fun));
				retv.f->funkind = WRAPPED;
				retv.f->fundat.wrap.w = v.f->fundat.wrap.w;
				retv.f->fundat.wrap.c_arg = c1;
				retv.f->fundat.wrap.c_res = c2;
			}
		} else {                   // u<s'=>t'> -> u<<s'=>t'>>
			retv.f = (fun*)GC_MALLOC(sizeof(fun));
			retv.f->funkind = WRAPPED;
			retv.f->fundat.wrap.w = v.f;
			retv.f->fundat.wrap.c_arg = s->crcdat.two_crc.c1;
			retv.f->fundat.wrap.c_res = s->crcdat.two_crc.c2;
		}
	} else if (s->crckind == SEQ && s->crcdat.two_crc.c1->crckind == FUN) { // v<s'=>t';G!>
		retv.d = (dyn*)GC_MALLOC(sizeof(dyn));
		retv.d->v = (value*)GC_MALLOC(sizeof(value));
		if (v.f->funkind == WRAPPED) {                                      // u<<s=>t>><s'=>t';G!>
			crc *c1 = compose(s->crcdat.two_crc.c1->crcdat.two_crc.c1, v.f->fundat.wrap.c_arg);
			crc *c2 = compose(v.f->fundat.wrap.c_res, s->crcdat.two_crc.c1->crcdat.two_crc.c2);
			retv.d->v->f = v.f->fundat.wrap.w;
			retv.d->d = (crc*)GC_MALLOC(sizeof(crc));
			retv.d->d->crckind = SEQ;
			retv.d->d->crcdat.two_crc.c2 = s->crcdat.two_crc.c2;
			if (c1->crckind == ID && c2->crckind == ID) { // u<<s=>t>><s'=>t';G!> -> u<id;G!> -> u<<id;G!>>
				retv.d->d->crcdat.two_crc.c1 = c1;
			} else { 									// u<<s=>t>><s'=>t';G!> -> u<s';;s=>t;;t';G!> -> u<<s';;s=>t;;t';G!>>
				retv.d->d->crcdat.two_crc.c1 = (crc*)GC_MALLOC(sizeof(crc));
				retv.d->d->crcdat.two_crc.c1->crckind = FUN;
				retv.d->d->crcdat.two_crc.c1->crcdat.two_crc.c1 = c1;
				retv.d->d->crcdat.two_crc.c1->crcdat.two_crc.c2 = c2;
			}
		} else { // u<s'=>t';G!> -> u<<s'=>t';G!>>
			retv.d->v->f = v.f;
			retv.d->d = s;
		}
	} else if (s->crckind == LIST) { // v<[s']>
		if (v.l != NULL && v.l->lstkind == WRAPPED_LIST) { // u<<[s]>><[s']>
			crc *c = compose(v.l->lstdat.wrap_l.c, s->crcdat.one_crc);
			if (c->crckind == ID) {    						// u<<[s]>><[s']> -> u<id> -> u
				retv.l = v.l->lstdat.wrap_l.w;
			} else {										// u<<[s]>><[s']> -> u<[s;;s']> -> u<<[s;;s']>>
				retv.l = (lst*)GC_MALLOC(sizeof(lst));
				retv.l->lstkind = WRAPPED_LIST;
				retv.l->lstdat.wrap_l.w = v.l->lstdat.wrap_l.w;
				retv.l->lstdat.wrap_l.c = c;
			}
		// } else if (v.l == NULL) {
		// 	printf("Null should not be a wrapped list: coercion is [%d]", s->crcdat.one_crc->crckind);
		// 	exit(1);
		} else {                   // u<[s']> -> u<<[s']>>
			retv.l = (lst*)GC_MALLOC(sizeof(lst));
			retv.l->lstkind = WRAPPED_LIST;
			retv.l->lstdat.wrap_l.w = v.l;
			retv.l->lstdat.wrap_l.c = s->crcdat.one_crc;
		}
	} else if (s->crckind == SEQ && s->crcdat.two_crc.c1->crckind == LIST) { // v<[s'];G!>
		retv.d = (dyn*)GC_MALLOC(sizeof(dyn));
		retv.d->v = (value*)GC_MALLOC(sizeof(value));
		if (v.l != NULL && v.l->lstkind == WRAPPED_LIST) {                                      // u<<[s]>><[s'];G!>
			crc *c = compose(v.l->lstdat.wrap_l.c, s->crcdat.two_crc.c1->crcdat.one_crc);
			retv.d->v->l = v.l->lstdat.wrap_l.w;
			retv.d->d = (crc*)GC_MALLOC(sizeof(crc));
			retv.d->d->crckind = SEQ;
			retv.d->d->crcdat.two_crc.c2 = s->crcdat.two_crc.c2;
			if (c->crckind == ID) { // u<<[s]>><[s'];G!> -> u<id;G!> -> u<<id;G!>>
				retv.d->d->crcdat.two_crc.c1 = c;
			} else { 									// u<<[s]>><[s'];G!> -> u<[s;;s'];G!> -> u<<[s;;s'];G!>>
				retv.d->d->crcdat.two_crc.c1 = (crc*)GC_MALLOC(sizeof(crc));
				retv.d->d->crcdat.two_crc.c1->crckind = LIST;
				retv.d->d->crcdat.two_crc.c1->crcdat.one_crc = c;
			}
		} else { // u<[s'];G!> -> u<<[s'];G!>>
			retv.d->v->l = v.l;
			retv.d->d = s;
		}
	} else if (s->crckind == SEQ && s->crcdat.two_crc.c2->crckind == INJ) { // v<id;G!> -> v<<id;G!>>
		retv.d = (dyn*)GC_MALLOC(sizeof(dyn)); 
		retv.d->v = (value*)GC_MALLOC(sizeof(value));
		*retv.d->v = v;
		retv.d->d = s;
	 } else if (s->crckind == INJ_TV) {
		retv = coerce(v, normalize_crc(s));
	 	// retv.d = (dyn*)GC_MALLOC(sizeof(dyn));
	 	// retv.d->v = (value*)GC_MALLOC(sizeof(value));
	 	// *retv.d->v = v;
	 	// retv.d->d = s;
	} else {									// v<G?p;i> = u<<d>><G?p;i>, v<X?p> = u<<d>><X?p>, v<?pX!> = u<<d>><?pX!>
		crc *c1 = compose(v.d->d, s);
		// printf("composed c:%d\n", c1->crckind);
		if (c1->crckind == ID) {                // u<<d>><s> -> u<id> -> u
			retv = *v.d->v;
		} else if (c1->crckind == FUN) {        // u<<d>><s> -> u<s=>t> -> u<<s=>t>>
			retv.f = (fun*)GC_MALLOC(sizeof(fun));
			retv.f->funkind = WRAPPED;
			retv.f->fundat.wrap.w = v.d->v->f;
			retv.f->fundat.wrap.c_arg = c1->crcdat.two_crc.c1;
			retv.f->fundat.wrap.c_res = c1->crcdat.two_crc.c2;
		} else if (c1->crckind == LIST) {        // u<<d>><s> -> u<[s]> -> u<<[s]>>
			retv.l = (lst*)GC_MALLOC(sizeof(lst));
			retv.l->lstkind = WRAPPED_LIST;
			retv.l->lstdat.wrap_l.w = v.d->v->l;
			retv.l->lstdat.wrap_l.c = c1->crcdat.one_crc;
		} else if (c1->crckind == BOT) {
			blame(c1->r_p);
			exit(1);
		} else {                                // u<<d>><s> -> u<d> -> u<<d>>
			retv.d = (dyn*)GC_MALLOC(sizeof(dyn));
			retv.d->v = v.d->v;
			retv.d->d = c1;
		}
	}
	return retv;
}			

value app(value f, value v, value w) {									// reduction of f(v)
	value retx;

	fun *g;

	value arg;
	value s;

	value (*l)(value, value);
	value (*c)(value, value, value*);
	value (*pl)(value, value, ty**);
	value (*pc)(value, value, value*, ty**);
// 	ran_pol neg_r_p;

    if (f.f->funkind == WRAPPED) {
		s.s = compose(f.f->fundat.wrap.c_res, w.s);
		arg = coerce(v, f.f->fundat.wrap.c_arg);
		g = f.f->fundat.wrap.w;
	} else {
		s.s = w.s;
		arg = v;
		g = f.f;
	}

	switch(g->funkind) {
		case(LABEL):												// if f is "label" function
		l = g->fundat.label;							// R_BETA : return f(v)
		retx = l(arg, s);
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		break;

		case(POLY_LABEL):
		pl = g->fundat.poly_label;
		retx = pl(arg, s, g->tas);
		break;

		case(CLOSURE):												// if f is closure
		c = g->fundat.closure.cls;				// R_BETA : return f(v, fvs)
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		retx = c(arg, s, g->fundat.closure.fvs);
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		break;

		case(POLY_CLOSURE):												// if f is closure
		pc = g->fundat.poly_closure.pcls;				// R_BETA : return f(v, fvs)
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		retx = pc(arg, s, g->fundat.poly_closure.fvs, g->tas);
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		break;
	}
	return retx;
}

int is_NULL(lst *l) {
	if (l==NULL) { 
		return 1;
	} else if (l->lstkind == WRAPPED_LIST) {
		return is_NULL(l->lstdat.wrap_l.w);
	} else {
		return 0;
	}
}

value hd(lst l) {
	if (l.lstkind == WRAPPED_LIST) {
		return coerce(*l.lstdat.wrap_l.w->lstdat.unwrap_l.h, l.lstdat.wrap_l.c);
	} else {
		return *l.lstdat.unwrap_l.h;
	}
}

value tl(lst l) {
	if (l.lstkind == WRAPPED_LIST) {
		return coerce(*l.lstdat.wrap_l.w->lstdat.unwrap_l.t, make_crc_list(l.lstdat.wrap_l.c));
	} else {
		return *l.lstdat.unwrap_l.t;
	}
}
