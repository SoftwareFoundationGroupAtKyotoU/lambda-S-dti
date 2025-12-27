#include <stdio.h>
#include <stdlib.h> //for abort
#include "coerce.h"
#include "coerceA.h"
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
		case(LABEL_alt):												// if f is "label" function
		if (s.s->crckind == ID) {
			value (*l_a)(value);
			l_a = g->fundat.label_alt.l_a;
			retx = l_a(arg);
		} else {
			value (*l)(value, value);
			l = g->fundat.label_alt.l;							// R_BETA : return f(v)
			retx = l(arg, s);
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
		}
		break;

		case(POLY_LABEL_alt):
		if (s.s->crckind == ID) {
			value (*pl_a)(value, ty**);
			pl_a = g->fundat.poly_label_alt.pl_a;
			retx = pl_a(arg, g->tas);
		} else {
			value (*pl)(value, value, ty**);
			pl = g->fundat.poly_label_alt.pl;
			retx = pl(arg, s, g->tas);
		}
		break;

		case(CLOSURE_alt):												// if f is closure
		if (s.s->crckind == ID) {
			value (*c_a)(value, value*);
			c_a = g->fundat.closure_alt.cls_alt.c_a;
			retx = c_a(arg, g->fundat.closure_alt.fvs);
		} else {
			value (*c)(value, value, value*);
			c = g->fundat.closure_alt.cls_alt.c;				// R_BETA : return f(v, fvs)
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			retx = c(arg, s, g->fundat.closure_alt.fvs);
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
		}
		break;

		case(POLY_CLOSURE_alt):												// if f is closure
		if (s.s->crckind == ID) {
			value (*pc_a)(value, value*, ty**);
			pc_a = g->fundat.poly_closure_alt.pcls_alt.pc_a;
			retx = pc_a(arg, g->fundat.closure_alt.fvs, g->tas);
		} else {
			value (*pc)(value, value, value*, ty**);
			pc = g->fundat.poly_closure_alt.pcls_alt.pc;				// R_BETA : return f(v, fvs)
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			retx = pc(arg, s, g->fundat.poly_closure_alt.fvs, g->tas);
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
		}
		break;
	}
	return retx;
}

// value app_alt(value f, value v) {									// reduction of f(v)
// 	// value s = { .s = &crc_id };
// 	// return app(f, v, s);
// 	value retx;

// 	fun *g;

// 	value arg;
// 	value s;

// 	value (*l_a)(value);
// 	value (*c_a)(value, value*);
// 	value (*pl_a)(value, ty**);
// 	value (*pc_a)(value, value*, ty**);
// // 	ran_pol neg_r_p;

// 	if (f.f->funkind == WRAPPED) {
// 		s.s = f.f->fundat.wrap.c_res;
// 		arg = coerce(v, f.f->fundat.wrap.c_arg);
// 		g = f.f->fundat.wrap.w;
// 		// if (s.s->crckind != ID) {
// 		value f_ = { .f = g };
// 		return app(f_, arg, s);
// 		// }
// 	} else {
// 		arg = v;
// 		g = f.f;
// 	}


// 	switch(g->funkind) {
// 		case(LABEL_alt):												// if f is "label" function
// 		l_a = g->fundat.label_alt.l_a;							// R_BETA : return f(v)
// 		retx = l_a(arg);
// 		//printf("Heap size = %d\n", (int)GC_get_heap_size());
// 		break;

// 		case(POLY_LABEL_alt):
// 		pl_a = g->fundat.poly_label_alt.pl_a;
// 		retx = pl_a(arg, g->tas);
// 		break;

// 		case(CLOSURE_alt):												// if f is closure
// 		c_a = g->fundat.closure_alt.cls_alt.c_a;				// R_BETA : return f(v, fvs)
// 		//printf("Heap size = %d\n", (int)GC_get_heap_size());
// 		retx = c_a(arg, g->fundat.closure_alt.fvs);
// 		//printf("Heap size = %d\n", (int)GC_get_heap_size());
// 		break;

// 		case(POLY_CLOSURE_alt):												// if f is closure
// 		pc_a = g->fundat.poly_closure_alt.pcls_alt.pc_a;				// R_BETA : return f(v, fvs)
// 		//printf("Heap size = %d\n", (int)GC_get_heap_size());
// 		retx = pc_a(arg, g->fundat.poly_closure_alt.fvs, g->tas);
// 		//printf("Heap size = %d\n", (int)GC_get_heap_size());
// 		break;
// 	}
// 	return retx;
// }

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

value crc_id_value = { .s = &crc_id };
