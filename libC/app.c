#include <stdio.h>
#include <stdlib.h> //for abort
#include "gc.h"

#include "crc.h"
#include "fun.h"
#include "dyn.h"
#include "lst.h"
#include "capp.h"
#include "value.h"
#include "app.h"
#include "ty.h"

#if defined(CAST) || defined(STATIC)
value appM(value f, value v) {									// reduction of f(v)
	switch(f.f->funkind) {
		case(LABEL): return f.f->fundat.label(v);	// if f is "label" function R_BETA : return f(v)
		case(CLOSURE): return f.f->fundat.closure.cls(v, f.f->fundat.closure.fvs); // if f is closure R_BETA : return f(v, fvs)
		#ifndef STATIC
		case(POLY_LABEL): return f.f->fundat.poly.f.poly_label(v, f.f->fundat.poly.tas);
		case(POLY_CLOSURE):	return f.f->fundat.poly.f.poly_closure.pcls(v, f.f->fundat.poly.f.poly_closure.fvs, f.f->fundat.poly.tas); // if f is closure R_BETA : return f(v, fvs)
		case(WRAPPED): {												// if f is wrapped function (f = w:U1->U2=>U3->U4)
			uint8_t pos_pol = f.f->polarity;
			uint8_t neg_pol = pos_pol ^ 1;
			uint32_t rid = f.f->rid;
			struct wrap w = f.f->fundat.wrap;
			value f1 = { .f = w.w };									// R_APPCAST : return (w(v:U3=>U1)):U2=>U4
			ty *u1 = w.u1;
			ty *u2 = w.u2;
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			value v_ = cast(v, u2->tydat.tyfun.left , u1->tydat.tyfun.left, rid, neg_pol);
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			value v__ = appM(f1, v_);
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			return cast(v__, u1->tydat.tyfun.right, u2->tydat.tyfun.right, rid, pos_pol);
		}
		#endif
	}
}
#endif

#ifdef ALT
value appM(value f, value v) {									// reduction of f(v)
	// value s = { .s = &crc_id };
	// return app(f, v, s);

	value s;
	value arg;
	fun *g;

	if (f.f->funkind == WRAPPED) {
		s.s = f.f->fundat.wrap.c->crcdat.two_crc.c2;
		arg = coerce(v, f.f->fundat.wrap.c->crcdat.two_crc.c1);
		g = f.f->fundat.wrap.w;
	} else {
		arg = v;
		g = f.f;
		goto CRC_ID;
	}

	if (s.s->crckind != ID) {
		switch(g->funkind) {
			case(LABEL): return g->fundat.label_alt.l(arg, s);	// if f is "label" function R_BETA : return f(v)
			case(POLY_LABEL): return g->fundat.poly.f.poly_label_alt.pl(arg, s, g->fundat.poly.tas);
			case(CLOSURE): return g->fundat.closure_alt.cls_alt.c(arg, s, g->fundat.closure_alt.fvs);	// if f is closure R_BETA : return f(v, fvs)		
			case(POLY_CLOSURE):	return g->fundat.poly.f.poly_closure_alt.pcls_alt.pc(arg, s, g->fundat.poly.f.poly_closure_alt.fvs, g->fundat.poly.tas);	// if f is closure R_BETA : return f(v, fvs)
		}
	}

	CRC_ID:
	switch(g->funkind) {
		case(LABEL): return g->fundat.label_alt.l_a(arg); // if f is "label" function R_BETA : return f(v)
		case(POLY_LABEL): return g->fundat.poly.f.poly_label_alt.pl_a(arg, g->fundat.poly.tas);
		case(CLOSURE): return g->fundat.closure_alt.cls_alt.c_a(arg, g->fundat.closure_alt.fvs); // if f is closure R_BETA : return f(v, fvs)
		case(POLY_CLOSURE):	return g->fundat.poly.f.poly_closure_alt.pcls_alt.pc_a(arg, g->fundat.poly.f.poly_closure_alt.fvs, g->fundat.poly.tas); // if f is closure R_BETA : return f(v, fvs)
	}
}
#endif

#if !defined(CAST) && !defined(STATIC)
value appD(value f, value v, value w) {									// reduction of f(v)
	value s;
	value arg;
	fun *g;

    if (f.f->funkind == WRAPPED) {
		struct wrap wrap = f.f->fundat.wrap;
		s.s = compose(wrap.c->crcdat.two_crc.c2, w.s);
		arg = coerce(v, wrap.c->crcdat.two_crc.c1);
		g = wrap.w;
	} else {
		s.s = w.s;
		arg = v;
		g = f.f;
	}

	#ifdef ALT
	if (s.s->crckind == ID) {
		switch(g->funkind){
			case(LABEL): return g->fundat.label_alt.l_a(arg);	
			case(POLY_LABEL): return g->fundat.poly.f.poly_label_alt.pl_a(arg, g->fundat.poly.tas);
			case(CLOSURE): return g->fundat.closure_alt.cls_alt.c_a(arg, g->fundat.closure_alt.fvs);
			case(POLY_CLOSURE):	return g->fundat.poly.f.poly_closure_alt.pcls_alt.pc_a(arg, g->fundat.poly.f.poly_closure_alt.fvs, g->fundat.poly.tas);
		}
	} else {
		switch(g->funkind) {
			case(LABEL): return g->fundat.label_alt.l(arg, s);
			case(POLY_LABEL): return g->fundat.poly.f.poly_label_alt.pl(arg, s, g->fundat.poly.tas);
			case(CLOSURE): return g->fundat.closure_alt.cls_alt.c(arg, s, g->fundat.closure_alt.fvs);
			case(POLY_CLOSURE):	return g->fundat.poly.f.poly_closure_alt.pcls_alt.pc(arg, s, g->fundat.poly.f.poly_closure_alt.fvs, g->fundat.poly.tas);
		}
	}
	#else
	switch(g->funkind) {
		case(LABEL): return g->fundat.label(arg, s);
		case(POLY_LABEL): return g->fundat.poly.f.poly_label(arg, s, g->fundat.poly.tas);
		case(CLOSURE): return g->fundat.closure.cls(arg, s, g->fundat.closure.fvs);
		case(POLY_CLOSURE): return g->fundat.poly.f.poly_closure.pcls(arg, s, g->fundat.poly.f.poly_closure.fvs, g->fundat.poly.tas);
	}
	#endif
}
#endif