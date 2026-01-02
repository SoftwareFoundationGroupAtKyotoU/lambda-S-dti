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

#ifdef CAST
value appM(value f, value v) {									// reduction of f(v)
	switch(f.f->funkind) {
		case(LABEL): {												// if f is "label" function
			value (*l)(value);
			l = f.f->fundat.label;							// R_BETA : return f(v)
			return l(v);
		}

		case(POLY_LABEL): {
			value (*pl)(value, ty**);
			pl = f.f->fundat.poly_label;
			return pl(v, f.f->tas);
		}

		case(CLOSURE): {											// if f is closure
			value (*c)(value, value*);
			c = f.f->fundat.closure.cls;				// R_BETA : return f(v, fvs)
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			return c(v, f.f->fundat.closure.fvs);
		}

		case(POLY_CLOSURE):	{											// if f is closure
			value (*pc)(value, value*, ty**);
			pc = f.f->fundat.poly_closure.pcls;				// R_BETA : return f(v, fvs)
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			return pc(v, f.f->fundat.poly_closure.fvs, f.f->tas);
		}

		case(WRAPPED): {												// if f is wrapped function (f = w:U1->U2=>U3->U4)
			ran_pol neg_r_p;
			neg_r_p = f.f->fundat.wrap.r_p;
			if(neg_r_p.polarity == 1){
				neg_r_p.polarity = 0;
			} else {
				neg_r_p.polarity = 1;
			}
			value f1;														// R_APPCAST : return (w(v:U3=>U1)):U2=>U4
			f1.f = f.f->fundat.wrap.w;
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			value v_ = cast(v, f.f->fundat.wrap.u3, f.f->fundat.wrap.u1, neg_r_p);
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			value v__ = appM(f1, v_);
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			return cast(v__, f.f->fundat.wrap.u2, f.f->fundat.wrap.u4, f.f->fundat.wrap.r_p);
		}
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
		s.s = f.f->fundat.wrap.c_res;
		arg = coerce(v, f.f->fundat.wrap.c_arg);
		g = f.f->fundat.wrap.w;
		if (s.s->crckind != ID) {
			switch(g->funkind) {
				case(LABEL): {												// if f is "label" function
					value (*l)(value, value);
					l = g->fundat.label_alt.l;							// R_BETA : return f(v)
					return l(arg, s);
				}
			
				case(POLY_LABEL): {
					value (*pl)(value, value, ty**);
					pl = g->fundat.poly_label_alt.pl;
					return pl(arg, s, g->tas);
				}
			
				case(CLOSURE): {												// if f is closure
					value (*c)(value, value, value*);
					c = g->fundat.closure_alt.cls_alt.c;				// R_BETA : return f(v, fvs)
					//printf("Heap size = %d\n", (int)GC_get_heap_size());
					return c(arg, s, g->fundat.closure_alt.fvs);
				}
			
				case(POLY_CLOSURE):	{											// if f is closure
					value (*pc)(value, value, value*, ty**);
					pc = g->fundat.poly_closure_alt.pcls_alt.pc;				// R_BETA : return f(v, fvs)
					//printf("Heap size = %d\n", (int)GC_get_heap_size());
					return pc(arg, s, g->fundat.poly_closure_alt.fvs, g->tas);
				}
			}
		}
	} else {
		arg = v;
		g = f.f;
	}


	switch(g->funkind) {
		case(LABEL): {												// if f is "label" function
			value (*l_a)(value);
			l_a = g->fundat.label_alt.l_a;							// R_BETA : return f(v)
			return l_a(arg);
		}

		case(POLY_LABEL): {
			value (*pl_a)(value, ty**);
			pl_a = g->fundat.poly_label_alt.pl_a;
			return pl_a(arg, g->tas);
		}

		case(CLOSURE): {												// if f is closure
			value (*c_a)(value, value*);
			c_a = g->fundat.closure_alt.cls_alt.c_a;				// R_BETA : return f(v, fvs)
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			return c_a(arg, g->fundat.closure_alt.fvs);
		}

		case(POLY_CLOSURE):	{											// if f is closure
			value (*pc_a)(value, value*, ty**);
			pc_a = g->fundat.poly_closure_alt.pcls_alt.pc_a;				// R_BETA : return f(v, fvs)
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			return pc_a(arg, g->fundat.poly_closure_alt.fvs, g->tas);
		}
	}
}
#endif

#ifndef CAST
value appD(value f, value v, value w) {									// reduction of f(v)
	value s;
	value arg;
	fun *g;

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
		case(LABEL): 
		#ifdef ALT
		if (s.s->crckind == ID) {
			value (*l_a)(value);
			l_a = g->fundat.label_alt.l_a;
			return l_a(arg);
		} else {
			value (*l)(value, value);
			l = g->fundat.label_alt.l;							// R_BETA : return f(v)
			return l(arg, s);
		}
		#else
		{												// if f is "label" function
			value (*l)(value, value);
			l = g->fundat.label;							// R_BETA : return f(v)
			return l(arg, s);
		}
		#endif

		case(POLY_LABEL): 
		#ifdef ALT
		if (s.s->crckind == ID) {
			value (*pl_a)(value, ty**);
			pl_a = g->fundat.poly_label_alt.pl_a;
			return pl_a(arg, g->tas);
		} else {
			value (*pl)(value, value, ty**);
			pl = g->fundat.poly_label_alt.pl;
			return pl(arg, s, g->tas);
		}
		#else
		{
			value (*pl)(value, value, ty**);
			pl = g->fundat.poly_label;
			return pl(arg, s, g->tas);
		}
		#endif

		case(CLOSURE): 
		#ifdef ALT
		if (s.s->crckind == ID) {
			value (*c_a)(value, value*);
			c_a = g->fundat.closure_alt.cls_alt.c_a;
			return c_a(arg, g->fundat.closure_alt.fvs);
		} else {
			value (*c)(value, value, value*);
			c = g->fundat.closure_alt.cls_alt.c;				// R_BETA : return f(v, fvs)
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			return c(arg, s, g->fundat.closure_alt.fvs);
		}
		#else
		{												// if f is closure
			value (*c)(value, value, value*);
			c = g->fundat.closure.cls;				// R_BETA : return f(v, fvs)
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			return c(arg, s, g->fundat.closure.fvs);
		}
		#endif
		
		case(POLY_CLOSURE):	
		#ifdef ALT
		if (s.s->crckind == ID) {
			value (*pc_a)(value, value*, ty**);
			pc_a = g->fundat.poly_closure_alt.pcls_alt.pc_a;
			return pc_a(arg, g->fundat.closure_alt.fvs, g->tas);
		} else {
			value (*pc)(value, value, value*, ty**);
			pc = g->fundat.poly_closure_alt.pcls_alt.pc;				// R_BETA : return f(v, fvs)
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			return pc(arg, s, g->fundat.poly_closure_alt.fvs, g->tas);
		}
		#else
		{											// if f is closure
			value (*pc)(value, value, value*, ty**);
			pc = g->fundat.poly_closure.pcls;				// R_BETA : return f(v, fvs)
			//printf("Heap size = %d\n", (int)GC_get_heap_size());
			return pc(arg, s, g->fundat.poly_closure.fvs, g->tas);
		}
		#endif
	}
}
#endif