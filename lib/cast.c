#include <stdio.h>
#include <stdlib.h> //for abort
#include "cast.h"
#include "gc.h"

ty tydyn = { .tykind = DYN };
ty tyint = { .tykind = BASE_INT };
ty tybool = { .tykind = BASE_BOOL };
ty tyunit = { .tykind = BASE_UNIT };
ty tyar = { .tykind = TYFUN, .tydat = { .tyfun = { .left = &tydyn, .right = &tydyn } } };
ty tyli = { .tykind = TYLIST, .tydat = { .tylist = &tydyn } };

ty *newty() {
	ty *retty = (ty*)GC_MALLOC(sizeof(ty));
	retty->tykind = TYVAR;
	return retty;
}

int blame(ran_pol r_p){
	if(r_p.polarity==1) {
		printf("Blame on the expression side:\n");
	} else {
		printf("Blame on the environment side:\n");
	}
	printf("%sline %d, character %d -- line %d, character %d\n", r_p.filename, r_p.startline, r_p.startchr, r_p.endline, r_p.endchr);
	return 0;
}

int is_ground(ty t) {
	if (t.tykind == BASE_INT || t.tykind == BASE_BOOL || t.tykind == BASE_UNIT) {
		return 1;
	} else if (t.tykind == TYFUN && t.tydat.tyfun.left->tykind == DYN && t.tydat.tyfun.right->tykind == DYN) {
		return 1;
	} else if (t.tykind == TYLIST && t.tydat.tylist->tykind == DYN) {
		return 1;
	} else {
		return 0;
	}
}

ground_ty to_ground(ty t) {
	if (t.tykind == BASE_INT) {
		return G_INT;
	} else if (t.tykind == BASE_BOOL) {
		return G_BOOL;
	} else if (t.tykind == BASE_UNIT) {
		return G_UNIT;
	} else if (t.tykind == TYFUN && t.tydat.tyfun.left->tykind == DYN && t.tydat.tyfun.right->tykind == DYN) {
		return G_AR;
	} else if (t.tykind == TYLIST && t.tydat.tylist->tykind == DYN) {
		return G_LI;
	} else {
		printf("not ground type was applied\n");
		exit(1);
	}
}

value cast(value x, ty *t1, ty *t2, ran_pol r_p) {			// input = x:t1=>t2
	value retx;

	if (t1->tykind == TYFUN && t2->tykind == TYFUN) { 				// when t1 and t2 are function type
		// printf("defined as a wrapped function\n");						// define x:U1->U2=>U3->U4 as wrapped function
		retx.f = (fun*)GC_MALLOC(sizeof(fun));
		retx.f->fundat.wrap.w = (fun*)GC_MALLOC(sizeof(fun));
		retx.f->fundat.wrap.w = x.f;
		retx.f->fundat.wrap.u1 = t1->tydat.tyfun.left;
		retx.f->fundat.wrap.u2 = t1->tydat.tyfun.right;
		retx.f->fundat.wrap.u3 = t2->tydat.tyfun.left;
		retx.f->fundat.wrap.u4 = t2->tydat.tyfun.right;
		retx.f->fundat.wrap.r_p = r_p;
		retx.f->funkind = WRAPPED;
	} else if (t1->tykind == TYLIST && t2->tykind == TYLIST) {
		// printf("defined as a wrapped list\n");						// define x:[U1]=>[U2] as wrapped list
		retx.l = (lst*)GC_MALLOC(sizeof(lst));
		retx.l->lstdat.wrap_l.w = (lst*)GC_MALLOC(sizeof(lst));
		retx.l->lstdat.wrap_l.w = x.l;
		retx.l->lstdat.wrap_l.u1 = t1->tydat.tylist;
		retx.l->lstdat.wrap_l.u2 = t2->tydat.tylist;
		retx.l->lstdat.wrap_l.r_p = r_p;
		retx.l->lstkind = WRAPPED_LIST;
	} else if (is_ground(*t1) == 1 && t2->tykind == DYN) {			// when t1 is ground and t2 is ?
		// printf("defined as a dyn value\n");								// define x:G=>? as dynamic type value
		retx.d = (dyn*)GC_MALLOC(sizeof(dyn));
		retx.d->v = (value*)GC_MALLOC(sizeof(value));
		*retx.d->v = x;
		retx.d->g = to_ground(*t1);
		retx.d->r_p = r_p;
	} else if (t1->tykind == DYN && t2->tykind == DYN) {			// when t1 and t2 are ?
		// printf ("ID STAR\n");											// R_IDSTAR (x:?=>? -> x)
		retx = x;
	} else if (t1->tykind == BASE_INT && t2->tykind == BASE_INT) {	// when t1 and t2 are int
		// printf ("ID BASE by int\n");									// R_IDBASE (x:int=>int -> x)
		retx = x;
	} else if (t1->tykind == BASE_BOOL && t2->tykind == BASE_BOOL) {// when t1 and t2 are bool
		// printf ("ID BASE by bool\n");									// R_IDBASE (x:bool=>bool -> x)
		retx = x;
	} else if (t1->tykind == BASE_UNIT && t2->tykind == BASE_UNIT) {// when t1 and t2 are unit
		// printf ("ID BASE by unit\n");									// R_IDBASE (x:unit=>unit -> x)
		retx = x;
	} else if (t1->tykind == DYN && is_ground(*t2) == 1) {			// when t1 is ? and t2 is ground type
		ground_ty t = x.d->g;
		ground_ty t_ = to_ground(*t2);
		if (t == t_) {													// when t1's injection ground type equals t2
			// printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
			retx = *x.d->v;
		} else if (t != t_) {											// when t1's injection ground type dosen't equal t2
			printf("cast fail. t:%d, t_:%d\n", t, t_);											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
			blame(r_p);
			exit(1);
		} else {
			// printf("cannot reachable\n");
			exit(1);
		}
	} else if (t1->tykind == TYFUN && t2->tykind == DYN) {			// when t1 is function type and t2 is ?
		// printf("cast ground\n");
		value x_ = cast(x, t1, &tyar, r_p);									// R_GROUND (x:U=>? -> x:U=>G=>?)
		retx = cast(x_, &tyar, t2, r_p);
	} else if (t1->tykind == DYN && t2->tykind == TYFUN) {			// when t1 is ? and t2 is function type
		// printf("cast expand\n");
		value x_ = cast(x, t1, &tyar, r_p);									// R_EXPAND (x:?=>U -> x:?=>G=>U)
		retx = cast(x_, &tyar, t2, r_p); 
	} else if (t1->tykind == TYLIST && t2->tykind == DYN) {			// when t1 is list type and t2 is ?
		// printf("cast ground\n");
		value x_ = cast(x, t1, &tyli, r_p);									// R_GROUND (x:U=>? -> x:U=>G=>?)
		retx = cast(x_, &tyli, t2, r_p);
	} else if (t1->tykind == DYN && t2->tykind == TYLIST) {			// when t1 is ? and t2 is list type
		// printf("cast expand\n");
		value x_ = cast(x, t1, &tyli, r_p);									// R_EXPAND (x:?=>U -> x:?=>G=>U)
		retx = cast(x_, &tyli, t2, r_p); 
	} else if (t1->tykind == DYN && t2->tykind == TYVAR) {			// when t1 is ? and t2 is type variable
		switch(x.d->g) {
			case(G_INT):												// when t1's injection ground type is int
			// printf("DTI : int was inferred\n");							// R_INSTBASE (x':int=>?=>X -[X:=int]> x')
			*t2 = tyint;
			retx = *x.d->v;
			break;

			case(G_BOOL):												// when t1's injection ground type is bool	
			// printf("DTI : bool was inferred\n");							// R_INSTBASE (x':bool=>?=>X -[X:=bool]> x')
			*t2 = tybool;
			retx = *x.d->v;
			break;

			case(G_UNIT):												// when t1's injection ground type is unit
			// printf("DTI : unit was inferred\n");							// R_INSTBASE (x':unit=>?=>X -[X:=unit]> x')
			*t2 = tyunit;
			retx = *x.d->v;
			break;

			case(G_AR):													// when t1's injection ground type is ?->?
			// printf("DTI : arrow was inferenced\n");							// R_INSTARROW (x':?->?=>?=>X -[X:=X_1->X_2]> x':?->?=>X_1->X_2)
			t2->tykind = TYFUN;
			t2->tydat.tyfun.left = (ty*)GC_MALLOC(sizeof(ty));
			t2->tydat.tyfun.right = (ty*)GC_MALLOC(sizeof(ty));
			t2->tydat.tyfun.left->tykind = TYVAR;
			t2->tydat.tyfun.right->tykind = TYVAR;
			retx = cast(*x.d->v, &tyar, t2, r_p);
			break;

			case(G_LI):													// when t1's injection ground type is [?]
			// printf("DTI : list was inferenced\n");							// R_INSTLIST (x':[?]=>?=>X -[X:=X_1->X_2]> x':[?]=>[X_1])
			t2->tykind = TYLIST;
			t2->tydat.tylist = (ty*)GC_MALLOC(sizeof(ty));
			t2->tydat.tylist->tykind = TYVAR;
			retx = cast(*x.d->v, &tyli, t2, r_p);
			break;
		}
	} else {
		printf("cast cannot be resolved. t1: %d, t2: %d\n", t1->tykind, t2->tykind);
		exit(1);
	}
	return retx;
}

value app(value f, value v) {									// reduction of f(v)
	value retx;
	value (*l)(value);
	value (*c)(value, value*);
	value (*pl)(value, ty**);
	value (*pc)(value, value*, ty**);
	ran_pol neg_r_p;
	switch(f.f->funkind) {
		case(LABEL):												// if f is "label" function
		l = f.f->fundat.label;							// R_BETA : return f(v)
		retx = l(v);
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		break;

		case(POLY_LABEL):
		pl = f.f->fundat.poly_label;
		retx = pl(v, f.f->tas);
		break;

		case(CLOSURE):												// if f is closure
		c = f.f->fundat.closure.cls;				// R_BETA : return f(v, fvs)
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		retx = c(v, f.f->fundat.closure.fvs);
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		break;

		case(POLY_CLOSURE):												// if f is closure
		pc = f.f->fundat.poly_closure.pcls;				// R_BETA : return f(v, fvs)
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		retx = pc(v, f.f->fundat.poly_closure.fvs, f.f->tas);
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		break;

		case(WRAPPED):												// if f is wrapped function (f = w:U1->U2=>U3->U4)
		neg_r_p = f.f->fundat.wrap.r_p;
		if(neg_r_p.polarity==1){
			neg_r_p.polarity = 0;
		} else {
			neg_r_p.polarity = 1;
		} {
		value f1;														// R_APPCAST : return (w(v:U3=>U1)):U2=>U4
		f1.f = f.f->fundat.wrap.w;
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		value v_ = cast(v, f.f->fundat.wrap.u3, f.f->fundat.wrap.u1, neg_r_p);
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		value v__ = app(f1, v_);
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		retx = cast(v__, f.f->fundat.wrap.u2, f.f->fundat.wrap.u4, f.f->fundat.wrap.r_p);
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		break;
		}
	}
	return retx;
}

value hd(lst l) {
	if (l.lstkind == WRAPPED_LIST) {
		if (l.lstdat.wrap_l.w == NULL) {
			printf ("hd NULL");
			exit(1);
		} else {
			return cast(hd(*l.lstdat.wrap_l.w), l.lstdat.wrap_l.u1, l.lstdat.wrap_l.u2, l.lstdat.wrap_l.r_p);
		}
	} else {
		return *l.lstdat.unwrap_l.h;
	}
}

value tl(lst l) {
	if (l.lstkind == WRAPPED_LIST) {
		ty *u1 = (ty*)GC_MALLOC(sizeof(ty));
		ty *u2 = (ty*)GC_MALLOC(sizeof(ty));
		u1->tykind = TYLIST;
		u1->tydat.tylist = l.lstdat.wrap_l.u1;
		u2->tykind = TYLIST;
		u2->tydat.tylist = l.lstdat.wrap_l.u2;
		return cast(tl(*l.lstdat.wrap_l.w), u1, u2, l.lstdat.wrap_l.r_p);
	} else {
		return *l.lstdat.unwrap_l.t;
	}
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

int did_not_match() {
	printf("didn't match");
	exit(1);
}