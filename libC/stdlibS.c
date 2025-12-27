#include <stdio.h>
#include <stdlib.h> //for abort
#include "coerce.h"
#include "coerceS.h"
#include "limits.h"
#include "gc.h"

value fun_print_int(value v, value w) {
	value retv;
	printf("%d", v.i_b_u);
	retv.i_b_u = 0;
	return coerce(retv, w.s);
}

value fun_print_bool(value v, value w) {
	value retv;
	int i = v.i_b_u;
	if (i == 1) {
		printf("true");
	} else if (i == 0) {
		printf("false");
	} else {
		printf("error:not boolean value is applied to print_bool");
		exit(1);
	}
	retv.i_b_u = 0;
	return coerce(retv, w.s);
}

value fun_print_newline(value v, value w) {
	value retv;
	int i = v.i_b_u;
	if (i == 0) {
		printf("\n");
	} else {
		printf("error:not unit value is applied to print_newline");
		exit(1);
	}
	retv.i_b_u = 0;
	return coerce(retv, w.s);
}

value fun_not(value b, value k) {
	if(b.i_b_u == 1) {
		value _retv = { .i_b_u = 0 };
		value retv = coerce(_retv, k.s);
		return retv;
	} else {
		value _retv = { .i_b_u = 1 };
		value retv = coerce(_retv, k.s);
		return retv;
	}
}

value fun_succ(value x, value k) {
	value _retv = { .i_b_u = x.i_b_u + 1 };
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_prec(value x, value k) {
	value _retv = { .i_b_u = x.i_b_u - 1 };
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_min_x(value y, value k, value zs[1]) {
	value x = zs[0];
	if(x.i_b_u < y.i_b_u) {
		value retv = coerce(x, k.s);
		return retv;
	} else {
		value retv = coerce(y, k.s);
		return retv;
	}
}

value fun_min(value x, value k) {
	value _retv;
	_retv.f = (fun*)GC_MALLOC(sizeof(fun));
	_retv.f->funkind = CLOSURE;
	_retv.f->fundat.closure.cls = fun_min_x;
	_retv.f->fundat.closure.fvs = (value*)GC_MALLOC(sizeof(value) * 1);
	_retv.f->fundat.closure.fvs[0] = x;
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_max_x(value y, value k, value zs[1]) {
	value x = zs[0];
	if(x.i_b_u > y.i_b_u) {
		value retv = coerce(x, k.s);
		return retv;
	} else {
		value retv = coerce(y, k.s);
		return retv;
	}
}

value fun_max(value x, value k) {
	value _retv;
	_retv.f = (fun*)GC_MALLOC(sizeof(fun));
	_retv.f->funkind = CLOSURE;
	_retv.f->fundat.closure.cls = fun_max_x;
	_retv.f->fundat.closure.fvs = (value*)GC_MALLOC(sizeof(value) * 1);
	_retv.f->fundat.closure.fvs[0] = x;
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_abs_ml(value x, value k) {
	if(x.i_b_u >= 0) {
		value retv = coerce(x, k.s);
		return retv;
	} else {
		value _retv = { .i_b_u = 0 - x.i_b_u };
		value retv = coerce(_retv, k.s);
		return retv;
	}
}

value fun_ignore(value x, value k, ty* tvs[1]) {
	value _retv = { .i_b_u = 0 };
	value retv = coerce(_retv, k.s);
	return retv;
}

value max_int = { .i_b_u = INT_MAX };
value min_int = { .i_b_u = INT_MIN };
value print_int;
value print_bool;
value print_newline;
value not;
value succ;
value prec;
value min;
value max;
value abs_ml;
value ignore;

int stdlibS() {
	print_int.f = (fun*)GC_MALLOC(sizeof(fun));
	print_int.f->fundat.label = fun_print_int;
	print_int.f->funkind = LABEL;
	print_bool.f = (fun*)GC_MALLOC(sizeof(fun));
	print_bool.f->fundat.label = fun_print_bool;
	print_bool.f->funkind = LABEL;
	print_newline.f = (fun*)GC_MALLOC(sizeof(fun));
	print_newline.f->fundat.label = fun_print_newline;
	print_newline.f->funkind = LABEL;
	not.f = (fun*)GC_MALLOC(sizeof(fun));
	not.f->fundat.label = fun_not;
	not.f->funkind = LABEL;
	succ.f = (fun*)GC_MALLOC(sizeof(fun));
	succ.f->fundat.label = fun_succ;
	succ.f->funkind = LABEL;
	prec.f = (fun*)GC_MALLOC(sizeof(fun));
	prec.f->fundat.label = fun_prec;
	prec.f->funkind = LABEL;
	min.f = (fun*)GC_MALLOC(sizeof(fun));
	min.f->fundat.label = fun_min;
	min.f->funkind = LABEL;
	max.f = (fun*)GC_MALLOC(sizeof(fun));
	max.f->fundat.label = fun_max;
	max.f->funkind = LABEL;
	abs_ml.f = (fun*)GC_MALLOC(sizeof(fun));
	abs_ml.f->fundat.label = fun_abs_ml;
	abs_ml.f->funkind = LABEL;
	ignore.f = (fun*)GC_MALLOC(sizeof(fun));
	ignore.f->fundat.poly_label = fun_ignore;
	ignore.f->funkind = POLY_LABEL;
	return 0;
}

//value print_newline_ = { .f = { .fundat = { .label = fun_print_newline }, .funkind = LABEL } };