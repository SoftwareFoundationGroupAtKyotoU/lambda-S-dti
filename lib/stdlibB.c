#include <stdio.h>
#include <stdlib.h> //for abort
#include "cast.h"
#include "limits.h"
#include "gc.h"

value fun_print_int(value v) {
	value retv;
	printf("%d", v.i_b_u);
	retv.i_b_u = 0;
	return retv;
}

value fun_print_bool(value v) {
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
	return retv;
}

value fun_print_newline(value v) {
	value retv;
	int i = v.i_b_u;
	if (i == 0) {
		printf("\n");
	} else {
		printf("error:not unit value is applied to print_newline");
		exit(1);
	}
	retv.i_b_u = 0;
	return retv;
}

value fun_not(value b) {
	if(b.i_b_u == 1) {
		value retv = { .i_b_u = 0 };
		return retv;
	} else {
		value retv = { .i_b_u = 1 };
		return retv;
	}
}

value fun_succ(value x) {
	value retv = { .i_b_u = x.i_b_u + 1 };
	return retv;
}

value fun_prec(value x) {
	value retv = { .i_b_u = x.i_b_u - 1 };
	return retv;
}

value fun_min_x(value y, value zs[1]) {
	value x = zs[0];
	if(x.i_b_u < y.i_b_u) {
		return x;
	} else {
		return y;
	}
}

value fun_min(value x) {
	value retv;
	retv.f = (fun*)GC_MALLOC(sizeof(fun));
	retv.f->funkind = CLOSURE;
	retv.f->fundat.closure.cls = fun_min_x;
	retv.f->fundat.closure.fvs = (value*)GC_MALLOC(sizeof(value) * 1);
	retv.f->fundat.closure.fvs[0] = x;
	return retv;
}

value fun_max_x(value y, value zs[1]) {
	value x = zs[0];
	if(x.i_b_u > y.i_b_u) {
		return x;
	} else {
		return y;
	}
}

value fun_max(value x) {
	value retv;
	retv.f = (fun*)GC_MALLOC(sizeof(fun));
	retv.f->funkind = CLOSURE;
	retv.f->fundat.closure.cls = fun_max_x;
	retv.f->fundat.closure.fvs = (value*)GC_MALLOC(sizeof(value) * 1);
	retv.f->fundat.closure.fvs[0] = x;
	return retv;
}

value fun_abs_ml(value x) {
	if(x.i_b_u >= 0) {
		return x;
	} else {
		value retv = { .i_b_u = 0 - x.i_b_u };
		return retv;
	}
}

value fun_ignore(value x, ty* tvs[1]) {
	value retv = { .i_b_u = 0 };
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

int stdlibB() {
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