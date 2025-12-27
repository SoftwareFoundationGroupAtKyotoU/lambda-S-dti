#include <stdio.h>
#include <stdlib.h> //for abort
#include "coerce.h"
#include "coerceA.h"
#include "limits.h"
#include "gc.h"

value fun_print_int(value v, value w) {
	value retv;
	printf("%d", v.i_b_u);
	retv.i_b_u = 0;
	return coerce(retv, w.s);
}

value fun_alt_print_int(value v) {
	value retv;
	printf("%d", v.i_b_u);
	retv.i_b_u = 0;
	return retv;
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

value fun_alt_print_bool(value v) {
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

value fun_alt_print_newline(value v) {
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

value fun_alt_not(value b) {
	if(b.i_b_u == 1) {
		value retv = { .i_b_u = 0 };
		return retv;
	} else {
		value retv = { .i_b_u = 1 };
		return retv;
	}
}

value fun_succ(value x, value k) {
	value _retv = { .i_b_u = x.i_b_u + 1 };
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_alt_succ(value x) {
	value retv = { .i_b_u = x.i_b_u + 1 };
	return retv;
}

value fun_prec(value x, value k) {
	value _retv = { .i_b_u = x.i_b_u - 1 };
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_alt_prec(value x) {
	value retv = { .i_b_u = x.i_b_u - 1 };
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

value fun_alt_min_x(value y, value zs[1]) {
	value x = zs[0];
	if(x.i_b_u < y.i_b_u) {
		return x;
	} else {
		return y;
	}
}

value fun_min(value x, value k) {
	value _retv;
	_retv.f = (fun*)GC_MALLOC(sizeof(fun));
	_retv.f->funkind = CLOSURE_alt;
	_retv.f->fundat.closure_alt.cls_alt.c = fun_min_x;
	_retv.f->fundat.closure_alt.cls_alt.c_a = fun_alt_min_x;
	_retv.f->fundat.closure_alt.fvs = (value*)GC_MALLOC(sizeof(value) * 1);
	_retv.f->fundat.closure_alt.fvs[0] = x;
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_alt_min(value x) {
	value retv;
	retv.f = (fun*)GC_MALLOC(sizeof(fun));
	retv.f->funkind = CLOSURE_alt;
	retv.f->fundat.closure_alt.cls_alt.c = fun_min_x;
	retv.f->fundat.closure_alt.cls_alt.c_a = fun_alt_min_x;
	retv.f->fundat.closure_alt.fvs = (value*)GC_MALLOC(sizeof(value) * 1);
	retv.f->fundat.closure_alt.fvs[0] = x;
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

value fun_alt_max_x(value y, value zs[1]) {
	value x = zs[0];
	if(x.i_b_u > y.i_b_u) {
		return x;
	} else {
		return y;
	}
}

value fun_max(value x, value k) {
	value _retv;
	_retv.f = (fun*)GC_MALLOC(sizeof(fun));
	_retv.f->funkind = CLOSURE_alt;
	_retv.f->fundat.closure_alt.cls_alt.c = fun_max_x;
	_retv.f->fundat.closure_alt.cls_alt.c_a = fun_alt_max_x;
	_retv.f->fundat.closure_alt.fvs = (value*)GC_MALLOC(sizeof(value) * 1);
	_retv.f->fundat.closure_alt.fvs[0] = x;
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_alt_max(value x) {
	value retv;
	retv.f = (fun*)GC_MALLOC(sizeof(fun));
	retv.f->funkind = CLOSURE_alt;
	retv.f->fundat.closure_alt.cls_alt.c = fun_max_x;
	retv.f->fundat.closure_alt.cls_alt.c_a = fun_alt_max_x;
	retv.f->fundat.closure_alt.fvs = (value*)GC_MALLOC(sizeof(value) * 1);
	retv.f->fundat.closure_alt.fvs[0] = x;
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

value fun_alt_abs_ml(value x) {
	if(x.i_b_u >= 0) {
		return x;
	} else {
		value retv = { .i_b_u = 0 - x.i_b_u };
		return retv;
	}
}

value fun_ignore(value x, value k, ty* tvs[1]) {
	value _retv = { .i_b_u = 0 };
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_alt_ignore(value x, ty* tvs[1]) {
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

int stdlibA() {
	print_int.f = (fun*)GC_MALLOC(sizeof(fun));
	print_int.f->fundat.label_alt.l = fun_print_int;
	print_int.f->fundat.label_alt.l_a = fun_alt_print_int;
	print_int.f->funkind = LABEL_alt;
	print_bool.f = (fun*)GC_MALLOC(sizeof(fun));
	print_bool.f->fundat.label_alt.l = fun_print_bool;
	print_bool.f->fundat.label_alt.l_a = fun_alt_print_bool;
	print_bool.f->funkind = LABEL_alt;
	print_newline.f = (fun*)GC_MALLOC(sizeof(fun));
	print_newline.f->fundat.label_alt.l = fun_print_newline;
	print_newline.f->fundat.label_alt.l_a = fun_alt_print_newline;
	print_newline.f->funkind = LABEL_alt;
	not.f = (fun*)GC_MALLOC(sizeof(fun));
	not.f->fundat.label_alt.l = fun_not;
	not.f->fundat.label_alt.l_a = fun_alt_not;
	not.f->funkind = LABEL_alt;
	succ.f = (fun*)GC_MALLOC(sizeof(fun));
	succ.f->fundat.label_alt.l = fun_succ;
	succ.f->fundat.label_alt.l_a = fun_alt_succ;
	succ.f->funkind = LABEL_alt;
	prec.f = (fun*)GC_MALLOC(sizeof(fun));
	prec.f->fundat.label_alt.l = fun_prec;
	prec.f->fundat.label_alt.l_a = fun_alt_prec;
	prec.f->funkind = LABEL_alt;
	min.f = (fun*)GC_MALLOC(sizeof(fun));
	min.f->fundat.label_alt.l = fun_min;
	min.f->fundat.label_alt.l_a = fun_alt_min;
	min.f->funkind = LABEL_alt;
	max.f = (fun*)GC_MALLOC(sizeof(fun));
	max.f->fundat.label_alt.l = fun_max;
	max.f->fundat.label_alt.l_a = fun_alt_max;
	max.f->funkind = LABEL_alt;
	abs_ml.f = (fun*)GC_MALLOC(sizeof(fun));
	abs_ml.f->fundat.label_alt.l = fun_abs_ml;
	abs_ml.f->fundat.label_alt.l_a = fun_alt_abs_ml;
	abs_ml.f->funkind = LABEL_alt;
	ignore.f = (fun*)GC_MALLOC(sizeof(fun));
	ignore.f->fundat.poly_label_alt.pl = fun_ignore;
	ignore.f->fundat.poly_label_alt.pl_a = fun_alt_ignore;
	ignore.f->funkind = POLY_LABEL_alt;
	return 0;
}

//value print_newline_ = { .f = { .fundat = { .label = fun_print_newline }, .funkind = LABEL } };