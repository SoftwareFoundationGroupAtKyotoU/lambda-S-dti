#include "runtime.h"
#include "limits.h"
#include "stdlib.h"

#ifdef ALT
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

value fun_not_ml(value b, value k) {
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

value fun_alt_not_ml(value b) {
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
	_retv.f->funkind = CLOSURE;
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
	retv.f->funkind = CLOSURE;
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
	_retv.f->funkind = CLOSURE;
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
	retv.f->funkind = CLOSURE;
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
#elif defined(CAST)
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

value fun_not_ml(value b) {
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
#else
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

value fun_not_ml(value b, value k) {
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
#endif

value max_int = { .i_b_u = INT_MAX };
value min_int = { .i_b_u = INT_MIN };
value print_int;
value print_bool;
value print_newline;
value not_ml;
value succ;
value prec;
value min;
value max;
value abs_ml;
value ignore;

int stdlib() {
	fun *funs = (fun*)GC_MALLOC(sizeof(fun) * 10);
	print_int.f = &funs[0];
	print_int.f->funkind = LABEL;
	print_bool.f = &funs[1];
	print_bool.f->funkind = LABEL;
	print_newline.f = &funs[2];
	print_newline.f->funkind = LABEL;
	not_ml.f = &funs[3];
	not_ml.f->funkind = LABEL;
	succ.f = &funs[4];
	succ.f->funkind = LABEL;
	prec.f = &funs[5];
	prec.f->funkind = LABEL;
	min.f = &funs[6];
	min.f->funkind = LABEL;
	max.f = &funs[7];
	max.f->funkind = LABEL;
	abs_ml.f = &funs[8];
	abs_ml.f->funkind = LABEL;
	ignore.f = &funs[9];
	ignore.f->funkind = POLY_LABEL;
	#ifdef ALT
	print_int.f->fundat.label_alt.l = fun_print_int;
	print_int.f->fundat.label_alt.l_a = fun_alt_print_int;
	print_bool.f->fundat.label_alt.l = fun_print_bool;
	print_bool.f->fundat.label_alt.l_a = fun_alt_print_bool;
	print_newline.f->fundat.label_alt.l = fun_print_newline;
	print_newline.f->fundat.label_alt.l_a = fun_alt_print_newline;
	not_ml.f->fundat.label_alt.l = fun_not_ml;
	not_ml.f->fundat.label_alt.l_a = fun_alt_not_ml;
	succ.f->fundat.label_alt.l = fun_succ;
	succ.f->fundat.label_alt.l_a = fun_alt_succ;
	prec.f->fundat.label_alt.l = fun_prec;
	prec.f->fundat.label_alt.l_a = fun_alt_prec;
	min.f->fundat.label_alt.l = fun_min;
	min.f->fundat.label_alt.l_a = fun_alt_min;
	max.f->fundat.label_alt.l = fun_max;
	max.f->fundat.label_alt.l_a = fun_alt_max;
	abs_ml.f->fundat.label_alt.l = fun_abs_ml;
	abs_ml.f->fundat.label_alt.l_a = fun_alt_abs_ml;
	ignore.f->fundat.poly_label_alt.pl = fun_ignore;
	ignore.f->fundat.poly_label_alt.pl_a = fun_alt_ignore;
	#else
	print_int.f->fundat.label = fun_print_int;
	print_bool.f->fundat.label = fun_print_bool;
	print_newline.f->fundat.label = fun_print_newline;
	not_ml.f->fundat.label = fun_not_ml;
	succ.f->fundat.label = fun_succ;
	prec.f->fundat.label = fun_prec;
	min.f->fundat.label = fun_min;
	max.f->fundat.label = fun_max;
	abs_ml.f->fundat.label = fun_abs_ml;
	ignore.f->fundat.poly_label = fun_ignore;
	#endif

	return 0;
}

//value print_newline_ = { .f = { .fundat = { .label = fun_print_newline }, .funkind = LABEL } };