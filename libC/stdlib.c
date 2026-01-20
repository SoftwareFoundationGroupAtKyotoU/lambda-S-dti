#include "runtime.h"
#include "stdlib.h"

#ifdef ALT
value fun_print_int(value v, value w) {
	value retv;
	printf("%ld", v.i_b_u);
	retv.i_b_u = 0;
	return coerce(retv, w.s);
}

value fun_alt_print_int(value v) {
	value retv;
	printf("%ld", v.i_b_u);
	retv.i_b_u = 0;
	return retv;
}

value fun_print_bool(value v, value w) {
	value retv;
	int64_t i = v.i_b_u;
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
	int64_t i = v.i_b_u;
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
	int64_t i = v.i_b_u;
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
	int64_t i = v.i_b_u;
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

#elif defined(CAST) || defined(STATIC)
value fun_print_int(value v) {
	value retv;
	printf("%ld", v.i_b_u);
	retv.i_b_u = 0;
	return retv;
}

value fun_print_bool(value v) {
	value retv;
	int64_t i = v.i_b_u;
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
	int64_t i = v.i_b_u;
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

#ifdef STATIC
value fun_ignore(value x) {
	value retv = { .i_b_u = 0 };
	return retv;
}
#elif
value fun_ignore(value x, ty* tvs[1]) {
	value retv = { .i_b_u = 0 };
	return retv;
}
#endif

#else
value fun_print_int(value v, value w) {
	value retv;
	printf("%ld", v.i_b_u);
	retv.i_b_u = 0;
	return coerce(retv, w.s);
}

value fun_print_bool(value v, value w) {
	value retv;
	int64_t i = v.i_b_u;
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
	int64_t i = v.i_b_u;
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

#ifdef ALT
#define INIT_LABEL(func, func_alt) \
    { .funkind = LABEL, \
      .fundat = { .label_alt = { .l = (func), .l_a = (func_alt) } } }
#define INIT_POLY_LABEL(func, func_alt) \
    { .funkind = POLY_LABEL, \
      .fundat = { .poly = { .f = { .poly_label_alt = { .pl = (func), .pl_a = (func_alt) } } } } }
#else 
#define INIT_LABEL(func) \
    { .funkind = LABEL, \
      .fundat = { .label = (func) } }
#ifndef STATIC
#define INIT_POLY_LABEL(func) \
    { .funkind = POLY_LABEL, \
      .fundat = { .poly = { .f = { .poly_label = (func) } } } }
#endif
#endif

#ifdef ALT
static fun f_print_int     = INIT_LABEL(fun_print_int,     fun_alt_print_int);
static fun f_print_bool    = INIT_LABEL(fun_print_bool,    fun_alt_print_bool);
static fun f_print_newline = INIT_LABEL(fun_print_newline, fun_alt_print_newline);
static fun f_not_ml        = INIT_LABEL(fun_not_ml,        fun_alt_not_ml);
static fun f_succ          = INIT_LABEL(fun_succ,          fun_alt_succ);
static fun f_prec          = INIT_LABEL(fun_prec,          fun_alt_prec);
static fun f_min           = INIT_LABEL(fun_min,           fun_alt_min);
static fun f_max           = INIT_LABEL(fun_max,           fun_alt_max);
static fun f_abs_ml        = INIT_LABEL(fun_abs_ml,        fun_alt_abs_ml);
static fun f_ignore        = INIT_POLY_LABEL(fun_ignore,   fun_alt_ignore);
#else
static fun f_print_int     = INIT_LABEL(fun_print_int);
static fun f_print_bool    = INIT_LABEL(fun_print_bool);
static fun f_print_newline = INIT_LABEL(fun_print_newline);
static fun f_not_ml        = INIT_LABEL(fun_not_ml);
static fun f_succ          = INIT_LABEL(fun_succ);
static fun f_prec          = INIT_LABEL(fun_prec);
static fun f_min           = INIT_LABEL(fun_min);
static fun f_max           = INIT_LABEL(fun_max);
static fun f_abs_ml        = INIT_LABEL(fun_abs_ml);
#ifdef STATIC
static fun f_ignore        = INIT_LABEL(fun_ignore);
#elif
static fun f_ignore        = INIT_POLY_LABEL(fun_ignore);
#endif
#endif

value max_int = { .i_b_u = INT64_MAX };
value min_int = { .i_b_u = INT64_MIN };
value print_int = { .f = &f_print_int };
value print_bool = { .f = &f_print_bool };
value print_newline = { .f = &f_print_newline };
value not_ml = { .f = &f_not_ml };
value succ = { .f = &f_succ };
value prec = { .f = &f_prec };
value min = { .f = &f_min };
value max = { .f = &f_max };
value abs_ml = { .f = &f_abs_ml };
value ignore = { .f = &f_ignore };