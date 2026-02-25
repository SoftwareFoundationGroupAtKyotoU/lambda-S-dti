#include "runtime.h"
#include "stdlib.h"

#ifdef ALT
value fun_print_int(value cls, value v, value w) {
	value retv;
	printf("%ld", v.i_b_u);
	retv.i_b_u = 0;
	return coerce(retv, w.s);
}

value fun_alt_print_int(value cls, value v) {
	value retv;
	printf("%ld", v.i_b_u);
	retv.i_b_u = 0;
	return retv;
}

value fun_print_bool(value cls, value v, value w) {
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

value fun_alt_print_bool(value cls, value v) {
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

value fun_print_newline(value cls, value v, value w) {
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

value fun_alt_print_newline(value cls, value v) {
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

value fun_read_int(value cls, value v, value w) {
	value retv;
	int64_t i = v.i_b_u;
	if (i == 0) {
		if (scanf("%ld", &retv.i_b_u) != 1) {
		    printf("Error: Input format error or EOF.");
		    exit(1);
		}
	} else {
		printf("error:not unit value is applied to read_int");
		exit(1);
	}
	return coerce(retv, w.s);
}

value fun_alt_read_int(value cls, value v) {
	value retv;
	int64_t i = v.i_b_u;
	if (i == 0) {
		if (scanf("%ld", &retv.i_b_u) != 1) {
		    printf("Error: Input format error or EOF.");
		    exit(1);
		}
	} else {
		printf("error:not unit value is applied to read_int");
		exit(1);
	}
	return retv;
}

value fun_not_ml(value cls, value b, value k) {
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

value fun_alt_not_ml(value cls, value b) {
	if(b.i_b_u == 1) {
		value retv = { .i_b_u = 0 };
		return retv;
	} else {
		value retv = { .i_b_u = 1 };
		return retv;
	}
}

value fun_succ(value cls, value x, value k) {
	value _retv = { .i_b_u = x.i_b_u + 1 };
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_alt_succ(value cls, value x) {
	value retv = { .i_b_u = x.i_b_u + 1 };
	return retv;
}

value fun_prec(value cls, value x, value k) {
	value _retv = { .i_b_u = x.i_b_u - 1 };
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_alt_prec(value cls, value x) {
	value retv = { .i_b_u = x.i_b_u - 1 };
	return retv;
}

value fun_min_x(value cls, value y, value k) {
	value x = (value){ .i_b_u = (uintptr_t)cls.f->env[0] };
	if(x.i_b_u < y.i_b_u) {
		value retv = coerce(x, k.s);
		return retv;
	} else {
		value retv = coerce(y, k.s);
		return retv;
	}
}

value fun_alt_min_x(value cls, value y) {
	value x = (value){ .i_b_u = (uintptr_t)cls.f->env[0] };
	if(x.i_b_u < y.i_b_u) {
		return x;
	} else {
		return y;
	}
}

value fun_min(value cls, value x, value k) {
	value _retv;
	_retv.f = (fun*)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1);
	_retv.f->funcM = fun_alt_min_x;
	_retv.f->funcD = fun_min_x;
	_retv.f->env[0] = (void*)x.i_b_u;
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_alt_min(value cls, value x) {
	value retv;
	retv.f = (fun*)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1);
	retv.f->funcM = fun_alt_min_x;
	retv.f->funcD = fun_min_x;
	retv.f->env[0] = (void*)x.i_b_u;
	return retv;
}

value fun_max_x(value cls, value y, value k) {
	value x = (value){ .i_b_u = (uintptr_t)cls.f->env[0] };
	if(x.i_b_u > y.i_b_u) {
		value retv = coerce(x, k.s);
		return retv;
	} else {
		value retv = coerce(y, k.s);
		return retv;
	}
}

value fun_alt_max_x(value cls, value y) {
	value x = (value){ .i_b_u = (uintptr_t)cls.f->env[0] };
	if(x.i_b_u > y.i_b_u) {
		return x;
	} else {
		return y;
	}
}

value fun_max(value cls, value x, value k) {
	value _retv;
	_retv.f = (fun*)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1);
	_retv.f->funcM = fun_alt_max_x;
	_retv.f->funcD = fun_max_x;
	_retv.f->env[0] = (void*)x.i_b_u;
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_alt_max(value cls, value x) {
	value retv;
	retv.f = (fun*)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1);
	retv.f->funcM = fun_alt_max_x;
	retv.f->funcD = fun_max_x;
	retv.f->env[0] = (void*)x.i_b_u;
	return retv;
}

value fun_abs_ml(value cls, value x, value k) {
	if(x.i_b_u >= 0) {
		value retv = coerce(x, k.s);
		return retv;
	} else {
		value _retv = { .i_b_u = 0 - x.i_b_u };
		value retv = coerce(_retv, k.s);
		return retv;
	}
}

value fun_alt_abs_ml(value cls, value x) {
	if(x.i_b_u >= 0) {
		return x;
	} else {
		value retv = { .i_b_u = 0 - x.i_b_u };
		return retv;
	}
}

value fun_ignore(value cls, value x, value k) {
	value _retv = { .i_b_u = 0 };
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_alt_ignore(value cls, value x) {
	value retv = { .i_b_u = 0 };
	return retv;
}

#elif defined(CAST) || defined(STATIC)
value fun_print_int(value cls, value v) {
	value retv;
	printf("%ld", v.i_b_u);
	retv.i_b_u = 0;
	return retv;
}

value fun_print_bool(value cls, value v) {
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

value fun_print_newline(value cls, value v) {
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

value fun_read_int(value cls, value v) {
	value retv;
	int64_t i = v.i_b_u;
	if (i == 0) {
		if (scanf("%ld", &retv.i_b_u) != 1) {
		    printf("Error: Input format error or EOF.");
		    exit(1);
		}	
	} else {
		printf("error:not unit value is applied to read_int");
		exit(1);
	}
	return retv;
}

value fun_not_ml(value cls, value b) {
	if(b.i_b_u == 1) {
		value retv = { .i_b_u = 0 };
		return retv;
	} else {
		value retv = { .i_b_u = 1 };
		return retv;
	}
}

value fun_succ(value cls, value x) {
	value retv = { .i_b_u = x.i_b_u + 1 };
	return retv;
}

value fun_prec(value cls, value x) {
	value retv = { .i_b_u = x.i_b_u - 1 };
	return retv;
}

value fun_min_x(value cls, value y) {
	value x = (value){ .i_b_u = (uintptr_t)cls.f->env[0] };
	if(x.i_b_u < y.i_b_u) {
		return x;
	} else {
		return y;
	}
}

value fun_min(value cls, value x) {
	value retv;
	retv.f = (fun*)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1);
	retv.f->funcM = fun_min_x;
	retv.f->env[0] = (void*)x.i_b_u;
	return retv;
}

value fun_max_x(value cls, value y) {
	value x = (value){ .i_b_u = (uintptr_t)cls.f->env[0] };
	if(x.i_b_u > y.i_b_u) {
		return x;
	} else {
		return y;
	}
}

value fun_max(value cls, value x) {
	value retv;
	retv.f = (fun*)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1);
	retv.f->funcM = fun_max_x;
	retv.f->env[0] = (void*)x.i_b_u;
	return retv;
}

value fun_abs_ml(value cls, value x) {
	if(x.i_b_u >= 0) {
		return x;
	} else {
		value retv = { .i_b_u = 0 - x.i_b_u };
		return retv;
	}
}

value fun_ignore(value cls, value x) {
	value retv = { .i_b_u = 0 };
	return retv;
}

#else
value fun_print_int(value cls, value v, value w) {
	value retv;
	printf("%ld", v.i_b_u);
	retv.i_b_u = 0;
	return coerce(retv, w.s);
}

value fun_print_bool(value cls, value v, value w) {
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

value fun_print_newline(value cls, value v, value w) {
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

value fun_read_int(value cls, value v, value w) {
	value retv;
	int64_t i = v.i_b_u;
	if (i == 0) {
		if (scanf("%ld", &retv.i_b_u) != 1) {
		    printf("Error: Input format error or EOF.");
		    exit(1);
		}
	} else {
		printf("error:not unit value is applied to read_int");
		exit(1);
	}
	return coerce(retv, w.s);
}

value fun_not_ml(value cls, value b, value k) {
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

value fun_succ(value cls, value x, value k) {
	value _retv = { .i_b_u = x.i_b_u + 1 };
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_prec(value cls, value x, value k) {
	value _retv = { .i_b_u = x.i_b_u - 1 };
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_min_x(value cls, value y, value k) {
	value x = (value){ .i_b_u = (uintptr_t)cls.f->env[0] };
	if(x.i_b_u < y.i_b_u) {
		value retv = coerce(x, k.s);
		return retv;
	} else {
		value retv = coerce(y, k.s);
		return retv;
	}
}

value fun_min(value cls, value x, value k) {
	value _retv;
	_retv.f = (fun*)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1);
	_retv.f->funcD = fun_min_x;
	_retv.f->env[0] = (void*)x.i_b_u;
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_max_x(value cls, value y, value k) {
	value x = (value){ .i_b_u = (uintptr_t)cls.f->env[0] };
	if(x.i_b_u > y.i_b_u) {
		value retv = coerce(x, k.s);
		return retv;
	} else {
		value retv = coerce(y, k.s);
		return retv;
	}
}

value fun_max(value cls, value x, value k) {
	value _retv;
	_retv.f = (fun*)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1);
	_retv.f->funcD = fun_max_x;
	_retv.f->env[0] = (void*)x.i_b_u;
	value retv = coerce(_retv, k.s);
	return retv;
}

value fun_abs_ml(value cls, value x, value k) {
	if(x.i_b_u >= 0) {
		value retv = coerce(x, k.s);
		return retv;
	} else {
		value _retv = { .i_b_u = 0 - x.i_b_u };
		value retv = coerce(_retv, k.s);
		return retv;
	}
}

value fun_ignore(value cls, value x, value k) {
	value _retv = { .i_b_u = 0 };
	value retv = coerce(_retv, k.s);
	return retv;
}
#endif

#ifdef ALT
#define INIT(func, func_alt) \
    { .funcD = (func), .funcM = (func_alt) }
#elif defined(CAST) || defined(STATIC)
#define INIT(func) \
    { .funcM = (func) }
#else
#define INIT(func) \
    { .funcD = (func) }
#endif

#ifdef ALT
static fun f_print_int     = INIT(fun_print_int,     fun_alt_print_int);
static fun f_print_bool    = INIT(fun_print_bool,    fun_alt_print_bool);
static fun f_print_newline = INIT(fun_print_newline, fun_alt_print_newline);
static fun f_read_int      = INIT(fun_read_int,      fun_alt_read_int);
static fun f_not_ml        = INIT(fun_not_ml,        fun_alt_not_ml);
static fun f_succ          = INIT(fun_succ,          fun_alt_succ);
static fun f_prec          = INIT(fun_prec,          fun_alt_prec);
static fun f_min           = INIT(fun_min,           fun_alt_min);
static fun f_max           = INIT(fun_max,           fun_alt_max);
static fun f_abs_ml        = INIT(fun_abs_ml,        fun_alt_abs_ml);
static fun f_ignore        = INIT(fun_ignore,        fun_alt_ignore);
#else
static fun f_print_int     = INIT(fun_print_int);
static fun f_print_bool    = INIT(fun_print_bool);
static fun f_print_newline = INIT(fun_print_newline);
static fun f_read_int      = INIT(fun_read_int);
static fun f_not_ml        = INIT(fun_not_ml);
static fun f_succ          = INIT(fun_succ);
static fun f_prec          = INIT(fun_prec);
static fun f_min           = INIT(fun_min);
static fun f_max           = INIT(fun_max);
static fun f_abs_ml        = INIT(fun_abs_ml);
static fun f_ignore        = INIT(fun_ignore);
#endif

value max_int = { .i_b_u = INT64_MAX };
value min_int = { .i_b_u = INT64_MIN };
value print_int = { .f = &f_print_int };
value print_bool = { .f = &f_print_bool };
value print_newline = { .f = &f_print_newline };
value read_int = { .f = &f_read_int };
value not_ml = { .f = &f_not_ml };
value succ = { .f = &f_succ };
value prec = { .f = &f_prec };
value min = { .f = &f_min };
value max = { .f = &f_max };
value abs_ml = { .f = &f_abs_ml };
value ignore = { .f = &f_ignore };