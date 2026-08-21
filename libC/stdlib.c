#include "runtime.h"
#include "stdlib.h"

#ifdef ALT
#define DEF_UNARY(fname, core) \
  value fun_##fname(value cls, value v, value w) { return toplevel_coerce(core(cls, v), (crc*)w); } \
  value fun_alt_##fname(value cls, value v) { return core(cls, v); }
#define DEF_BINARY(fname) \
  value fun_alt_##fname(value cls, value x) { \
    value retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1); \
    ((fun*)retv)->funcM = fun_alt_##fname##_x; \
    ((fun*)retv)->funcD = fun_##fname##_x; \
    ((fun*)retv)->env[0] = (void*)x; \
    return retv; \
  } \
  value fun_##fname(value cls, value x, value w) { \
    value retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1); \
    ((fun*)retv)->funcM = fun_alt_##fname##_x; \
    ((fun*)retv)->funcD = fun_##fname##_x; \
    ((fun*)retv)->env[0] = (void*)x; \
    return toplevel_coerce(retv, (crc*)w); \
  }
#elif defined(CAST) || defined(STATIC)
#define DEF_UNARY(fname, core) \
  value fun_##fname(value cls, value v) { return core(cls, v); }
#define DEF_BINARY(fname) \
  value fun_##fname(value cls, value x) { \
    value retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1); \
    ((fun*)retv)->funcM = fun_##fname##_x; \
    ((fun*)retv)->env[0] = (void*)x; \
    return retv; \
  }
#else
#define DEF_UNARY(fname, core) \
  value fun_##fname(value cls, value v, value w) { return toplevel_coerce(core(cls, v), (crc*)w); }
#define DEF_BINARY(fname) \
  value fun_##fname(value cls, value x, value w) { \
    value retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 1); \
    ((fun*)retv)->funcD = fun_##fname##_x; \
    ((fun*)retv)->env[0] = (void*)x; \
    return toplevel_coerce(retv, (crc*)w); \
  }
#endif

/* ---- core implementations ---- */

static inline value _core_print_int(value cls, value v) {
	(void)cls;
	printf("%ld", v);
	return 0;
}
DEF_UNARY(print_int, _core_print_int)

static inline value _core_print_bool(value cls, value v) {
	(void)cls;
	int64_t i = v;
	if (i == 1) {
		printf("true");
	} else if (i == 0) {
		printf("false");
	} else {
		printf("error:not boolean value is applied to print_bool");
		exit(1);
	}
	return 0;
}
DEF_UNARY(print_bool, _core_print_bool)

static inline value _core_print_newline(value cls, value v) {
	(void)cls;
	int64_t i = v;
	if (i == 0) {
		printf("\n");
	} else {
		printf("error:not unit value is applied to print_newline");
		exit(1);
	}
	return 0;
}
DEF_UNARY(print_newline, _core_print_newline)

static inline value _core_print_float(value cls, value v) {
	(void)cls;
	printf("%lf", to_double(v));
	return 0;
}
DEF_UNARY(print_float, _core_print_float)

static inline value _core_read_int(value cls, value v) {
	(void)cls;
	value retv;
	int64_t i = v;
	if (i == 0) {
		if (scanf("%ld", &retv) != 1) {
			printf("Error: Input format error or EOF.");
			exit(1);
		}
	} else {
		printf("error:not unit value is applied to read_int");
		exit(1);
	}
	return retv;
}
DEF_UNARY(read_int, _core_read_int)

static inline value _core_read_float(value cls, value v) {
	(void)cls;
	double retv;
	int64_t i = v;
	if (i == 0) {
		if (scanf("%lf", &retv) != 1) {
			printf("Error: Input format error or EOF.");
			exit(1);
		}
	} else {
		printf("error:not unit value is applied to read_float");
		exit(1);
	}
	return of_double(retv);
}
DEF_UNARY(read_float, _core_read_float)

static inline value _core_float_of_int(value cls, value x) {
	(void)cls;
	return of_double((double)x);
}
DEF_UNARY(float_of_int, _core_float_of_int)

static inline value _core_int_of_float(value cls, value x) {
	(void)cls;
	return (value)to_double(x);
}
DEF_UNARY(int_of_float, _core_int_of_float)

static inline value _core_not_ml(value cls, value b) {
	(void)cls;
	if (b == 1) {
		return 0;
	} else {
		return 1;
	}
}
DEF_UNARY(not_ml, _core_not_ml)

static inline value _core_succ(value cls, value x) {
	(void)cls;
	return x + 1;
}
DEF_UNARY(succ, _core_succ)

static inline value _core_prec(value cls, value x) {
	(void)cls;
	return x - 1;
}
DEF_UNARY(prec, _core_prec)

static inline value _core_abs_ml(value cls, value x) {
	(void)cls;
	if (x >= 0) {
		return x;
	} else {
		return 0 - x;
	}
}
DEF_UNARY(abs_ml, _core_abs_ml)

static inline value _core_ignore(value cls, value x) {
	(void)cls;
	(void)x;
	return 0;
}
DEF_UNARY(ignore, _core_ignore)

static inline value _core_min_x(value cls, value y) {
	value x = (value)((fun*)cls)->env[0];
	if (x < y) {
		return x;
	} else {
		return y;
	}
}
DEF_UNARY(min_x, _core_min_x)
DEF_BINARY(min)

static value _core_max_x(value cls, value y) {
	value x = (value)((fun*)cls)->env[0];
	if (x > y) {
		return x;
	} else {
		return y;
	}
}
DEF_UNARY(max_x, _core_max_x)
DEF_BINARY(max)

#undef DEF_UNARY
#undef DEF_BINARY

#ifdef ALT
#define STDLIB_TABLE(n) static fun f_##n = { .funcD = fun_##n, .funcM = fun_alt_##n };
#elif defined(CAST) || defined(STATIC)
#define STDLIB_TABLE(n) static fun f_##n = { .funcM = fun_##n };
#else
#define STDLIB_TABLE(n) static fun f_##n = { .funcD = fun_##n };
#endif

STDLIB_UNARY_LIST(STDLIB_TABLE)
STDLIB_BINARY_LIST(STDLIB_TABLE)
#undef STDLIB_TABLE

#define STDLIB_EXPORT(n) value n = (value)&f_##n;
STDLIB_UNARY_LIST(STDLIB_EXPORT)
STDLIB_BINARY_LIST(STDLIB_EXPORT)
#undef STDLIB_EXPORT

value max_int = INT64_MAX >> 3;
value min_int = INT64_MIN >> 3;