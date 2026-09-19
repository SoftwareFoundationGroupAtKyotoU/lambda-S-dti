#include <math.h>

#include "runtime.h"
#include "stdlib_math.h"

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

static inline value _core_sqrt_ml(value cls, value v) {
	(void)cls;
	return of_double(sqrt(to_double(v)));
}
DEF_UNARY(sqrt_ml, _core_sqrt_ml)

static inline value _core_exp_ml(value cls, value v) {
	(void)cls;
	return of_double(exp(to_double(v)));
}
DEF_UNARY(exp_ml, _core_exp_ml)

static inline value _core_log_ml(value cls, value v) {
	(void)cls;
	return of_double(log(to_double(v)));
}
DEF_UNARY(log_ml, _core_log_ml)

static inline value _core_round_ml(value cls, value v) {
	(void)cls;
	return of_double(round(to_double(v)));
}
DEF_UNARY(round_ml, _core_round_ml)

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

static inline value _core_fmin_ml_x(value cls, value y) {
	value x = (value)((fun*)cls)->env[0];
	if (to_double(x) < to_double(y)) {
		return x;
	} else {
		return y;
	}
}
DEF_UNARY(fmin_ml_x, _core_fmin_ml_x)
DEF_BINARY(fmin_ml)

static inline value _core_fmax_ml_x(value cls, value y) {
	value x = (value)((fun*)cls)->env[0];
	if (to_double(x) > to_double(y)) {
		return x;
	} else {
		return y;
	}
}
DEF_UNARY(fmax_ml_x, _core_fmax_ml_x)
DEF_BINARY(fmax_ml)

STDLIB_MATH_UNARY_LIST(STDLIB_TABLE)
STDLIB_MATH_BINARY_LIST(STDLIB_TABLE)

STDLIB_MATH_UNARY_LIST(STDLIB_EXPORT)
STDLIB_MATH_BINARY_LIST(STDLIB_EXPORT)

value max_int = INT64_MAX >> 3;
value min_int = INT64_MIN >> 3;
