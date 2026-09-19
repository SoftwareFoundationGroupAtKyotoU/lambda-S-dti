#ifndef STDLIB_MATH_H
#define STDLIB_MATH_H

#include "types.h"
#include "stdlib_macros.h"

#define STDLIB_MATH_CONSTANT_LIST(X) \
  X(max_int) X(min_int)
#define STDLIB_MATH_UNARY_LIST(X) \
  X(succ) X(prec) X(abs_ml) X(sqrt_ml) X(exp_ml) X(log_ml) X(round_ml)
#define STDLIB_MATH_BINARY_LIST(X) \
  X(min) X(max) X(fmin_ml) X(fmax_ml)

STDLIB_MATH_UNARY_LIST(STDLIB_DECL_UNARY)
STDLIB_MATH_BINARY_LIST(STDLIB_DECL_BINARY)

STDLIB_MATH_CONSTANT_LIST(STDLIB_DECL_EXTERN)
STDLIB_MATH_UNARY_LIST(STDLIB_DECL_EXTERN)
STDLIB_MATH_BINARY_LIST(STDLIB_DECL_EXTERN)

#endif
