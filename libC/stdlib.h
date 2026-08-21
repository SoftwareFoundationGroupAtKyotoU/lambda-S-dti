#ifndef STDLIB_H
#define STDLIB_H

#include "types.h"

/* stdlib value name list */
// for constant
#define STDLIB_CONSTANT_LIST(X) \
  X(max_int) X(min_int)
// for unary function
#define STDLIB_UNARY_LIST(X) \
  X(print_int) X(print_bool) X(print_newline) X(print_float) \
  X(read_int) X(read_float)   X(float_of_int) X(int_of_float) \
  X(ignore) X(abs_ml) X(prec) X(succ) X(not_ml)
// for binary function
#define STDLIB_BINARY_LIST(X) \
   X(max) X(min)

/* function declaration (e.g. print_int) */
#ifdef ALT
// for ALT
// value fun_print_int(value, value, value);
// value fun_alt_print_int(value, value);
#define STDLIB_DECL_UNARY(n) \
  value fun_##n(value, value, value); \
  value fun_alt_##n(value, value);
#elif defined(CAST) || defined(STATIC)
// for CAST or STATIC
// value fun_print_int(value, value);
#define STDLIB_DECL_UNARY(n) \
  value fun_##n(value, value);
#else
// otherwise
// value fun_print_int(value, value, value);
#define STDLIB_DECL_UNARY(n) \
  value fun_##n(value, value, value);
#endif

// for binary function, preparing one more function applied only one argument (e.g. min)
// value fun_min(value, value, value);
// value fun_min_x(value, value, value);
#define STDLIB_DECL_BINARY(n) \
  STDLIB_DECL_UNARY(n) \
  STDLIB_DECL_UNARY(n##_x)

// generate function declarations
STDLIB_UNARY_LIST(STDLIB_DECL_UNARY)
STDLIB_BINARY_LIST(STDLIB_DECL_BINARY)

#undef STDLIB_DECL_UNARY
#undef STDLIB_DECL_BINARY

/* extern values (e.g. print_int) */
// extern value print_int;
#define STDLIB_DECL_EXTERN(n) extern value n;
STDLIB_CONSTANT_LIST(STDLIB_DECL_EXTERN)
STDLIB_UNARY_LIST(STDLIB_DECL_EXTERN)
STDLIB_BINARY_LIST(STDLIB_DECL_EXTERN)
#undef STDLIB_DECL_EXTERN

#endif