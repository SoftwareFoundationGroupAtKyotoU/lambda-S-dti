#ifndef STDLIB_BASIC_H
#define STDLIB_BASIC_H

#include "types.h"
#include "stdlib_macros.h"

#define STDLIB_BASIC_UNARY_LIST(X) \
  X(float_of_int) X(int_of_float) X(char_of_int) X(int_of_char) X(not_ml) X(ignore)

STDLIB_BASIC_UNARY_LIST(STDLIB_DECL_UNARY)

STDLIB_BASIC_UNARY_LIST(STDLIB_DECL_EXTERN)

#endif
