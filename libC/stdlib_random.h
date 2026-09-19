#ifndef STDLIB_RANDOM_H
#define STDLIB_RANDOM_H

#include "types.h"
#include "stdlib_macros.h"

#define STDLIB_RANDOM_UNARY_LIST(X) \
  X(random_init) X(random_int) X(random_float)

STDLIB_RANDOM_UNARY_LIST(STDLIB_DECL_UNARY)

STDLIB_RANDOM_UNARY_LIST(STDLIB_DECL_EXTERN)

#endif
