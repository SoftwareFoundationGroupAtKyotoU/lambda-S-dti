#ifndef STDLIB_ARRAY_H
#define STDLIB_ARRAY_H

#include "types.h"
#include "stdlib_macros.h"

// NOTE: array_iteri is not yet implemented in C (it needs to call back into
// a user closure argument); it remains interpreter-only (ITGL, c_backing =
// CUnimplemented) for now.
#define STDLIB_ARRAY_UNARY_LIST(X) \
  X(array_to_list)

STDLIB_ARRAY_UNARY_LIST(STDLIB_DECL_UNARY)

STDLIB_ARRAY_UNARY_LIST(STDLIB_DECL_EXTERN)

#endif
