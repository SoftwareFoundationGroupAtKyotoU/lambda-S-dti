#ifndef STDLIB_LIST_H
#define STDLIB_LIST_H

#include "types.h"
#include "stdlib_macros.h"

// NOTE: list_map/list_fold_left/list_init/list_mapi/list_iteri are not yet
// implemented in C (they need to call back into a user closure argument);
// they remain interpreter-only (ITGL, c_backing = CUnimplemented) for now.
#define STDLIB_LIST_UNARY_LIST(X) \
  X(list_length)

STDLIB_LIST_UNARY_LIST(STDLIB_DECL_UNARY)

STDLIB_LIST_UNARY_LIST(STDLIB_DECL_EXTERN)

#endif
