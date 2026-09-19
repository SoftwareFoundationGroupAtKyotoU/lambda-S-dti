#ifndef STR_H
#define STR_H

#include "types.h"

/* runtime helper backing the `^` (SConcat) binop -- not a user-visible stdlib
 * binding, so it bypasses the fun_ / closure machinery entirely. */
value string_concat(value, value);

#endif
