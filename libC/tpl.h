#ifndef TPL_H
#define TPL_H

#include "types.h"

typedef struct tpl_header {
    uint16_t size;
    #if !defined(EAGER) && !defined(STATIC)
    uint8_t wrap : 1;
    #ifdef CAST
    uint8_t polarity : 1;
    uint32_t rid;
    #endif
	#endif
} tpl_header;

typedef struct tpl_raw {
    tpl_header hdr;
    value fields[]; // tupleの要素
} tpl_raw;

#if !defined(EAGER) && !defined(STATIC)
typedef struct tpl_wrap {
    tpl_header hdr;
	tpl_header *w; // wrapの内側のtuple
    
	#ifdef CAST
    ty **u1;
    ty **u2;
    #else
    crc **cs;
    #endif
} tpl_wrap;
#endif

#if defined(EAGER) || defined(STATIC)
typedef tpl_raw tpl;
#else
typedef tpl_header tpl;
#endif

#if !defined(EAGER) && !defined(STATIC)

// I2: the unwrapped case is a single load, so keep it inline at every
// projection site; only wrapped (lazily coerced) tuples go out of line.
value tget_wrapped(tpl*, uint16_t i);

static inline value tget(tpl *t, uint16_t i) {
    if (__builtin_expect(t->wrap, 0)) {
        return tget_wrapped(t, i);
    }
    return ((tpl_raw*)t)->fields[i];
}

#endif

#endif
