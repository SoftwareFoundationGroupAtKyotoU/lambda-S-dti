#ifndef TPL_H
#define TPL_H

#include "types.h"

typedef struct tpl_header {
    uint16_t arity;
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
    crc *c;
    #endif
} tpl_wrap;
#endif

#if defined(EAGER) || defined(STATIC)
typedef tpl_raw tpl;
#else
typedef tpl_header tpl;
#endif

#if !defined(EAGER) && !defined(STATIC)

value tget(tpl*, uint16_t i);

#endif

#endif
