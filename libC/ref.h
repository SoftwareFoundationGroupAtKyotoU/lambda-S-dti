#ifndef REF_H
#define REF_H

#include "types.h"

#ifdef STATIC
typedef value *ref;
#elif defined(MONOTONIC)
typedef struct ref {
	value v;
	ty *u;
} ref;
#else
typedef struct ref {
	// 1ワード目
    union {
        value v;        // unwrap の場合
        ref *w;         // wrap の場合
    };

	// 2ワード目
    #if defined(CAST)
    uintptr_t u1_tag; // ty *u1 のポインタ + 下位1bit(wrap)
    uintptr_t u2_p;   // ty *u2 のポインタ + 下位1bit(polarity)
    uint32_t rid;

    #else
    uintptr_t c_tag;      // coercionポインタ ＋ 下位1bitフラグ(wrap)
	#endif
} ref;

value deref(ref*);

void subst(ref*, value);
#endif

#endif