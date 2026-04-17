#ifndef LST_H
#define LST_H

#include "types.h"

typedef struct lst {
	// 1ワード目
    union {
        value h;        // unwrap の場合
        lst *w;         // wrap の場合
    };

	// 2ワード目
    #if defined(EAGER) || defined(STATIC)
    // EAGER / STATIC: キャストなし
    value t;

    #elif defined(CAST)
    union {
        value t;              // unwrap の場合
        struct {
            uintptr_t u1_tag; // ty *u1 のポインタ + 下位1bit(wrap)
            uintptr_t u2_p;   // ty *u2 のポインタ + 下位1bit(polarity)
            uint32_t rid;
        } wrap_info;
    };

    #else
    union {
        value t;              // unwrap の場合
        uintptr_t c_tag;      // coercionポインタ ＋ 下位1bitフラグ(wrap)
    };
    #endif
} lst;

#if !defined(EAGER) && !defined(STATIC)
int is_NULL(lst*);

value hd(lst*);

value tl(lst*);
#endif

#endif