#ifndef ARRAY_H
#define ARRAY_H

#include "types.h"

#if defined(MONOTONIC) || defined(STATIC)

typedef struct arr_raw {
    uint32_t length;
    #ifdef MONOTONIC
    ty *u;
    #endif
    value vs[];
} arr_raw;

#else

typedef struct arr_header {
    uint8_t wrap : 1;
    #ifdef CAST
    uint8_t polarity : 1;
    uint32_t rid;
    #endif
} arr_header;

typedef struct arr_raw {
    arr_header hdr;
    uint32_t length;
    value vs[];
} arr_raw;

typedef struct arr_wrap {
    arr_header hdr;
    arr_header *w; // wrap の内側
    #ifdef CAST
    ty *u1; // wrap 前 (内側) の要素型
    ty *u2; // wrap 後 (外側) の要素型
    #else
    crc *c1; // 読み出し (aget) 用 coercion
    crc *c2; // 書き込み (aset) 用 coercion
    #endif
} arr_wrap;

#endif

#if defined(MONOTONIC) || defined(STATIC)
typedef arr_raw arr;
#else
typedef arr_header arr;
#endif

// I9: array bounds check (direct monotonic/static accesses in toC.ml and get/put in arr.c), enabled with -D BOUNDS
#ifdef BOUNDS
#include <stdio.h>
#include <stdlib.h>
#define BOUNDS_CHECK(a, i) do { \
    if ((uint64_t)(i) >= (uint64_t)((arr_raw*)(a))->length) { \
        printf("index out of bound %ld\n", (long)(i)); exit(1); \
    } } while (0)
// Array.make の長さは uint32_t の length に入る。ここで n を範囲内に限ると、clang が
// length == n を知り、i < n で回るループの BOUNDS_CHECK を消して最適化（ベクトル化）できる
#define ARRAY_SIZE_CHECK(n) do { \
    if ((uint64_t)(n) > UINT32_MAX) { \
        printf("invalid array size %ld\n", (long)(n)); exit(1); \
    } } while (0)
#else
#define BOUNDS_CHECK(a, i) ((void)0)
#define ARRAY_SIZE_CHECK(n) ((void)0)
#endif

#if !defined(MONOTONIC) && !defined(STATIC)
value get(arr*, uint32_t);
void put(arr*, uint32_t, value);
value length(arr*);
#endif

#endif
