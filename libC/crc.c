#if !defined(CAST) && !defined(STATIC)

#ifdef HASH
#define CRC_HASH_INIT_SIZE 1024  // intern_table の初期サイズ（2 の冪）。負荷率 1/2 を超えたら倍にする
#define CACHE_SIZE 65536
// compose memo（compose_cache）は HASH のとき既定で有効。-D NO_COMPOSE_CACHE で無効にできる
#ifndef NO_COMPOSE_CACHE
#define COMPOSE_CACHE
#endif
#endif //HASH

#include <stdio.h>
#include <stdlib.h>
#include <gc.h>

#include "crc.h"
#include "capp.h"
#include "ty.h"

crc crc_id = { .crckind = C_ID, .has_proj = 0, .has_inj = 0, .has_tv = 0 };
crc crc_inj_INT = { .crckind = C_ID, .has_inj = 1, .crcdat = { .id.g = G_INT } };
crc crc_inj_BOOL = { .crckind = C_ID, .has_inj = 1, .crcdat = { .id.g = G_BOOL } };
crc crc_inj_UNIT = { .crckind = C_ID, .has_inj = 1, .crcdat = { .id.g = G_UNIT } };
crc crc_inj_FLOAT = { .crckind = C_ID, .has_inj = 1, .crcdat = { .id.g = G_FLOAT } };
crc crc_inj_CHAR = { .crckind = C_ID, .has_inj = 1, .crcdat = { .id.g = G_CHAR } };
crc crc_inj_STRING = { .crckind = C_ID, .has_inj = 1, .crcdat = { .id.g = G_STRING } };
crc crc_inj_FN = { .crckind = C_ID, .has_inj = 1, .crcdat = { .id.g = G_FN } };
crc crc_inj_LI = { .crckind = C_ID, .has_inj = 1, .crcdat = { .id.g = G_LI } };
#ifdef MONOTONIC
crc crc_inj_RF = { .crckind = C_REF, .has_inj = 1, .crcdat = { .mref_crc = &tydyn } };
crc crc_inj_AR = { .crckind = C_ARRAY, .has_inj = 1, .crcdat = { .marray_crc = &tydyn } };
#else
crc crc_inj_RF = { .crckind = C_ID, .has_inj = 1, .crcdat = { .id.g = G_RF } };
crc crc_inj_AR = { .crckind = C_ID, .has_inj = 1, .crcdat = { .id.g = G_AR } };
#endif

static inline crc* create_new_crc(crc* candidate) {
	#ifdef PROFILE
	new_crc_num++;
	#endif
	crc *new_c = (crc*)GC_MALLOC(sizeof(crc));
    *new_c = *candidate;
	return new_c;
}

#ifdef HASH
#include <string.h>

static crc **static_crcs = NULL;
static int static_crc_n = 0;

void set_static_crcs(crc **arr, int n) {
    static_crcs = arr;
    static_crc_n = n;
}

// intern_table は GC_MALLOC で確保し、この static 変数を root として GC に辿らせる。
// 以前は calloc した固定長（131072 エントリ）を GC_add_roots していたため、中身が少なくても
// GC のたびに 1MB 全体がスキャンされ、埋まると線形探索に劣化していた。
static crc **intern_table = NULL;
static uint32_t intern_size = 0;   // 2 の冪
static uint32_t intern_count = 0;

// hash_crc の値はポインタ由来でも下位ビットが偏るので、マスクで添字を取る前に混ぜる
static inline uint32_t mix32(uint32_t h) {
    h ^= h >> 16;
    h *= 0x45d9f3bu;
    h ^= h >> 16;
    return h;
}

static uint32_t hash_crc(const crc *c) {
    uint32_t h = c->crckind;
    h = (h * 31) + ((c->has_proj << 3) | (c->has_inj << 2) | (c->has_tv << 1) | c->p_proj);
    h = (h * 31) + c->rid_proj;

    switch (c->crckind) {
		case C_ID:
			h = (h * 31) + c->crcdat.id.g;
			h = (h * 31) + c->crcdat.id.size;
			break;
        case C_FUN:
            h = (h * 31) + (uintptr_t)c->crcdat.fun_crc.c1;
            h = (h * 31) + (uintptr_t)c->crcdat.fun_crc.c2;
            break;
        case C_LIST:
            h = (h * 31) + (uintptr_t)c->crcdat.lst_crc;
            break;
        case C_TUPLE:
            h = (h * 31) + c->crcdat.tpl_crc.size;
            for (int i = 0; i < c->crcdat.tpl_crc.size; i++) {
                h = (h * 31) + (uintptr_t)c->crcdat.tpl_crc.crcs[i];
            }
            break;
		case C_REF:
			#ifdef MONOTONIC
			h = (h * 31) + (uintptr_t)c->crcdat.mref_crc;
			break;
			#else
            h = (h * 31) + (uintptr_t)c->crcdat.ref_crc.c1;
            h = (h * 31) + (uintptr_t)c->crcdat.ref_crc.c2;
            break;
			#endif
		case C_ARRAY:
			#ifdef MONOTONIC
			h = (h * 31) + (uintptr_t)c->crcdat.marray_crc;
			break;
			#else
            h = (h * 31) + (uintptr_t)c->crcdat.array_crc.c1;
            h = (h * 31) + (uintptr_t)c->crcdat.array_crc.c2;
            break;
			#endif
		case C_TV:
			h = (h * 31) + c->crcdat.tv.rid_inj;
            h = (h * 31) + ((uintptr_t)c->crcdat.tv.tv_ptr | c->crcdat.tv.p_inj);
            break;
		case C_BOT: 
		    h = (h * 31) + (uintptr_t)c->crcdat.bot.g + c->crcdat.bot.size + c->crcdat.bot.kind_bot + c->crcdat.bot.p_bot;
			h = (h * 31) + c->crcdat.bot.rid_bot;
			break;
    }

    return h;
}

static int eq_crc(const crc *a, const crc *b) {
    if (a == b) return 1;
    
    if (a->crckind  != b->crckind  ||
		a->has_proj != b->has_proj ||
		a->has_inj  != b->has_inj  ||
		a->has_tv   != b->has_tv   ||
        a->p_proj   != b->p_proj   ||
        a->rid_proj != b->rid_proj
	) {
        return 0;
    }

    switch (a->crckind) {
		case C_ID:
			return a->crcdat.id.g    == b->crcdat.id.g &&
		           a->crcdat.id.size == b->crcdat.id.size;
        case C_FUN:
            return a->crcdat.fun_crc.c1 == b->crcdat.fun_crc.c1 &&
                   a->crcdat.fun_crc.c2 == b->crcdat.fun_crc.c2;
        case C_LIST:
            return a->crcdat.lst_crc == b->crcdat.lst_crc;
        case C_TUPLE:
            if (a->crcdat.tpl_crc.size != b->crcdat.tpl_crc.size) return 0;
            for (int i = 0; i < a->crcdat.tpl_crc.size; i++) {
                if (a->crcdat.tpl_crc.crcs[i] != b->crcdat.tpl_crc.crcs[i]) return 0;
            }
            return 1;
		case C_REF:
			#ifdef MONOTONIC
            return a->crcdat.mref_crc == b->crcdat.mref_crc;
			#else
            return a->crcdat.ref_crc.c1 == b->crcdat.ref_crc.c1 &&
                   a->crcdat.ref_crc.c2 == b->crcdat.ref_crc.c2;
        	#endif
		case C_ARRAY:
			#ifdef MONOTONIC
            return a->crcdat.marray_crc == b->crcdat.marray_crc;
			#else
            return a->crcdat.array_crc.c1 == b->crcdat.array_crc.c1 &&
                   a->crcdat.array_crc.c2 == b->crcdat.array_crc.c2;
        	#endif
        case C_TV:
            return a->crcdat.tv.rid_inj == b->crcdat.tv.rid_inj &&
                   a->crcdat.tv.p_inj   == b->crcdat.tv.p_inj   &&
                   a->crcdat.tv.tv_ptr  == b->crcdat.tv.tv_ptr;
		case C_BOT:
            return a->crcdat.bot.rid_bot  == b->crcdat.bot.rid_bot  &&
                   a->crcdat.bot.p_bot    == b->crcdat.bot.p_bot    &&
                   a->crcdat.bot.kind_bot == b->crcdat.bot.kind_bot &&
                   a->crcdat.bot.g        == b->crcdat.bot.g        &&
                   a->crcdat.bot.size     == b->crcdat.bot.size;
    }
}

static void intern_table_alloc(uint32_t size) {
    intern_table = (crc**)GC_MALLOC(sizeof(crc*) * size);
    if (!intern_table) { printf("Fatal: intern_table allocation failed\n"); exit(1); }
    intern_size = size;
    intern_count = 0;
}

// c を（同一ポインタが既に入っていなければ）挿入する。伸長はしない
static void intern_table_put(crc *c) {
    uint32_t idx = mix32(hash_crc(c)) & (intern_size - 1);
    while (intern_table[idx] != NULL) {
        if (intern_table[idx] == c) return;
        idx = (idx + 1) & (intern_size - 1);
    }
    intern_table[idx] = c;
    intern_count++;
}

static void intern_table_grow(void) {
    crc **old = intern_table;
    uint32_t old_size = intern_size;
    intern_table_alloc(old_size * 2);
    for (uint32_t i = 0; i < old_size; i++) {
        if (old[i]) intern_table_put(old[i]);
    }
}

static void ensure_intern_table(void) {
    if (intern_table) return;
    intern_table_alloc(CRC_HASH_INIT_SIZE);
    for (int i = 0; i < static_crc_n; i++) {
        intern_table_put(static_crcs[i]);
        if (intern_count * 2 > intern_size) intern_table_grow();
    }
}

static crc* intern_crc(crc *candidate) {
    if (!intern_table) {
        for (int i = 0; i < static_crc_n; i++) {
            if (eq_crc(static_crcs[i], candidate)) {
                #ifdef PROFILE
                alloc_hash++;
                #endif
                return static_crcs[i];
            }
        }
        ensure_intern_table();
    }

    uint32_t idx = mix32(hash_crc(candidate)) & (intern_size - 1);
    while (intern_table[idx] != NULL) {
        if (eq_crc(intern_table[idx], candidate)) {
			#ifdef PROFILE
			alloc_hash++;
			#endif
            return intern_table[idx];
        }
        idx = (idx + 1) & (intern_size - 1);
    }

    crc *new_c = create_new_crc(candidate);
    intern_table[idx] = new_c;
    if (++intern_count * 2 > intern_size) intern_table_grow();
    return new_c;
}

#ifdef COMPOSE_CACHE
typedef struct {
    crc *c1;
    crc *c2;
    crc *result;
} compose_cache_entry;

static compose_cache_entry *compose_cache = NULL;

static inline void ensure_compose_cache(void) {
    if (compose_cache) return;
    // calloc した領域は GC のスキャン対象外（GC_add_roots しない）。GC のたびに 1.5MB を
    // スキャンするコストを避けるため、表の中のポインタは表以外からも必ず生かされていることを
    // 不変条件とする:
    //   - c1/c2 は has_tv == 0 のときだけ登録する（compose_body）。HASH モードで has_tv == 0 の crc は
    //     必ず intern_crc を通る（crc を作るのは create_new_crc だけ）か static な crc。
    //   - 結果も has_tv == 0 のときだけ登録するので、同じく intern 済みか static。
    //   - intern_table は中身を clear_crc_caches まで強参照で持ち、clear_crc_caches は両表を同時に捨てる。
    // 以前、結果が intern されていない crc（has_tv = 1 の mref）を root 登録せずに保持して、回収後の
    // アドレス再利用でダングリングポインタになったことがある。has_tv == 0 の crc を create_new_crc 以外の
    // 経路で作るコードを足すと、この不変条件が壊れるので注意。
    compose_cache = (compose_cache_entry*)calloc(CACHE_SIZE, sizeof(compose_cache_entry));
    if (!compose_cache) { printf("Fatal: compose_cache allocation failed\n"); exit(1); }
}
#endif //COMPOSE_CACHE

void clear_crc_caches() {
    // 次の intern で static crc の登録からやり直す（旧表は GC に回収される）
    intern_table = NULL;
    intern_size = 0;
    intern_count = 0;
	#ifdef COMPOSE_CACHE
    if (compose_cache) memset(compose_cache, 0, CACHE_SIZE * sizeof(compose_cache_entry));
	#endif
}
#endif //HASH

crc* alloc_crc(crc *candidate) {
	#ifdef PROFILE
	current_alloc++;
	#endif
	// fprintf(stderr, "TRACE alloc ");
	// trace_crc("candidate", candidate);
	// fprintf(stderr, "\n");
	if (candidate->crckind == C_TV) {
		ty *tv = candidate->crcdat.tv.tv_ptr;
		if (tv->tykind == SUBSTITUTED) {
			tv = ty_find(tv);
			candidate->crcdat.tv.tv_ptr = tv;
		}
		// 解決済みなら normalize_tv が割り当て（intern）済みの crc を返すので、そのまま返す。
		// 未解決（TYVAR）のときは normalize_tv は引数自身（toC の crctmp や new_tv の一時変数）
		// を返すので、必ず下の割り当て経路を通すこと
		if (tv->tykind != TYVAR) return normalize_tv(candidate);
	}
    #ifdef HASH
    if (candidate->has_tv) return create_new_crc(candidate);
	// crc *retc = intern_crc(candidate);
	// fprintf(stderr, "TRACE   -> ");
	// trace_crc("res", retc);
	// fprintf(stderr, "\n");
    return intern_crc(candidate);
    #else // HASH
	crc *norm = create_new_crc(candidate);
   	return norm;
    #endif // HASH
}

static inline crc *new_id(const crc *proj, const ground_ty g, const uint16_t size, const crc *inj) {
	if (proj->has_proj == 0) {
		if (inj->has_inj == 0) return &crc_id;
		switch (g) {
			case G_INT: return &crc_inj_INT;
			case G_BOOL: return &crc_inj_BOOL;
			case G_UNIT: return &crc_inj_UNIT;
			case G_FLOAT: return &crc_inj_FLOAT;
			case G_CHAR: return &crc_inj_CHAR;
			case G_STRING: return &crc_inj_STRING;
			case G_FN: return &crc_inj_FN;
			case G_LI: return &crc_inj_LI;
			case G_TP: {
				crc temp = { .crckind = C_ID, .has_inj = 1, .crcdat.id = { .g = G_TP, .size = size } };
				return alloc_crc(&temp);
			}
			case G_RF: return &crc_inj_RF;
			case G_AR: return &crc_inj_AR;
		}
	} else {
		crc temp = {
			.crckind = C_ID, .has_proj = 1, .has_inj = inj->has_inj,
			.p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
			.crcdat.id = { .g = g, .size = size }
		};
		return alloc_crc(&temp);
	}
}

static inline crc* new_fun(const crc *proj, crc *c1, crc *c2, const crc *inj) {
	crc temp = {
		.crckind = C_FUN, .has_proj = proj->has_proj, .has_inj = inj->has_inj,
		.has_tv = c1->has_tv | c2->has_tv, .p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
		.crcdat.fun_crc = { .c1 = c1, .c2 = c2 }
	};
    return alloc_crc(&temp);
}

static inline crc* new_list(const crc *proj, crc *c, const crc *inj) {
    crc temp = {
		.crckind = C_LIST, .has_proj = proj->has_proj, .has_inj = inj->has_inj,
		.has_tv = c->has_tv, .p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
		.crcdat.lst_crc = c
	};
    return alloc_crc(&temp);
}

static inline crc* new_tuple(const crc *proj, uint16_t size, crc **crcs, const crc *inj) {
    uint8_t has_tv = 0;
    for (int i = 0; i < size; i++) {
        has_tv |= crcs[i]->has_tv;
    }
	crc temp = {
		.crckind = C_TUPLE, .has_proj = proj->has_proj, .has_inj = inj->has_inj,
		.has_tv = has_tv, .p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
		.crcdat.tpl_crc = { .size = size, .crcs = crcs }
	};
    return alloc_crc(&temp);
}

#ifdef MONOTONIC
// has_tv は呼び出し側が決める。キーの型が型変数を含まないと分かっていない限り 1 を渡すこと
static inline crc* new_mref_tv(const crc *proj, ty *u, const crc *inj, uint8_t has_tv) {
    crc temp = {
		.crckind = C_REF, .has_proj = proj->has_proj, .has_inj = inj->has_inj,
		.has_tv = has_tv, .p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
		.crcdat.mref_crc = u
	};
    return alloc_crc(&temp);
}

static inline crc* new_mref(const crc *proj, ty *u, const crc *inj) {
	// キーの型が型変数を含むかは見ないので、安全側に倒して has_tv = 1 とする
	return new_mref_tv(proj, u, inj, 1);
}
#else
static inline crc* new_ref(const crc *proj, crc *c1, crc *c2, const crc *inj) {
    crc temp = {
		.crckind = C_REF, .has_proj = proj->has_proj, .has_inj = inj->has_inj,
		.has_tv = c1->has_tv | c2->has_tv, .p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
		.crcdat.ref_crc = { .c1 = c1, .c2 = c2 }
	};
    return alloc_crc(&temp);
}
#endif

#ifdef MONOTONIC
// has_tv は呼び出し側が決める。キーの型が型変数を含まないと分かっていない限り 1 を渡すこと
static inline crc* new_marray_tv(const crc *proj, ty *u, const crc *inj, uint8_t has_tv) {
    crc temp = {
		.crckind = C_ARRAY, .has_proj = proj->has_proj, .has_inj = inj->has_inj,
		.has_tv = has_tv, .p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
		.crcdat.marray_crc = u
	};
    return alloc_crc(&temp);
}

static inline crc* new_marray(const crc *proj, ty *u, const crc *inj) {
	// キーの型が型変数を含むかは見ないので、安全側に倒して has_tv = 1 とする
	return new_marray_tv(proj, u, inj, 1);
}

// mref/marray どうしの合成 (G?p;)m(U)(;G!) ;;; (H?q;)m(U')(;H!) のキー U'' = unify_meet(U, U') を返す。
// 両方の has_tv が 0（U, U' が型変数を含まない）なら U'' も型変数を含まないので、結果も has_tv = 0 にできる。
// ただし unify_meet は複合型を毎回新しく作るため、そのままでは intern_table のキー（ポインタ比較）が
// 呼び出しごとに変わり、一致しないエントリが溜まり続ける。U'' が U か U' と構造的に等しければ（片方が
// Dyn・同じ型どうしなど大半のケース）元のキーのポインタを使う。型変数を含まない型は書き換わらないので安全。
static inline ty *compose_mkey(ty *u1, ty *u2, uint8_t has_tv) {
	ty *meet = unify_meet(u1, u2);
	if (has_tv || meet == u1 || meet == u2) return meet;
	if (ty_equal(meet, u1)) return u1;
	if (ty_equal(meet, u2)) return u2;
	return meet;
}
#else
static inline crc* new_array(const crc *proj, crc *c1, crc *c2, const crc *inj) {
    crc temp = {
		.crckind = C_ARRAY, .has_proj = proj->has_proj, .has_inj = inj->has_inj,
		.has_tv = c1->has_tv | c2->has_tv, .p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
		.crcdat.array_crc = { .c1 = c1, .c2 = c2 }
	};
    return alloc_crc(&temp);
}
#endif

static inline crc *new_tv(const crc *proj, ty *tv, const crc *inj) {
	crc temp = {
		.crckind = C_TV, .has_proj = proj->has_proj, .has_inj = inj->has_inj,
		.has_tv = 1, .p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
		.crcdat.tv = { .p_inj = inj->crcdat.tv.p_inj, .rid_inj = inj->crcdat.tv.rid_inj, .tv_ptr = tv }
	};
    return alloc_crc(&temp);
}

static inline crc *new_bot(const crc *proj, const ground_ty g, const uint16_t size, const uint8_t kind_bot, const uint8_t p_bot, const uint32_t rid_bot) {
    crc temp = {
		.crckind = C_BOT, .has_proj = proj->has_proj,
		.p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
		.crcdat.bot = { .g = g, .size = size, .kind_bot = kind_bot, .p_bot = p_bot, .rid_bot = rid_bot }
	};
    return alloc_crc(&temp);
}

crc *normalize_tv(crc *c) {
	// fprintf(stderr, "TRACE norm ");
	// trace_crc("c", c);
	// fprintf(stderr, "tykind: %d ", c->crcdat.tv.tv_ptr->tykind);
	// fprintf(stderr, "\n");
	#ifdef PROFILE
	normalize_tv_num++;
	#endif
	ty *tv = c->crcdat.tv.tv_ptr;
	switch(tv->tykind) {
		case BASE_INT: return new_id(c, G_INT, 0, c);
		case BASE_BOOL: return new_id(c, G_BOOL, 0, c);
		case BASE_UNIT: return new_id(c, G_UNIT, 0, c);
		case BASE_FLOAT: return new_id(c, G_FLOAT, 0, c);
		case BASE_CHAR: return new_id(c, G_CHAR, 0, c);
		case BASE_STRING: return new_id(c, G_STRING, 0, c);
		case TYFUN: {
			crc inv_c = {
				.crckind = C_TV, .has_proj = c->has_inj, .has_inj = c->has_proj,
				.p_proj = c->crcdat.tv.p_inj ^ 1, .rid_proj = c->crcdat.tv.rid_inj,
				.crcdat.tv = { .rid_inj = c->rid_proj, .p_inj = c->p_proj ^ 1 }
			};
			return new_fun(c, new_tv(&inv_c, tv->tydat.tyfun.left, &inv_c), new_tv(c, tv->tydat.tyfun.right, c), c);
		}
		case TYLIST: return new_list(c, new_tv(c, tv->tydat.tylist, c), c);
		case TYTUPLE: {
			uint16_t size = tv->tydat.tytuple.size; 
			crc **new_crcs = (crc**)GC_MALLOC(sizeof(crc*) * size);
			for (int i = 0; i < size; i++) {
			    new_crcs[i] = new_tv(c, tv->tydat.tytuple.tys[i], c);
			}
		    return new_tuple(c, size, new_crcs, c);
		}
		case TYREF: {
			#ifdef MONOTONIC
			return new_mref(c, tv->tydat.tyref, c);
			#else
			crc inv_c = {
				.crckind = C_TV, .has_proj = c->has_inj, .has_inj = c->has_proj,
				.p_proj = c->crcdat.tv.p_inj ^ 1, .rid_proj = c->crcdat.tv.rid_inj,
				.crcdat.tv = { .rid_inj = c->rid_proj, .p_inj = c->p_proj ^ 1 }
			};
			return new_ref(c, new_tv(c, tv->tydat.tyref, c), new_tv(&inv_c, tv->tydat.tyref, &inv_c), c);
			#endif
		}
		case TYARRAY: {
			#ifdef MONOTONIC
			return new_marray(c, tv->tydat.tyarray, c);
			#else
			crc inv_c = {
				.crckind = C_TV, .has_proj = c->has_inj, .has_inj = c->has_proj,
				.p_proj = c->crcdat.tv.p_inj ^ 1, .rid_proj = c->crcdat.tv.rid_inj,
				.crcdat.tv = { .rid_inj = c->rid_proj, .p_inj = c->p_proj ^ 1 }
			};
			return new_array(c, new_tv(c, tv->tydat.tyarray, c), new_tv(&inv_c, tv->tydat.tyarray, &inv_c), c);
			#endif
		}
		case TYVAR: return c;
		case DYN: {
			printf("tydyn is substituted to tyvar (in normalize_tv)\n");
			exit(1);
		}
		case SUBSTITUTED: {
			printf("SUBSTITUTED is given to normalize_tv\n");
			exit(1);
		}
	}
}

static inline int occur_check_ty(ty *u, const ty *tv) {
	switch (u->tykind) {
		case DYN:
		case BASE_INT:
		case BASE_BOOL:
		case BASE_UNIT:
		case BASE_FLOAT:
		case BASE_CHAR:
		case BASE_STRING:
			return 0;
		case TYFUN:
			return occur_check_ty(u->tydat.tyfun.left, tv) || occur_check_ty(u->tydat.tyfun.right, tv);
		case TYLIST:
			return occur_check_ty(u->tydat.tylist, tv);
		case TYTUPLE:
			for (int i = 0; i < u->tydat.tytuple.size; i++) {
                if (occur_check_ty(u->tydat.tytuple.tys[i], tv)) return 1;
            }
            return 0;
		case TYREF:
			return occur_check_ty(u->tydat.tyref, tv);
		case TYARRAY:
			return occur_check_ty(u->tydat.tyarray, tv);
		case TYVAR:
			return u == tv;
		case SUBSTITUTED:
			u = ty_find(u);
			return occur_check_ty(u, tv);
	}
}

static inline int occur_check_crc(const crc* c, const ty *tv) {
	if (c->has_tv == 0) return 0;
	switch (c->crckind) {
		case C_ID: return 0;
		case C_FUN: return occur_check_crc(c->crcdat.fun_crc.c1, tv) || occur_check_crc(c->crcdat.fun_crc.c2, tv);
		case C_LIST: return occur_check_crc(c->crcdat.lst_crc, tv);
		case C_TUPLE: {
            for (int i = 0; i < c->crcdat.tpl_crc.size; i++) {
                if (occur_check_crc(c->crcdat.tpl_crc.crcs[i], tv)) return 1;
            }
            return 0;
        }
		case C_REF:
			#ifdef MONOTONIC
			return occur_check_ty(c->crcdat.mref_crc, tv);
			#else
			return occur_check_crc(c->crcdat.ref_crc.c1, tv) || occur_check_crc(c->crcdat.ref_crc.c2, tv);
			#endif
		case C_ARRAY:
			#ifdef MONOTONIC
			return occur_check_ty(c->crcdat.marray_crc, tv);
			#else
			return occur_check_crc(c->crcdat.array_crc.c1, tv) || occur_check_crc(c->crcdat.array_crc.c2, tv);
			#endif
		case C_TV: return occur_check_ty(c->crcdat.tv.tv_ptr, tv);
		case C_BOT: return 0;
	}
}

static inline crc *rewrite_proj(crc *proj, crc *base) {
	crc temp = *base;
	temp.has_proj = proj->has_proj;
	temp.p_proj = proj->p_proj;
	temp.rid_proj = proj->rid_proj;
	return alloc_crc(&temp);
}

static inline crc *rewrite_inj(crc *base, crc *inj) {
	crc temp = *base;
	temp.has_inj = inj->has_inj;
	return alloc_crc(&temp);
}

static inline crc *compose_s_tv(crc *c1, const ground_ty g, const uint16_t size, crc *c2) {
	ty *tv = c2->crcdat.tv.tv_ptr;
	switch (tv->tykind) {
		case TYVAR: {
			if (occur_check_crc(c1, tv)) {
				dti(g, size, tv);
				return new_bot(c1, g, size, 1, c2->p_proj, c2->rid_proj); // (G?p;)⊥q (when X occurs in s1 or s2)
			} else {
				dti(g, size, tv); // DTI(G, X)
				break;
			}
		}
		case SUBSTITUTED: {
			c2->crcdat.tv.tv_ptr = ty_find(tv);
			break;
		}
		default: break;
	}
	return compose(c1, normalize_tv(c2));
}

static inline crc *compose_s_bot(crc *c1, const ground_ty g, const uint16_t size, crc *c2) {
	if (c2->has_proj && (g != c2->crcdat.bot.g || size != c2->crcdat.bot.size)) {
		return new_bot(c1, g, size, 0, c2->p_proj, c2->rid_proj);
	}
	return rewrite_proj(c1, c2);
}

static inline crc *compose_tv_tv(crc *c1, ty *tv, crc *c2) {
	ty *tv_ = c2->crcdat.tv.tv_ptr;
	switch (tv_->tykind) {
		case TYVAR: {
			if (tv != tv_) {
				tv->tykind = SUBSTITUTED;
				tv->tydat.tv = tv_;
			}
			if (c1->has_proj == 0 && c2->has_inj == 0) return &crc_id;
			return new_tv(c1, tv_, c2);
		}
		case SUBSTITUTED: {
			c2->crcdat.tv.tv_ptr = ty_find(tv_);
			break;
		}
		default: break;
	}
	return compose(normalize_tv(c1), normalize_tv(c2));
}

static inline crc *compose_tv_bot(crc *c1, ty *tv, crc *c2) { // X?p should not be passed to this function
	dti(c2->crcdat.bot.g, c2->crcdat.bot.size, tv);
	return rewrite_proj(c1, c2); // (G?p;)⊥r
}

// void trace_crc(const char *label, crc *c) {
// 	if (c == &crc_id) { fprintf(stderr, "%s=crc_id ", label); return; }
// 	fprintf(stderr, "%s{kind=%d p=%d i=%d tv=%d p=%d rid=%d", label, c->crckind, c->has_proj, c->has_inj, c->has_tv, c->p_proj, c->rid_proj);
// 	if (c->crckind == C_ID) fprintf(stderr, " g=%d size=%d", c->crcdat.id.g, c->crcdat.id.size);
// 	if (c->crckind == C_TV) fprintf(stderr, " tv=%p rid_inj=%d", (void*)c->crcdat.tv.tv_ptr, c->crcdat.tv.rid_inj);
// 	if (c->crckind == C_FUN) fprintf(stderr, " c1=%p c2=%p", (void*)c->crcdat.fun_crc.c1, (void*)c->crcdat.fun_crc.c2);
// 	fprintf(stderr, "}@%p ", (void*)c);
// }

static crc* internal_compose(crc *c1, crc *c2) {
	// fprintf(stderr, "TRACE compose ");
	// trace_crc("c1", c1);
	// trace_crc("c2", c2);
	// fprintf(stderr, "\n");
	// if (c1->has_inj == 1 && c2->has_proj == 0) {
	// 	fprintf(stderr, "inj ;;; no_proj");
	// 	exit(1);
	// }
	// if (c1->has_inj == 0 && c2->has_proj == 1) {
	// 	fprintf(stderr, "no_inj ;;; proj");
	// 	exit(1);
	// }
	switch(c1->crckind) {
		case C_ID: {
			switch (c2->crckind) {
				case C_ID: { // (G?p;)id{U}(;G!) ;;; (H?q;)id{U'}(;H!)
					if (c1->has_inj == 1 && (c1->crcdat.id.g != c2->crcdat.id.g || c1->crcdat.id.size != c2->crcdat.id.size)) break;
					// if (c1->has_proj == 0 && c2->has_inj == 0) return &crc_id;
					return new_id(c1, c1->crcdat.id.g, c1->crcdat.id.size, c2); // (G?p;)id{U'}(;H!)
				}
				case C_FUN: { // (G?p;)id{U}(;G!) ;;; (H?q;)s->t(;H!)
					if (c1->has_inj == 1 && c1->crcdat.id.g != G_FN) break;
					return rewrite_proj(c1, c2); // (G?p;)s->t(;H!)
				}
				case C_LIST: { // (G?p;)id{U}(;G!) ;;; (H?q;)[s](;H!)
					if (c1->has_inj == 1 && c1->crcdat.id.g != G_LI) break;
					return rewrite_proj(c1, c2); // (G?p;)[s](;H!)
				}
				case C_TUPLE: { // (G?p;)id{U}(;G!) ;;; (H?q;)s1*s2*...*sn(;H!)
					if (c1->has_inj == 1 && (c1->crcdat.id.g != G_TP || c1->crcdat.id.size != c2->crcdat.tpl_crc.size)) break;
					return rewrite_proj(c1, c2); // (G?p;)s1*s2*...*sn(;H!)
				}
				case C_REF: { // (G?p;)id{U}(;G!) ;;; ((H?q;)mref(U')(;H!), (H?q;)ref(s1,s2)(;H!))
					if (c1->has_inj == 1 && c1->crcdat.id.g != G_RF) break;
					return rewrite_proj(c1, c2); // (G?p;)mref(U')(;H!), (G?p;)ref(s1,s2)(;H!)
				}
				case C_ARRAY: { // (G?p;)id{U}(;G!) ;;; ((H?q;)marray(U')(;H!), (H?q;)array(s1,s2)(;H!))
					if (c1->has_inj == 1 && c1->crcdat.id.g != G_AR) break;
					return rewrite_proj(c1, c2); // (G?p;)marray(U')(;H!), (G?p;)array(s1,s2)(;H!)
				}
				case C_TV: { // (G?p;)id{U}(;G!) ;;; (X?q, ?qX!r, X!r)
					// if (c1->has_inj) {
						return compose_s_tv(c1, c1->crcdat.id.g, c1->crcdat.id.size, c2);
					// } else { // id{X} ;;; X!r (because c2 does not have proj and U is not X when c1 has proj)
					// 	return c2;
					// }
				}
				case C_BOT: { // (G?p;)id{U}(;G!) ;;; ((H?q;)⊥r, (X?q;)⊥r)
					return compose_s_bot(c1, c1->crcdat.id.g, c1->crcdat.id.size, c2);
				}
			}
			return new_bot(c1, c1->crcdat.id.g, c1->crcdat.id.size, 0, c2->p_proj, c2->rid_proj); // (G?p;)⊥q
		}
		case C_FUN: {
			switch (c2->crckind) {
				case C_ID: { // (G?p;)s1->s2(;G!) ;;; (H?q;)id{U}(;H!)
					if (c2->has_proj == 1 && c2->crcdat.id.g != G_FN) break;
					return rewrite_inj(c1, c2); // (G?p;)s1->s2(;H!)
				}
				case C_FUN: { // (G?p;)s1->s2(;G!) ;;; (H?q;)t1->t2(;H!)
					crc *cfun1 = compose(c2->crcdat.fun_crc.c1, c1->crcdat.fun_crc.c1); // c1 = t1 ;;; s1
					crc *cfun2 = compose(c1->crcdat.fun_crc.c2, c2->crcdat.fun_crc.c2); // c2 = s2 ;;; t2
					if (cfun1 == &crc_id && cfun2 == &crc_id) { // (G?p;)id(;H!) (if c1=id and c2=id)
						return new_id(c1, G_FN, 0, c2);
					} else {
						return new_fun(c1, cfun1, cfun2, c2); // (G?p;)c1->c2(;H!)
					}
				}
				case C_TV: { // (G?p;)s1->s2(;G!) ;;; (X?q, ?qX!r, X!r)
					return compose_s_tv(c1, G_FN, 0, c2);
				}
				case C_BOT: { // (G?p;)s1->s2(;G!) ;;; ((H?q;)⊥r, (X?q;)⊥r)
					return compose_s_bot(c1, G_FN, 0, c2);
				}
				default: break;
			}
			return new_bot(c1, G_FN, 0, 0, c2->p_proj, c2->rid_proj); // (G?p;)⊥q
		}
		case C_LIST: {
			switch (c2->crckind) {
				case C_ID: { // (G?p;)list(s)(;G!) ;;; (H?q;)id{U}(;H!)
					if (c2->has_proj == 1 && c2->crcdat.id.g != G_LI) break;
					return rewrite_inj(c1, c2); // (G?p;)list(s)(;H!)
				}
				case C_LIST: { // (G?p;)list(s)(;G!) ;;; (H?q;)list(t)(;H!)
					crc *clist = compose(c1->crcdat.lst_crc, c2->crcdat.lst_crc); // c = s ;;; t
					if (clist == &crc_id) { // (G?p;)id(;H!) (if c=id)
						return new_id(c1, G_LI, 0, c2);
					} else {
						return new_list(c1, clist, c2); // (G?p;)list(c)(;H!)
					}
				}
				case C_TV: { // (G?p;)list(s)(;G!) ;;; (X?q, ?qX!r, X!r)
					return compose_s_tv(c1, G_LI, 0, c2);
				}
				case C_BOT: { // (G?p;)list(s)(;G!) ;;; ((H?q;)⊥r, X?q;⊥r)
					return compose_s_bot(c1, G_LI, 0, c2);
				}
				default: break;
			}
			return new_bot(c1, G_LI, 0, 0, c2->p_proj, c2->rid_proj); // (G?p;)⊥q
		}
		case C_TUPLE: {
			uint16_t size = c1->crcdat.tpl_crc.size;
			switch (c2->crckind) {
				case C_ID: { // (G?p;)s1*s2*...*sn(;G!) ;;; (H?q;)id{U}(;H!)
					if (c2->has_proj == 1 && (c2->crcdat.id.g != G_TP || c2->crcdat.id.size != size)) break;
					return rewrite_inj(c1, c2); // (G?p;)s1*s2*...*sn(;H!)
				}
				case C_TUPLE: { // (G?p;)s1*s2*...*sn(;G!) ;;; (H?q;)t1*t2*...*tn(;H!)
					if (c2->crcdat.tpl_crc.size != size) break;
				    crc **new_crcs = (crc**)GC_MALLOC(sizeof(crc*) * size);
				    int all_id = 1;
				    for (int i = 0; i < size; i++) { // c1, c2, ..., cn = s1;;;t1, s2;;;t2, ..., sn;;;tn
				        new_crcs[i] = compose(c1->crcdat.tpl_crc.crcs[i], c2->crcdat.tpl_crc.crcs[i]);
				        if (new_crcs[i] != &crc_id) all_id = 0;
				    }
				    if (all_id) { // (G?p;)id(;H!) (if c1 = id, c2 = id, ..., cn = id)
				        return new_id(c1, G_TP, size, c2);
				    } else {
				        return new_tuple(c1, size, new_crcs, c2); // (G?p;)c1*c2*...*cn(;H!)
				    }
				}
				case C_TV: { // (G?p;)s1*s2*...*sn(;G!) ;;; (X?q, ?qX!r, X!r)
					return compose_s_tv(c1, G_TP, size, c2);
				}
				case C_BOT: { // (G?p;)s1*s2*...*sn(;G!) ;;; ((H?q;)⊥r, X?q;⊥r)
					return compose_s_bot(c1, G_TP, size, c2);
				}
				default: break;
			}
			return new_bot(c1, G_TP, size, 0, c2->p_proj, c2->rid_proj); // (G?p;)⊥q
		}
		case C_REF: {
			switch (c2->crckind) {
				case C_ID: { // ((G?p;)mref(U)(;G!), (G?p;)ref(s1,s2)(;G!)) ;;; (H?q;)id{U'}(;H!)
					if (c2->has_proj == 1 && c2->crcdat.id.g != G_RF) break;
					return rewrite_inj(c1, c2); // (G?p;)mref(U)(;H!), (G?p;)ref(s1,s2)(;H!)
				}
				case C_REF: {
					#ifdef MONOTONIC // (G?p;)mref(U)(;G!) ;;; (H?q;)mref(U')(;H!)
					uint8_t has_tv = c1->has_tv | c2->has_tv;
					ty *meet = compose_mkey(c1->crcdat.mref_crc, c2->crcdat.mref_crc, has_tv); // U'' = unify_meet(U, U')
					return new_mref_tv(c1, meet, c2, has_tv); // (G?p;)mref(U'')(;H!)
					#else // (G?p;)ref(s1,s2)(;G!) ;;; (H?q;)ref(t1,t2)(;H!)
					crc *cref1 = compose(c1->crcdat.ref_crc.c1, c2->crcdat.ref_crc.c1); // c1 = s1 ;;; t1
					crc *cref2 = compose(c2->crcdat.ref_crc.c2, c1->crcdat.ref_crc.c2); // c2 = s2 ;;; t2
					if (cref1 == &crc_id && cref2 == &crc_id) { // (G?p;)id(;H!)
						return new_id(c1, G_RF, 0, c2);
					} else {
						return new_ref(c1, cref1, cref2, c2); // (G?p;)ref(c1,c2)(;H!)
					}
					#endif
				}
				case C_TV: { // (G?p;)ref(s1,s2)(;G!) ;;; (X?q, ?qX!r, X!r)
					return compose_s_tv(c1, G_RF, 0, c2);
				}
				case C_BOT: { // (G?p;)ref(s1,s2)(;G!) ;;; ((H?q;)⊥r, X?q;⊥r)
					return compose_s_bot(c1, G_RF, 0, c2);
				}
				default: break;
			}
			return new_bot(c1, G_RF, 0, 0, c2->p_proj, c2->rid_proj); // (G?p;)⊥q
		}
		case C_ARRAY: {
			switch (c2->crckind) {
				case C_ID: { // ((G?p;)marray(U)(;G!), (G?p;)array(s1,s2)(;G!)) ;;; (H?q;)id{U'}(;H!)
					if (c2->has_proj == 1 && c2->crcdat.id.g != G_AR) break;
					return rewrite_inj(c1, c2); // (G?p;)marray(U)(;H!), (G?p;)array(s1,s2)(;H!)
				}
				case C_ARRAY: {
					#ifdef MONOTONIC // (G?p;)marray(U)(;G!) ;;; (H?q;)marray(U')(;H!)
					uint8_t has_tv = c1->has_tv | c2->has_tv;
					ty *meet = compose_mkey(c1->crcdat.marray_crc, c2->crcdat.marray_crc, has_tv); // U'' = unify_meet(U, U')
					return new_marray_tv(c1, meet, c2, has_tv); // (G?p;)marray(U'')(;H!)
					#else // (G?p;)array(s1,s2)(;G!) ;;; (H?q;)array(t1,t2)(;H!)
					crc *carray1 = compose(c1->crcdat.array_crc.c1, c2->crcdat.array_crc.c1); // c1 = s1 ;;; t1
					crc *carray2 = compose(c2->crcdat.array_crc.c2, c1->crcdat.array_crc.c2); // c2 = s2 ;;; t2
					if (carray1 == &crc_id && carray2 == &crc_id) { // (G?p;)id(;H!)
						return new_id(c1, G_AR, 0, c2);
					} else {
						return new_array(c1, carray1, carray2, c2); // (G?p;)array(c1,c2)(;H!)
					}
					#endif
				}
				case C_TV: { // (G?p;)array(s1,s2)(;G!) ;;; (X?q, ?qX!r, X!r)
					return compose_s_tv(c1, G_AR, 0, c2);
				}
				case C_BOT: { // (G?p;)array(s1,s2)(;G!) ;;; ((H?q;)⊥r, X?q;⊥r)
					return compose_s_bot(c1, G_AR, 0, c2);
				}
				default: break;
			}
			return new_bot(c1, G_AR, 0, 0, c2->p_proj, c2->rid_proj); // (G?p;)⊥q
		}
		case C_TV: {
			ty *tv = c1->crcdat.tv.tv_ptr;
			switch(tv->tykind) {
				case TYVAR: {
					switch (c2->crckind) {
						case C_ID: dti(c2->crcdat.id.g, c2->crcdat.id.size, tv); break;
						case C_FUN: {
							if (occur_check_crc(c2, tv)) return new_bot(c1, G_FN, 0, 1, c2->p_proj, c2->rid_proj);
							dti(G_FN, 0, tv); break;
						}
						case C_LIST: {
							if (occur_check_crc(c2, tv)) return new_bot(c1, G_LI, 0, 1, c2->p_proj, c2->rid_proj);
							dti(G_LI, 0, tv); break;
						}
						case C_TUPLE: {
							if (occur_check_crc(c2, tv)) return new_bot(c1, G_TP, c2->crcdat.tpl_crc.size, 1, c2->p_proj, c2->rid_proj);
							dti(G_TP, c2->crcdat.tpl_crc.size, tv); break;
						}
						case C_REF: {
							if (occur_check_crc(c2, tv)) return new_bot(c1, G_RF, 0, 1, c2->p_proj, c2->rid_proj);
							dti(G_RF, 0, tv); break;
						}
						case C_ARRAY: {
							if (occur_check_crc(c2, tv)) return new_bot(c1, G_AR, 0, 1, c2->p_proj, c2->rid_proj);
							dti(G_AR, 0, tv); break;
						}
						case C_TV: {
							return compose_tv_tv(c1, tv, c2);
						}
						case C_BOT: {
							return compose_tv_bot(c1, tv, c2);
						}
					}
					break;
				}
				case SUBSTITUTED: {
					c1->crcdat.tv.tv_ptr = ty_find(tv);
					break;
				}
				default: break;
			}
			crc *tmp = normalize_tv(c1);
			// fprintf(stderr, "TRACE normalize_result ");
			// trace_crc("tmp", tmp);
			// fprintf(stderr, "\n");
			return compose(tmp, c2);
		}
		case C_BOT: return c1; // (G?p;)⊥q ;;; s = (G?p;)⊥q
	}
}


static crc* compose_body(crc *c1, crc *c2) {
	#ifdef COMPOSE_CACHE
	if (c1->has_tv || c2->has_tv) {
		crc *_res = internal_compose(c1, c2);
		return _res;
    }
    ensure_compose_cache();
    uint32_t hash = (((uintptr_t)c1 >> 3) ^ ((uintptr_t)c2 >> 3)) % CACHE_SIZE;
    if (compose_cache[hash].c1 == c1 && compose_cache[hash].c2 == c2) {
		#ifdef PROFILE
		compose_cached++;
		#endif //PROFILE
		// fprintf(stderr, "TRACE   -> ");
		// trace_crc("res (cached)", compose_cache[hash].result);
		// fprintf(stderr, "\n");
        return compose_cache[hash].result;
    }
    crc *result = internal_compose(c1, c2);
    if (!result->has_tv) { // ensure_compose_cache の不変条件（結果も intern 済みか static）
        compose_cache[hash].c1 = c1;
        compose_cache[hash].c2 = c2;
        compose_cache[hash].result = result;
    }
	// fprintf(stderr, "TRACE   -> ");
	// trace_crc("res", result);
	// fprintf(stderr, "\n");
    return result;

	#else //COMPOSE_CACHE

	crc *_res = internal_compose(c1, c2);
	// fprintf(stderr, "TRACE   -> ");
	// trace_crc("res", _res);
	// fprintf(stderr, "\n");
	return _res;

	#endif //COMPOSE_CACHE
}

crc* compose(crc *c1, crc *c2) {
	#ifdef PROFILE
	current_compose++;
	#endif //PROFILE

    if (c2 == &crc_id) return c1;
    if (c1 == &crc_id) return c2;

	#ifdef PROFILE
	static int compose_depth = 0;
	if (++compose_depth > compose_max_depth) compose_max_depth = compose_depth;
	crc *r = compose_body(c1, c2);
	--compose_depth;
	return r;
	#else
	return compose_body(c1, c2);
	#endif //PROFILE
}

#ifdef MONOTONIC
static void cannot_unify_crc(ty *u1, ty *u2) __attribute__((noreturn));
static void cannot_unify_crc(ty *u1, ty *u2) {
	printf("cannot_unify; %d ~ %d", u1->tykind, u2->tykind);
	blame(0, 0);
}

crc *make_s_coercion(ty *u1, ty *u2) {
	if (ty_equal(u1, u2)) return &crc_id;
	crc temp = {};
	crc temp_proj = { .has_proj = 1 };
	crc temp_inj = { .has_inj = 1 };
    switch (u1->tykind) {
        case DYN: {
			switch (u2->tykind) {
				case DYN: return &crc_id;
				case BASE_INT: return new_id(&temp_proj, G_INT, 0, &temp);
				case BASE_BOOL: return new_id(&temp_proj, G_BOOL, 0, &temp);
				case BASE_UNIT: return new_id(&temp_proj, G_UNIT, 0, &temp);
				case BASE_FLOAT: return new_id(&temp_proj, G_FLOAT, 0, &temp);
				case BASE_CHAR: return new_id(&temp_proj, G_CHAR, 0, &temp);
				case BASE_STRING: return new_id(&temp_proj, G_STRING, 0, &temp);
				case TYFUN: {
					crc *c1 = make_s_coercion_to_dyn(u2->tydat.tyfun.left);
					crc *c2 = make_s_coercion_from_dyn(u2->tydat.tyfun.right);
					if (c1 == &crc_id && c2 == &crc_id) {
						return new_id(&temp_proj, G_FN, 0, &temp);
					} else {
						return new_fun(&temp_proj, c1, c2, &temp);
					}
				}
				case TYLIST: {
					crc *c = make_s_coercion_from_dyn(u2->tydat.tylist);
					if (c == &crc_id) {
						return new_id(&temp_proj, G_LI, 0, &temp);
					} else {
						return new_list(&temp_proj, c, &temp);
					}
				}
				case TYTUPLE: {
					uint16_t size = u2->tydat.tytuple.size;
					crc **crcs = (crc**)GC_MALLOC(sizeof(crc*) * size);
					int all_id = 1;
					for (int i = 0; i < size; i++) {
						crcs[i] = make_s_coercion_from_dyn(u2->tydat.tytuple.tys[i]);
						if (crcs[i] != &crc_id) all_id = 0;
					}
					if (all_id) {
						return new_id(&temp_proj, G_TP, size, &temp);
					} else {
						return new_tuple(&temp_proj, size, crcs, &temp);
					}
				}
				case TYREF: return new_mref(&temp_proj, u2->tydat.tyref, &temp);
				case TYARRAY: return new_marray(&temp_proj, u2->tydat.tyarray, &temp);
				case TYVAR: return new_tv(&temp_proj, u2, &temp);
				case SUBSTITUTED: {
					u2 = ty_find(u2);
					return make_s_coercion(u1, u2);
				}
			}
		}
        case BASE_INT: {
            switch (u2->tykind) {
                case DYN: return &crc_inj_INT;
                case BASE_INT: return &crc_id;
				case SUBSTITUTED: {
					u2 = ty_find(u2);
					return make_s_coercion(u1, u2);
				}
				default: cannot_unify_crc(u1, u2);
            }
        }
        case BASE_BOOL: {
            switch (u2->tykind) {
                case DYN: return &crc_inj_BOOL;
                case BASE_BOOL: return &crc_id;
				case SUBSTITUTED: {
					u2 = ty_find(u2);
					return make_s_coercion(u1, u2);
				}
				default: cannot_unify_crc(u1, u2);
            }
        }
        case BASE_UNIT: {
            switch (u2->tykind) {
                case DYN: return &crc_inj_UNIT;
                case BASE_UNIT: return &crc_id;
				case SUBSTITUTED: {
					u2 = ty_find(u2);
					return make_s_coercion(u1, u2);
				}
				default: cannot_unify_crc(u1, u2);
            }
        }
        case BASE_FLOAT: {
            switch (u2->tykind) {
                case DYN: return &crc_inj_FLOAT;
                case BASE_FLOAT: return &crc_id;
				case SUBSTITUTED: {
					u2 = ty_find(u2);
					return make_s_coercion(u1, u2);
				}
				default: cannot_unify_crc(u1, u2);
            }
        }
        case BASE_CHAR: {
            switch (u2->tykind) {
                case DYN: return &crc_inj_CHAR;
                case BASE_CHAR: return &crc_id;
				case SUBSTITUTED: {
					u2 = ty_find(u2);
					return make_s_coercion(u1, u2);
				}
				default: cannot_unify_crc(u1, u2);
            }
        }
        case BASE_STRING: {
            switch (u2->tykind) {
                case DYN: return &crc_inj_STRING;
                case BASE_STRING: return &crc_id;
				case SUBSTITUTED: {
					u2 = ty_find(u2);
					return make_s_coercion(u1, u2);
				}
				default: cannot_unify_crc(u1, u2);
            }
        }
        case TYFUN: {
            switch (u2->tykind) {
                case DYN: {
					crc *c1 = make_s_coercion_from_dyn(u1->tydat.tyfun.left);
					crc *c2 = make_s_coercion_to_dyn(u1->tydat.tyfun.right);
					if (c1 == &crc_id && c2 == &crc_id) {
						return &crc_inj_FN;
					} else {
						return new_fun(&temp, c1, c2, &temp_inj);
					}
				}
                case TYFUN: {
					crc *c1 = make_s_coercion(u2->tydat.tyfun.left, u1->tydat.tyfun.left);
					crc *c2 = make_s_coercion(u1->tydat.tyfun.right, u2->tydat.tyfun.right);
					if (c1 == &crc_id && c2 == &crc_id) {
						return &crc_id;
					} else {
						return new_fun(&temp, c1, c2, &temp);
					}
                }
				case SUBSTITUTED: {
					u2 = ty_find(u2);
					return make_s_coercion(u1, u2);
				}
                default: cannot_unify_crc(u1, u2);
            }
        }
        case TYLIST: {
            switch (u2->tykind) {
                case DYN: {
					crc *c = make_s_coercion_to_dyn(u1->tydat.tylist);
					if (c == &crc_id) {
						return &crc_inj_LI;
					} else {
						return new_list(&temp, c, &temp_inj);
					}
				}
                case TYLIST: {
					crc *c = make_s_coercion(u1->tydat.tylist, u2->tydat.tylist);
					if (c == &crc_id) {
						return &crc_id;
					} else {
						return new_list(&temp, c, &temp);
					}
                }
				case SUBSTITUTED: {
					u2 = ty_find(u2);
					return make_s_coercion(u1, u2);
				}
                default: cannot_unify_crc(u1, u2);
            }
        }
        case TYTUPLE: {
			uint16_t size = u1->tydat.tytuple.size;
            switch (u2->tykind) {
                case DYN: {
					crc **crcs = (crc**)GC_MALLOC(sizeof(crc*) * size);
					int all_id = 1;
					for (int i = 0; i < size; i++) {
						crcs[i] = make_s_coercion_to_dyn(u1->tydat.tytuple.tys[i]);
						if (crcs[i] != &crc_id) all_id = 0;
					}
                    if (all_id) {
                        return new_id(&temp, G_TP, size, &temp_inj);
                    } else {
                        return new_tuple(&temp, size, crcs, &temp_inj);
                    }
				}
                case TYTUPLE: {
					crc **crcs = (crc**)GC_MALLOC(sizeof(crc*) * size);
					int all_id = 1;
					for (int i = 0; i < size; i++) {
						crcs[i] = make_s_coercion(u1->tydat.tytuple.tys[i], u2->tydat.tytuple.tys[i]);
						if (crcs[i] != &crc_id) all_id = 0;
					}
                    if (all_id) {
                        return &crc_id;
                    } else {
                        return new_tuple(&temp, size, crcs, &temp);
                    }
                }
				case SUBSTITUTED: {
					u2 = ty_find(u2);
					return make_s_coercion(u1, u2);
				}
                default: cannot_unify_crc(u1, u2);
            }
        }
        case TYREF: {
            switch (u2->tykind) {
                case DYN: return new_mref(&temp, &tydyn, &temp_inj);
                case TYREF: return new_mref(&temp, u2->tydat.tyref, &temp);
				case SUBSTITUTED: {
					u2 = ty_find(u2);
					return make_s_coercion(u1, u2);
				}
                default: cannot_unify_crc(u1, u2);
            }
        }
        case TYARRAY: {
            switch (u2->tykind) {
                case DYN: return new_marray(&temp, &tydyn, &temp_inj);
                case TYARRAY: return new_marray(&temp, u2->tydat.tyarray, &temp);
				case SUBSTITUTED: {
					u2 = ty_find(u2);
					return make_s_coercion(u1, u2);
				}
                default: cannot_unify_crc(u1, u2);
            }
        }
        case TYVAR: {
            switch (u2->tykind) {
                case DYN: return new_tv(&temp, u1, &temp_inj);
				case TYVAR: return &crc_id;
				case SUBSTITUTED: {
					u2 = ty_find(u2);
					return make_s_coercion(u1, u2);
				}
                default: cannot_unify_crc(u1, u2);
            }
        }
		case SUBSTITUTED: {
			u1 = ty_find(u1);
			return make_s_coercion(u1, u2);
		}
    }
}

crc *wrap_list(crc *inner) {
	if (inner == &crc_id) return &crc_id;
	crc temp = {};
	return new_list(&temp, inner, &temp);
}

crc *wrap_tuple(uint16_t size, crc **crcs) {
	int all_id = 1;
	for (int i = 0; i < size; i++) {
		if (crcs[i] != &crc_id) { all_id = 0; break; }
	}
	if (all_id) return &crc_id;
	crc temp = {};
	return new_tuple(&temp, size, crcs, &temp);
}

crc *wrap_fn(crc *c1, crc *c2) {
	if (c1 == &crc_id && c2 == &crc_id) return &crc_id;
	crc temp = {};
	return new_fun(&temp, c1, c2, &temp);
}

crc *make_s_coercion_to_dyn(ty *u1) {
	crc temp = {};
	crc temp_inj = { .has_inj = 1 };
	switch (u1->tykind) {
		case DYN: return &crc_id;
		case BASE_INT: return &crc_inj_INT;
		case BASE_BOOL: return &crc_inj_BOOL;
		case BASE_UNIT: return &crc_inj_UNIT;
		case BASE_FLOAT: return &crc_inj_FLOAT;
		case BASE_CHAR: return &crc_inj_CHAR;
		case BASE_STRING: return &crc_inj_STRING;
		case TYFUN: {
			crc *c1 = make_s_coercion_from_dyn(u1->tydat.tyfun.left);
			crc *c2 = make_s_coercion_to_dyn(u1->tydat.tyfun.right);
			if (c1 == &crc_id && c2 == &crc_id) {
				return &crc_inj_FN;
			} else {
				return new_fun(&temp, c1, c2, &temp_inj);
			}
		}
		case TYLIST: {
			crc *c = make_s_coercion_to_dyn(u1->tydat.tylist);
			if (c == &crc_id) {
				return &crc_inj_LI;
			} else {
				return new_list(&temp, c, &temp_inj);
			}
		}
		case TYTUPLE: {
			uint16_t size = u1->tydat.tytuple.size;
			crc **crcs = (crc**)GC_MALLOC(sizeof(crc*) * size);
			int all_id = 1;
			for (int i = 0; i < size; i++) {
				crcs[i] = make_s_coercion_to_dyn(u1->tydat.tytuple.tys[i]);
				if (crcs[i] != &crc_id) all_id = 0;
			}
			if (all_id) {
				return new_id(&temp, G_TP, size, &temp_inj);
			} else {
				return new_tuple(&temp, size, crcs, &temp_inj);
			}
		}
		// TyRef/TyArray(monotonic) は target = Dyn を保持するだけでよい(中身は不要)。
		case TYREF: return new_mref(&temp, &tydyn, &temp_inj);
		case TYARRAY: return new_marray(&temp, &tydyn, &temp_inj);
		case TYVAR: return new_tv(&temp, u1, &temp_inj);
		case SUBSTITUTED: return make_s_coercion_to_dyn(ty_find(u1));
	}
}

crc *make_s_coercion_from_dyn(ty *u2) {
	crc temp = {};
	crc temp_proj = { .has_proj = 1 };
	switch (u2->tykind) {
		case DYN: return &crc_id;
		case BASE_INT: return new_id(&temp_proj, G_INT, 0, &temp);
		case BASE_BOOL: return new_id(&temp_proj, G_BOOL, 0, &temp);
		case BASE_UNIT: return new_id(&temp_proj, G_UNIT, 0, &temp);
		case BASE_FLOAT: return new_id(&temp_proj, G_FLOAT, 0, &temp);
		case BASE_CHAR: return new_id(&temp_proj, G_CHAR, 0, &temp);
		case BASE_STRING: return new_id(&temp_proj, G_STRING, 0, &temp);
		case TYFUN: {
			crc *c1 = make_s_coercion_to_dyn(u2->tydat.tyfun.left);
			crc *c2 = make_s_coercion_from_dyn(u2->tydat.tyfun.right);
			if (c1 == &crc_id && c2 == &crc_id) {
				return new_id(&temp_proj, G_FN, 0, &temp);
			} else {
				return new_fun(&temp_proj, c1, c2, &temp);
			}
		}
		case TYLIST: {
			crc *c = make_s_coercion_from_dyn(u2->tydat.tylist);
			if (c == &crc_id) {
				return new_id(&temp_proj, G_LI, 0, &temp);
			} else {
				return new_list(&temp_proj, c, &temp);
			}
		}
		case TYTUPLE: {
			uint16_t size = u2->tydat.tytuple.size;
			crc **crcs = (crc**)GC_MALLOC(sizeof(crc*) * size);
			int all_id = 1;
			for (int i = 0; i < size; i++) {
				crcs[i] = make_s_coercion_from_dyn(u2->tydat.tytuple.tys[i]);
				if (crcs[i] != &crc_id) all_id = 0;
			}
			if (all_id) {
				return new_id(&temp_proj, G_TP, size, &temp);
			} else {
				return new_tuple(&temp_proj, size, crcs, &temp);
			}
		}
		case TYREF: return new_mref(&temp_proj, u2->tydat.tyref, &temp);
		case TYARRAY: return new_marray(&temp_proj, u2->tydat.tyarray, &temp);
		case TYVAR: return new_tv(&temp_proj, u2, &temp);
		case SUBSTITUTED: return make_s_coercion_from_dyn(ty_find(u2));
	}
}

crc *make_s_coercion_to_ground(ty *u1, ground_ty g) {
	if (u1 == &tydyn) {
		crc temp = {};
		crc temp_proj = { .has_proj = 1 };
		return new_id(&temp_proj, g, 0, &temp);
	} else {
		return &crc_id;
	}
}

crc *make_s_coercion_from_ground(ground_ty g, ty *u2) {
	if (u2 == &tydyn) {
		switch (g) {
			case G_INT: return &crc_inj_INT;
			case G_BOOL: return &crc_inj_BOOL;
			case G_UNIT: return &crc_inj_UNIT;
			case G_FLOAT: return &crc_inj_FLOAT;
			case G_CHAR: return &crc_inj_CHAR;
			case G_STRING: return &crc_inj_STRING;
			default: exit(1);
		}
	} else {
		return &crc_id;
	}
}

crc *make_s_coercion_to_mref(ty *u1, ty *u2) {
	if (u1 == &tydyn) {
		crc temp = {};
		crc temp_proj = { .has_proj = 1 };
		return new_mref(&temp_proj, u2, &temp);
	} else {
		crc temp = {};
		return new_mref(&temp, u2, &temp);
	}
}

crc *make_s_coercion_from_mref(ty *u2) {
	if (u2 == &tydyn) {
		crc temp = {};
		crc temp_inj = { .has_inj = 1 };
		return new_mref(&temp, &tydyn, &temp_inj);
	} else {
		crc temp = {};
		return new_mref(&temp, u2, &temp);
	}
}

crc *make_s_coercion_to_marray(ty *u1, ty *u2) {
	if (u1 == &tydyn) {
		crc temp = {};
		crc temp_proj = { .has_proj = 1 };
		return new_marray(&temp_proj, u2, &temp);
	} else {
		crc temp = {};
		return new_marray(&temp, u2, &temp);
	}
}

crc *make_s_coercion_from_marray(ty *u2) {
	if (u2 == &tydyn) {
		crc temp = {};
		crc temp_inj = { .has_inj = 1 };
		return new_marray(&temp, &tydyn, &temp_inj);
	} else {
		crc temp = {};
		return new_marray(&temp, u2, &temp);
	}
}
#endif

#endif