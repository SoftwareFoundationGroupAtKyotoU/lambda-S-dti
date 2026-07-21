#if !defined(CAST) && !defined(STATIC)

#ifdef HASH
#define CRC_HASH_SIZE 131072
#define CACHE_SIZE 65536
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
crc crc_inj_FN = { .crckind = C_ID, .has_inj = 1, .crcdat = { .id.g = G_FN } };
crc crc_inj_LI = { .crckind = C_ID, .has_inj = 1, .crcdat = { .id.g = G_LI } };
#ifdef MONOTONIC
crc crc_inj_RF = { .crckind = C_REF, .has_inj = 1, .crcdat = { .mref_crc = &tydyn } };
#else
crc crc_inj_RF = { .crckind = C_ID, .has_inj = 1, .crcdat = { .id.g = G_RF } };
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

static crc* intern_table[CRC_HASH_SIZE] = {NULL};

static uint32_t hash_crc(const crc *c) {
    uint32_t h = c->crckind;
    h = (h * 31) + ((c->has_proj << 3) | (c->has_inj << 2) | (c->has_tv << 1) | c->p_proj);
    h = (h * 31) + c->rid_proj;

    switch(c->crckind) {
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
		case C_TV:
			h = (h * 31) + c->crcdat.tv.rid_inj;
            h = (h * 31) + ((uintptr_t)c->crcdat.tv.tv_ptr | c->crcdat.tv.p_inj);
            break;
		case C_BOT: 
		    h = (h * 31) + (uintptr_t)c->crcdat.bot.tv_ptr + c->crcdat.bot.kind_proj + c->crcdat.bot.kind_bot + c->crcdat.bot.p_bot;
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

    switch(a->crckind) {
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
        case C_TV:
            return a->crcdat.tv.rid_inj == b->crcdat.tv.rid_inj &&
                   a->crcdat.tv.p_inj   == b->crcdat.tv.p_inj   &&
                   a->crcdat.tv.tv_ptr  == b->crcdat.tv.tv_ptr;
		case C_BOT:
            return a->crcdat.bot.rid_bot   == b->crcdat.bot.rid_bot   &&
                   a->crcdat.bot.p_bot     == b->crcdat.bot.p_bot     &&
                   a->crcdat.bot.kind_bot  == b->crcdat.bot.kind_bot  &&
                   a->crcdat.bot.kind_proj == b->crcdat.bot.kind_proj &&
                   a->crcdat.bot.tv_ptr    == b->crcdat.bot.tv_ptr;
    }
}

static crc* intern_crc(crc *candidate) {
    uint32_t hash = hash_crc(candidate);
    uint32_t idx = hash % CRC_HASH_SIZE;
    uint32_t start_idx = idx;
    
    while (intern_table[idx] != NULL) {
        if (eq_crc(intern_table[idx], candidate)) {
			#ifdef PROFILE
			alloc_hash++;
			#endif
            return intern_table[idx];
        }
        idx = (idx + 1) % CRC_HASH_SIZE;
        
        if (idx == start_idx) {
            break;
        }
    }
    
    crc *new_c = create_new_crc(candidate);
    intern_table[idx] = new_c;
    
    return new_c;
}

void register_static_crc(crc *c) {
    uint32_t hash = hash_crc(c);
    uint32_t idx = hash % CRC_HASH_SIZE;
    uint32_t start_idx = idx;
    
    while (intern_table[idx] != NULL) {
        if (intern_table[idx] == c) return;
        idx = (idx + 1) % CRC_HASH_SIZE;
        if (idx == start_idx) {
            printf("Fatal: intern_table is full! Increase CRC_HASH_SIZE.\n");
            exit(1);
        }
    }
    intern_table[idx] = c;
}

typedef struct {
    crc *c1;
    crc *c2;
    crc *result;
} compose_cache_entry;

static compose_cache_entry compose_cache[CACHE_SIZE] = {0};

void clear_crc_caches() {
    memset(intern_table, 0, sizeof(intern_table));
    memset(compose_cache, 0, sizeof(compose_cache));
}
#endif //HASH

crc* alloc_crc(crc *candidate) {
	#ifdef PROFILE
	current_alloc++;
	#endif
    #ifdef HASH
	switch(candidate->crckind) {
		case C_TV: {
			ty *tv = ty_find(candidate->crcdat.tv.tv_ptr);
			candidate->crcdat.tv.tv_ptr = tv;
        	if (tv->tykind != TYVAR) candidate = normalize_tv(candidate);
			break;
    	} 
		case C_BOT: {
			if (candidate->crcdat.bot.kind_proj == 1) {
				ty *tv = ty_find(candidate->crcdat.bot.tv_ptr);
				candidate->crcdat.bot.tv_ptr = tv;
    	        if (tv->tykind != TYVAR) candidate = normalize_bot_tv(candidate); 
				break;
			}
			break;
    	}
		default:
			break;
	}
    if (candidate->has_tv) return create_new_crc(candidate);
    return intern_crc(candidate);
    #else // HASH
   	return create_new_crc(candidate);
    #endif // HASH
}

static inline crc *new_id(const crc *proj, const ground_ty g, const uint16_t size, const crc *inj) {
	if (proj->has_proj == 0) {
		if (inj->has_inj == 0) return &crc_id;
		switch (g) {
			case G_INT: return &crc_inj_INT;
			case G_BOOL: return &crc_inj_BOOL;
			case G_UNIT: return &crc_inj_UNIT;
			case G_FN: return &crc_inj_FN;
			case G_LI: return &crc_inj_LI;
			case G_TP: {
				crc temp = { .crckind = C_ID, .has_inj = 1, .crcdat.id = { .g = G_TP, .size = size } };
				return alloc_crc(&temp);
			}
			case G_RF: return &crc_inj_RF;
			default: {
				printf("got G_NONE\n");
				exit(1);
			}
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
static inline crc* new_mref(const crc *proj, ty *u, const crc *inj) {
    crc temp = {
		.crckind = C_REF, .has_proj = proj->has_proj, .has_inj = inj->has_inj,
		/*.has_tv = TODO yet, */ .p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
		.crcdat.mref_crc = u
	};
    return alloc_crc(&temp);
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

static inline crc *new_tv(const crc *proj, ty *tv, const crc *inj) {
	crc temp = {
		.crckind = C_TV, .has_proj = proj->has_proj, .has_inj = inj->has_inj,
		.has_tv = 1, .p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
		.crcdat.tv = { .p_inj = inj->crcdat.tv.p_inj, .rid_inj = inj->crcdat.tv.rid_inj, .tv_ptr = tv }
	};
    return alloc_crc(&temp);
}

static inline crc *new_bot_tv(const crc *proj, ty *tv_ptr, const uint8_t p_bot, const uint32_t rid_bot) {
    crc temp = {
		.crckind = C_BOT, .has_proj = proj->has_proj,
		.has_tv = 1, .p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
		.crcdat.bot = { .tv_ptr = tv_ptr, .kind_proj = 1, .kind_bot = 1, .p_bot = p_bot, .rid_bot = rid_bot }
	};
    return alloc_crc(&temp);
}

static inline crc *new_bot(const crc *proj, const ground_ty g, const uint16_t size, const uint8_t kind_bot, const uint8_t p_bot, const uint32_t rid_bot) {
    crc temp = {
		.crckind = C_BOT, .has_proj = proj->has_proj,
		.p_proj = proj->p_proj, .rid_proj = proj->rid_proj,
		.crcdat.bot = { .proj = { .g = g, .size = size }, .kind_bot = kind_bot, .p_bot = p_bot, .rid_bot = rid_bot }
	};
    return alloc_crc(&temp);
}

crc *normalize_tv(crc *c) {
	ty *tv = c->crcdat.tv.tv_ptr;
	switch(tv->tykind) {
		case BASE_INT: return new_id(c, G_INT, 0, c);
		case BASE_BOOL: return new_id(c, G_BOOL, 0, c);
		case BASE_UNIT: return new_id(c, G_UNIT, 0, c);
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
			// Even if tv is a concrete tyref type, mref should hold tydyn if the coercion has injection
			// X!q ~> mref(dyn);RF!, ?pX!q ~> RF?p;mref(dyn);RF!, X?p ~> RF?p;mref(X') (when X is X' ref)
			if (c->has_inj) {
				return new_mref(c, &tydyn, c);
			} else {
				return new_mref(c, tv->tydat.tyref, c);
			}
			#else
			crc inv_c = {
				.crckind = C_TV, .has_proj = c->has_inj, .has_inj = c->has_proj,
				.p_proj = c->crcdat.tv.p_inj ^ 1, .rid_proj = c->crcdat.tv.rid_inj,
				.crcdat.tv = { .rid_inj = c->rid_proj, .p_inj = c->p_proj ^ 1 }
			};
			return new_ref(c, new_tv(c, tv->tydat.tyref, c), new_tv(&inv_c, tv->tydat.tyref, &inv_c), c);
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

crc *normalize_bot_tv(crc *c) {
	ty *tv = c->crcdat.bot.tv_ptr;
	switch(tv->tykind) {
		case BASE_INT: return new_bot(c, G_INT, 0, c->crcdat.bot.kind_bot, c->crcdat.bot.p_bot, c->crcdat.bot.rid_bot);
		case BASE_BOOL: return new_bot(c, G_BOOL, 0, c->crcdat.bot.kind_bot, c->crcdat.bot.p_bot, c->crcdat.bot.rid_bot);
		case BASE_UNIT: return new_bot(c, G_UNIT, 0, c->crcdat.bot.kind_bot, c->crcdat.bot.p_bot, c->crcdat.bot.rid_bot);
		case TYFUN: return new_bot(c, G_FN, 0, c->crcdat.bot.kind_bot, c->crcdat.bot.p_bot, c->crcdat.bot.rid_bot);
		case TYLIST: return new_bot(c, G_LI, 0, c->crcdat.bot.kind_bot, c->crcdat.bot.p_bot, c->crcdat.bot.rid_bot);
		case TYTUPLE: return new_bot(c, G_TP, tv->tydat.tytuple.size, c->crcdat.bot.kind_bot, c->crcdat.bot.p_bot, c->crcdat.bot.rid_bot);
		case TYREF: return new_bot(c, G_RF, 0, c->crcdat.bot.kind_bot, c->crcdat.bot.p_bot, c->crcdat.bot.rid_bot);
		case TYVAR: return c;
		case DYN: {
			printf("tydyn is substituted to tyvar (in normalize_bot_tv)\n");
			exit(1);
		}
		case SUBSTITUTED: {
			printf("SUBSTITUTED is given to normalize_bot_tv\n");
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
		case C_TV:
			return occur_check_ty(c->crcdat.tv.tv_ptr, tv);
		case C_BOT:
			return c->crcdat.bot.kind_proj && occur_check_ty(c->crcdat.bot.tv_ptr, tv);
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

static inline crc *compose_s_tv(crc *c1, const ground_ty g, const uint16_t size,  crc *c2) {
	ty *tv = c2->crcdat.tv.tv_ptr;
	switch (tv->tykind) {
		case TYVAR: {
			if (occur_check_crc(c1, tv)) {
				return new_bot_tv(c1, tv, c2->p_proj, c2->rid_proj); // (G?p;)⊥q (when X occurs in s1 or s2)
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
	if (c2->has_proj) {
		if (c2->crcdat.bot.kind_proj) {
			ty *tv = c2->crcdat.bot.tv_ptr;
			switch (tv->tykind) {
				case TYVAR: {
					if (occur_check_crc(c1, tv)) {
						return new_bot_tv(c1, tv, c2->p_proj, c2->rid_proj); // (G?p;)⊥q (when X occurs in s1 or s2)
					} else {
						dti(g, size, tv); // DTI(G, X)
						break;
					}
				}
				case SUBSTITUTED: {
					c2->crcdat.bot.tv_ptr = ty_find(tv);
					break;
				}
				default: break;
			}
			return compose(c1, normalize_bot_tv(c2));
		} else {
			if (g != c2->crcdat.bot.proj.g || size != c2->crcdat.bot.proj.size) {
				return new_bot(c1, g, size, 0, c2->p_proj, c2->rid_proj);
			}
		}
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
			return new_tv(c1, tv_, c2);
		}
		case SUBSTITUTED: {
			c2->crcdat.tv.tv_ptr = ty_find(tv_);
			break;
		}
		default: break;
	}
	return compose(c1, normalize_tv(c2));
}

static inline crc *compose_tv_bot(crc *c1, ty *tv, crc *c2) {
	if (c2->has_proj) {
		if (c2->crcdat.bot.kind_proj) { // (X!q, ?pX!q) ;;; ?p'Y;⊥q'
			ty *tv_ = c2->crcdat.bot.tv_ptr;
			switch (tv_->tykind) {
				case TYVAR: {
					if (tv != tv_) {
						tv->tykind = SUBSTITUTED;
						tv->tydat.tv = tv_;
					}
					return new_bot_tv(c1, tv_, c2->crcdat.bot.p_bot, c2->crcdat.bot.rid_bot);
				}
				case SUBSTITUTED: {
					c2->crcdat.bot.tv_ptr = ty_find(tv_);
					break;
				}
				default: break;
			}
			return compose(c1, normalize_bot_tv(c2));
		} else {
			dti(c2->crcdat.bot.proj.g, c2->crcdat.bot.proj.size, tv);
		}
	}
	return rewrite_proj(c1, c2); // (G?p;)⊥r
}

static crc* internal_compose(crc *c1, crc *c2) {
	switch(c1->crckind) {
		case C_ID: {
			switch (c2->crckind) {
				case C_ID: { // (G?p;)id{U}(;G!) ;;; (H?q;)id{U'}(;H!)
					if (c1->has_inj == 1 && (c1->crcdat.id.g != c2->crcdat.id.g || c1->crcdat.id.size != c2->crcdat.id.size)) break;
					return rewrite_proj(c1, c2); // (G?p;)id{U'}(;H!)
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
				case C_TV: { // (G?p;)id{U}(;G!) ;;; (X?q, ?qX!r, X!r)
					if (c1->has_inj) {
						return compose_s_tv(c1, c1->crcdat.id.g, c1->crcdat.id.size, c2);
					} else { // id{X} ;;; X!r (because c2 does not have proj and U is not X when c1 has proj)
						return c2;
					}
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
					ty *meet = unify_meet(c1->crcdat.mref_crc, c2->crcdat.mref_crc); // U'' = unify_meet(U, U')
					return new_mref(c1, meet, c2); // (G?p;)mref(U'')(;H!)
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
		case C_TV: {
			ty *tv = c1->crcdat.tv.tv_ptr;
			switch(tv->tykind) {
				case TYVAR: {
					switch (c2->crckind) {
						case C_ID: dti(c2->crcdat.id.g, c2->crcdat.id.size, tv); break;
						case C_FUN: {
							if (occur_check_crc(c2, tv)) return new_bot_tv(c1, tv, c2->p_proj, c2->rid_proj);
							dti(G_FN, 0, tv); break;
						}
						case C_LIST: {
							if (occur_check_crc(c2, tv)) return new_bot_tv(c1, tv, c2->p_proj, c2->rid_proj);
							dti(G_LI, 0, tv); break;
						}
						case C_TUPLE: {
							if (occur_check_crc(c2, tv)) return new_bot_tv(c1, tv, c2->p_proj, c2->rid_proj);
							dti(G_TP, c2->crcdat.tpl_crc.size, tv); break;
						}
						case C_REF: {
							if (occur_check_crc(c2, tv)) return new_bot_tv(c1, tv, c2->p_proj, c2->rid_proj);
							dti(G_RF, 0, tv); break;
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
			return compose(normalize_tv(c1), c2);
		}
		case C_BOT: return c1; // ((G?p;)⊥q, X?p;⊥q) ;;; s = (G?p;)⊥q, X?p;⊥q
	}
}


crc* compose(crc *c1, crc *c2) {
	#ifdef PROFILE
	current_compose++;
	#endif //PROFILE

    if (c2 == &crc_id) return c1;
    if (c1 == &crc_id) return c2;

	#ifdef HASH
	if (c1->has_tv || c2->has_tv) {
        return internal_compose(c1, c2);
    }
    uint32_t hash = (((uintptr_t)c1 >> 3) ^ ((uintptr_t)c2 >> 3)) % CACHE_SIZE;
    if (compose_cache[hash].c1 == c1 && compose_cache[hash].c2 == c2) {
		#ifdef PROFILE
		compose_cached++;
		#endif //PROFILE
        return compose_cache[hash].result;
    }
    crc *result = internal_compose(c1, c2);
    compose_cache[hash].c1 = c1;
    compose_cache[hash].c2 = c2;
    compose_cache[hash].result = result;
    return result;

	#else //HASH
    
	return internal_compose(c1, c2);
	
	#endif //HASH
}

#ifdef MONOTONIC
// blame label is not implemented, yet TODO
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
				case TYFUN: return new_id(&temp_proj, G_FN, 0, &temp);
				case TYLIST: return new_id(&temp_proj, G_LI, 0, &temp);
				case TYTUPLE: return new_id(&temp_proj, G_TP, u2->tydat.tytuple.size, &temp);
				case TYREF: return new_id(&temp_proj, G_RF, 0, &temp);
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
				default: break;
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
				default: break;
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
				default: break;
            }
        }
        case TYFUN: {
            switch (u2->tykind) {
                case DYN: {
					crc *c1 = make_s_coercion(&tydyn, u1->tydat.tyfun.left);
					crc *c2 = make_s_coercion(u1->tydat.tyfun.right, &tydyn);
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
                default: break;
            }
        }
        case TYLIST: {
            switch (u2->tykind) {
                case DYN: {
					crc *c = make_s_coercion(u1->tydat.tylist, &tydyn);
					if (c == &crc_id) {
						return &crc_id;
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
                default: break;
            }
        }
        case TYTUPLE: {
			uint16_t size = u1->tydat.tytuple.size;
            switch (u2->tykind) {
                case DYN: {
					crc **crcs = (crc**)GC_MALLOC(sizeof(crc*) * size);
					int all_id = 1;
					for (int i = 0; i < size; i++) {
						crcs[i] = make_s_coercion(u1->tydat.tytuple.tys[i], u2->tydat.tytuple.tys[i]);
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
                default: break;
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
                default: break;
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
                default: break;
            }
        }
		case SUBSTITUTED: {
			u1 = ty_find(u1);
			return make_s_coercion(u1, u2);
		}
    }
}
#endif

#endif