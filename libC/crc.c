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

crc crc_id = { .crckind = ID, .has_tv = 0 };
crc crc_inj_INT = { .crckind = SEQ_INJ, .g_inj = G_INT, .has_tv = 0, .crcdat = { .seq_tv = { .ptr = { .s = &crc_id } } } };
crc crc_inj_BOOL = { .crckind = SEQ_INJ, .g_inj = G_BOOL, .has_tv = 0, .crcdat = { .seq_tv = { .ptr = { .s = &crc_id } } } };
crc crc_inj_UNIT = { .crckind = SEQ_INJ, .g_inj = G_UNIT, .has_tv = 0, .crcdat = { .seq_tv = { .ptr = { .s = &crc_id } } } };
crc crc_inj_AR = { .crckind = SEQ_INJ, .g_inj = G_AR, .has_tv = 0, .crcdat = { .seq_tv = { .ptr = { .s = &crc_id } } } };
crc crc_inj_LI = { .crckind = SEQ_INJ, .g_inj = G_LI, .has_tv = 0, .crcdat = { .seq_tv = { .ptr = { .s = &crc_id } } } };

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
    h = (h * 31) + c->g_proj;
    h = (h * 31) + c->g_inj;
    h = (h * 31) + c->p_proj;
    h = (h * 31) + c->p_inj;
    h = (h * 31) + c->botkind;
    h = (h * 31) + c->crcdat.seq_tv.rid_proj;
    h = (h * 31) + c->crcdat.seq_tv.rid_inj;
    h = (h * 31) + (uintptr_t)c->crcdat.seq_tv.ptr.s;
    return h;
}

static int eq_crc(const crc *a, const crc *b) {
    if (a == b) return 1;
    
    if (a->crckind != b->crckind ||
        a->g_proj  != b->g_proj  ||
        a->g_inj   != b->g_inj   ||
        a->p_proj  != b->p_proj  ||
        a->p_inj   != b->p_inj   ||
        a->botkind != b->botkind) {
        return 0;
    }

    return a->crcdat.seq_tv.rid_proj == b->crcdat.seq_tv.rid_proj &&
           a->crcdat.seq_tv.rid_inj  == b->crcdat.seq_tv.rid_inj  &&
           a->crcdat.seq_tv.ptr.s    == b->crcdat.seq_tv.ptr.s;
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
		case TV_INJ: {
			candidate->crcdat.seq_tv.ptr.tv = ty_find(candidate->crcdat.seq_tv.ptr.tv);
        	if (candidate->crcdat.seq_tv.ptr.tv->tykind != TYVAR) {
            	return normalize_tv_inj(candidate); 
        	}
			break;
    	} 
		case TV_PROJ: {
    	    candidate->crcdat.seq_tv.ptr.tv = ty_find(candidate->crcdat.seq_tv.ptr.tv);
    	    if (candidate->crcdat.seq_tv.ptr.tv->tykind != TYVAR) {
    	        return normalize_tv_proj(candidate); 
    	    }
			break;
    	}
		case TV_PROJ_INJ: {
    	    candidate->crcdat.seq_tv.ptr.tv = ty_find(candidate->crcdat.seq_tv.ptr.tv);
    	    if (candidate->crcdat.seq_tv.ptr.tv->tykind != TYVAR) {
    	        return normalize_tv_proj_inj(candidate); 
    	    }
			break;
    	} 
		case TV_PROJ_OCCUR: {
    	    candidate->crcdat.seq_tv.ptr.tv = ty_find(candidate->crcdat.seq_tv.ptr.tv);
    	    if (candidate->crcdat.seq_tv.ptr.tv->tykind != TYVAR) {
    	        return normalize_tv_proj_occur(candidate); 
    	    }
			break;
    	}
		default:
			break;
	}

    if (candidate->has_tv) {
        return create_new_crc(candidate);
    }

    return intern_crc(candidate);
    
    #else // HASH
   	return create_new_crc(candidate);
    #endif // HASH
}

static inline crc* new_fun(crc *c1, crc *c2) {
    crc temp = {0};
    temp.crckind = FUN;
	temp.has_tv = c1->has_tv | c2->has_tv;
    temp.crcdat.two_crc.c1 = c1;
    temp.crcdat.two_crc.c2 = c2;
    return alloc_crc(&temp);
}

static inline crc* new_list(crc *c) {
    crc temp = {0};
    temp.crckind = LIST;
	temp.has_tv = c->has_tv;
    temp.crcdat.one_crc = c;
    return alloc_crc(&temp);
}

static inline crc *new_bot(const uint8_t p, const uint32_t rid, const uint8_t is_occur) {
    crc temp = {0};
    temp.crckind = BOT;
    temp.p_proj = p;
	temp.botkind = is_occur;
	temp.has_tv = 0;
    temp.crcdat.seq_tv.rid_proj = rid;
    return alloc_crc(&temp);
}

static inline crc* new_seq_proj(const crc *base_proj, crc *s_new) {
    crc temp = {0};
    temp.crckind = SEQ_PROJ;
    temp.g_proj = base_proj->g_proj;
    temp.p_proj = base_proj->p_proj;
	temp.has_tv = s_new->has_tv;
    temp.crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    temp.crcdat.seq_tv.ptr.s = s_new;
    return alloc_crc(&temp);
}

static inline crc* new_seq_inj(crc *s_new, const crc *base_inj) {
    if (s_new == &crc_id) {
        switch (base_inj->g_inj) {
            case G_INT: return &crc_inj_INT;
            case G_BOOL: return &crc_inj_BOOL;
            case G_UNIT: return &crc_inj_UNIT;
            case G_AR: return &crc_inj_AR;
            case G_LI: return &crc_inj_LI;
            default: {
                printf("got G_NONE");
                exit(1);
            }
        }
    }
    crc temp = {0};
    temp.crckind = SEQ_INJ;
    temp.g_inj = base_inj->g_inj;
	temp.has_tv = s_new->has_tv;
    temp.crcdat.seq_tv.ptr.s = s_new;
    return alloc_crc(&temp);
}

static inline crc* new_seq_proj_inj(const crc *base_proj, crc *s_new, const crc *base_inj) {
    crc temp = {0};
    temp.crckind = SEQ_PROJ_INJ;
    temp.g_proj = base_proj->g_proj;
    temp.p_proj = base_proj->p_proj;
    temp.g_inj = base_inj->g_inj;
	temp.has_tv = s_new->has_tv;
    temp.crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    temp.crcdat.seq_tv.ptr.s = s_new;
    return alloc_crc(&temp);
}

static inline crc *new_seq_proj_bot(const crc *base_proj, crc *bot) {
    crc temp = {0};
    temp.crckind = SEQ_PROJ_BOT;
    temp.g_proj = base_proj->g_proj;
    temp.p_proj = base_proj->p_proj;
	temp.has_tv = bot->has_tv;
    temp.crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    temp.crcdat.seq_tv.ptr.s = bot;
    return alloc_crc(&temp);
}

static inline crc* new_tv_proj(const crc *base_proj, ty *tv) {
    crc temp = {0};
    temp.crckind = TV_PROJ;
    temp.p_proj = base_proj->p_proj;
	temp.has_tv = 1;
    temp.crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    temp.crcdat.seq_tv.ptr.tv = tv;
    return alloc_crc(&temp);
}

static inline crc* new_tv_inj(ty *tv, const crc *base_inj) {
    crc temp = {0};
    temp.crckind = TV_INJ;
    temp.p_inj = base_inj->p_inj;
	temp.has_tv = 1;
    temp.crcdat.seq_tv.rid_inj = base_inj->crcdat.seq_tv.rid_inj;
    temp.crcdat.seq_tv.ptr.tv = tv;
    return alloc_crc(&temp);
}

static inline crc* new_tv_proj_inj(const crc *base_proj, ty *tv, const crc *base_inj) {
    crc temp = {0};
    temp.crckind = TV_PROJ_INJ;
    temp.p_proj = base_proj->p_proj;
    temp.p_inj = base_inj->p_inj;
	temp.has_tv = 1;
    temp.crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    temp.crcdat.seq_tv.rid_inj = base_inj->crcdat.seq_tv.rid_inj;
    temp.crcdat.seq_tv.ptr.tv = tv;
    return alloc_crc(&temp);
}

static inline crc* new_tv_proj_occur(const crc* base_proj, const uint8_t bot_p, const uint32_t bot_rid) {
    crc temp = {0};
    temp.crckind = TV_PROJ_OCCUR;
    temp.p_proj = base_proj->p_proj;
    temp.p_inj = bot_p;
	temp.has_tv = 1;
    temp.crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    temp.crcdat.seq_tv.rid_inj = bot_rid;
    temp.crcdat.seq_tv.ptr.tv = base_proj->crcdat.seq_tv.ptr.tv;
    return alloc_crc(&temp);
}

static inline crc *normalize_tv_inj_int(crc *c) { return &crc_inj_INT; }
static inline crc *normalize_tv_inj_bool(crc *c) { return &crc_inj_BOOL; }
static inline crc *normalize_tv_inj_unit(crc *c) { return &crc_inj_UNIT; }
static inline crc *normalize_tv_inj_fun(crc *c) {
    crc temp1 = {0};
    temp1.crckind = TV_PROJ;
    temp1.p_proj = c->p_inj ^ 1;
	temp1.has_tv = 1;
    temp1.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_inj;
    temp1.crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.left;
    crc *cfun1 = alloc_crc(&temp1);

    crc temp2 = {0};
    temp2.crckind = TV_INJ;
    temp2.p_inj = c->p_inj;
	temp2.has_tv = 1;
    temp2.crcdat.seq_tv.rid_inj = c->crcdat.seq_tv.rid_inj;
    temp2.crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.right;
    crc *cfun2 = alloc_crc(&temp2);

    crc *cfun = new_fun(cfun1, cfun2);

    crc temp3 = {0};
    temp3.crckind = SEQ_INJ;
    temp3.g_inj = G_AR;
	temp3.has_tv = cfun->has_tv;
    temp3.crcdat.seq_tv.ptr.s = cfun;
    return alloc_crc(&temp3);
}
static inline crc *normalize_tv_inj_list(crc* c) {
    crc temp1 = {0};
    temp1.crckind = TV_INJ;
    temp1.p_inj = c->p_inj;
	temp1.has_tv = 1;
    temp1.crcdat.seq_tv.rid_inj = c->crcdat.seq_tv.rid_inj;
    temp1.crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tylist;
    crc *clist_ = alloc_crc(&temp1);

    crc *clist = new_list(clist_);

    crc temp2 = {0};
    temp2.crckind = SEQ_INJ;
    temp2.g_inj = G_LI;
	temp2.has_tv = clist->has_tv;
    temp2.crcdat.seq_tv.ptr.s = clist;
    return alloc_crc(&temp2);
}
inline crc *normalize_tv_inj(crc *c) {
	switch(c->crcdat.seq_tv.ptr.tv->tykind) {
		case BASE_INT: return normalize_tv_inj_int(c); // X! [X:=int] -> id;int!
		case BASE_BOOL: return normalize_tv_inj_bool(c);
		case BASE_UNIT: return normalize_tv_inj_unit(c);
		case TYFUN: return normalize_tv_inj_fun(c);         // X! [X:=X1=>X2] -> X1?p=>X2!;(★→★)!	
		case TYLIST: return normalize_tv_inj_list(c);         // X! [X:=[X1]] -> [X1!];[★]!
		default: return c;
	}
}

static inline crc *normalize_tv_proj_base(crc *c, ground_ty g) {
    crc temp = {0};
    temp.crckind = SEQ_PROJ;
    temp.g_proj = g;
    temp.p_proj = c->p_proj;
	temp.has_tv = 0;
    temp.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
    temp.crcdat.seq_tv.ptr.s = &crc_id;
    return alloc_crc(&temp);
}
static inline crc *normalize_tv_proj_int(crc *c)  { return normalize_tv_proj_base(c, G_INT); }
static inline crc *normalize_tv_proj_bool(crc *c) { return normalize_tv_proj_base(c, G_BOOL); }
static inline crc *normalize_tv_proj_unit(crc *c) { return normalize_tv_proj_base(c, G_UNIT); }
static inline crc *normalize_tv_proj_fun(crc *c) {
    crc temp1 = {0};
    temp1.crckind = TV_INJ;
    temp1.p_inj = c->p_proj ^ 1;
	temp1.has_tv = 1;
    temp1.crcdat.seq_tv.rid_inj = c->crcdat.seq_tv.rid_proj;
    temp1.crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.left;
    crc *cfun1 = alloc_crc(&temp1);

    crc temp2 = {0};
    temp2.crckind = TV_PROJ;
    temp2.p_proj = c->p_proj;
	temp2.has_tv = 1;
    temp2.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
    temp2.crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.right;
    crc *cfun2 = alloc_crc(&temp2);

    crc *cfun = new_fun(cfun1, cfun2);

    crc temp3 = {0};
    temp3.crckind = SEQ_PROJ;
    temp3.g_proj = G_AR;
    temp3.p_proj = c->p_proj;
	temp3.has_tv = cfun->has_tv;
    temp3.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
    temp3.crcdat.seq_tv.ptr.s = cfun;
    return alloc_crc(&temp3);
}
static inline crc *normalize_tv_proj_list(crc *c) {
    crc temp1 = {0};
    temp1.crckind = TV_PROJ;
    temp1.p_proj = c->p_proj;
	temp1.has_tv = 1;
    temp1.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
    temp1.crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tylist;
    crc *clist_ = alloc_crc(&temp1);

    crc *clist = new_list(clist_);

    crc temp2 = {0};
    temp2.crckind = SEQ_PROJ;
    temp2.g_proj = G_LI;
    temp2.p_proj = c->p_proj;
	temp2.has_tv = clist->has_tv;
    temp2.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
    temp2.crcdat.seq_tv.ptr.s = clist;
    return alloc_crc(&temp2);
}
inline crc *normalize_tv_proj(crc *c) {
	switch(c->crcdat.seq_tv.ptr.tv->tykind) {
		case BASE_INT: return normalize_tv_proj_int(c);				// X?p [X:=int] -> int?p;id
		case BASE_BOOL: return normalize_tv_proj_bool(c);
		case BASE_UNIT: return normalize_tv_proj_unit(c);
		case TYFUN: return normalize_tv_proj_fun(c);       // X?p [X:=X1=>X2] -> (★→★)?p;X1!=>X2?p
		case TYLIST: return normalize_tv_proj_list(c);        // X?p [X:=[X1]] -> [★]?p;[X1?p]
		default: return c;
	}
}

static inline crc *normalize_tv_proj_inj_base(crc *c, ground_ty g) {
    crc temp = {0};
    temp.crckind = SEQ_PROJ_INJ;
    temp.g_proj = g;
    temp.g_inj = g;
    temp.p_proj = c->p_proj;
	temp.has_tv = 0;
    temp.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
    temp.crcdat.seq_tv.ptr.s = &crc_id;
    return alloc_crc(&temp);
}
static inline crc *normalize_tv_proj_inj_int(crc *c)  { return normalize_tv_proj_inj_base(c, G_INT); }
static inline crc *normalize_tv_proj_inj_bool(crc *c) { return normalize_tv_proj_inj_base(c, G_BOOL); }
static inline crc *normalize_tv_proj_inj_unit(crc *c) { return normalize_tv_proj_inj_base(c, G_UNIT); }
static inline crc *normalize_tv_proj_inj_fun(crc *c) {
    ty *t1 = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.left;
    ty *t2 = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.right;

    crc temp1 = {0};
    temp1.crckind = TV_PROJ_INJ;
    temp1.p_proj = c->p_inj ^ 1;
    temp1.p_inj = c->p_proj ^ 1;
	temp1.has_tv = 1;
    temp1.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_inj;
    temp1.crcdat.seq_tv.rid_inj = c->crcdat.seq_tv.rid_proj;
    temp1.crcdat.seq_tv.ptr.tv = t1;
    crc *cfun1 = alloc_crc(&temp1);

    crc temp2 = {0};
    temp2.crckind = TV_PROJ_INJ;
    temp2.p_proj = c->p_proj;
    temp2.p_inj = c->p_inj;
	temp2.has_tv = 1;
    temp2.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
    temp2.crcdat.seq_tv.rid_inj = c->crcdat.seq_tv.rid_inj;
    temp2.crcdat.seq_tv.ptr.tv = t2;
    crc *cfun2 = alloc_crc(&temp2);

    crc *cfun = new_fun(cfun1, cfun2);

    crc temp3 = {0};
    temp3.crckind = SEQ_PROJ_INJ;
    temp3.g_proj = G_AR;
    temp3.g_inj = G_AR;
    temp3.p_proj = c->p_proj;
	temp3.has_tv = cfun->has_tv;
    temp3.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
    temp3.crcdat.seq_tv.ptr.s = cfun;
    return alloc_crc(&temp3);
}
static inline crc *normalize_tv_proj_inj_list(crc *c) {
    crc temp1 = {0};
    temp1.crckind = TV_PROJ_INJ;
    temp1.p_proj = c->p_proj;
    temp1.p_inj = c->p_inj;
	temp1.has_tv = 1;
    temp1.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
    temp1.crcdat.seq_tv.rid_inj = c->crcdat.seq_tv.rid_inj;
    temp1.crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tylist;
    crc *clist_ = alloc_crc(&temp1);

    crc *clist = new_list(clist_);

    crc temp2 = {0};
    temp2.crckind = SEQ_PROJ_INJ;
    temp2.g_proj = G_LI;
    temp2.g_inj = G_LI;
    temp2.p_proj = c->p_proj;
	temp2.has_tv = clist->has_tv;
    temp2.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
    temp2.crcdat.seq_tv.ptr.s = clist;
    return alloc_crc(&temp2);
}
inline crc *normalize_tv_proj_inj(crc *c) {
	switch(c->crcdat.seq_tv.ptr.tv->tykind) {
		case BASE_INT: return normalize_tv_proj_inj_int(c);                    // ?pX!q [X:=int] -> int?p;id;int!
		case BASE_BOOL: return normalize_tv_proj_inj_bool(c);
		case BASE_UNIT: return normalize_tv_proj_inj_unit(c);
		case TYFUN: return normalize_tv_proj_inj_fun(c);  				// ?pX!q [X:=X1=>X2] -> (★→★)?p;(?-qX1!-p=>?pX2!q);(★→★)!
		case TYLIST: return normalize_tv_proj_inj_list(c);				// ?pX!q [X:=[X1]] -> [★]?p;[?pX1!q];[★]!
		default: return c;
	}
}

static inline crc *normalize_tv_proj_occur_base(crc *c, ground_ty g) {
    crc bot_temp = {0};
    bot_temp.crckind = BOT;
    bot_temp.botkind = 1;
    bot_temp.p_proj = c->p_inj;
	bot_temp.has_tv = 0;
    bot_temp.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_inj;
    crc *bot = alloc_crc(&bot_temp);

    crc temp = {0};
    temp.crckind = SEQ_PROJ_BOT;
    temp.g_proj = g;
    temp.p_proj = c->p_proj;
	temp.has_tv = bot->has_tv;
    temp.crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
    temp.crcdat.seq_tv.ptr.s = bot;
    return alloc_crc(&temp);
}
static inline crc *normalize_tv_proj_occur_int(crc *c)  { return normalize_tv_proj_occur_base(c, G_INT); }
static inline crc *normalize_tv_proj_occur_bool(crc *c) { return normalize_tv_proj_occur_base(c, G_BOOL); }
static inline crc *normalize_tv_proj_occur_unit(crc *c) { return normalize_tv_proj_occur_base(c, G_UNIT); }
static inline crc *normalize_tv_proj_occur_fun(crc *c)  { return normalize_tv_proj_occur_base(c, G_AR); }
static inline crc *normalize_tv_proj_occur_list(crc *c) { return normalize_tv_proj_occur_base(c, G_LI); }
inline crc *normalize_tv_proj_occur(crc *c) {
	switch(c->crcdat.seq_tv.ptr.tv->tykind) {
		case BASE_INT: return normalize_tv_proj_occur_int(c);                    // ?p⊥Xq [X:=int] -> int?p;⊥q
		case BASE_BOOL: return normalize_tv_proj_occur_bool(c);
		case BASE_UNIT: return normalize_tv_proj_occur_unit(c);
		case TYFUN: return normalize_tv_proj_occur_fun(c);  				// ?p⊥Xq [X:=X1=>X2] -> (★→★)?p;⊥q
		case TYLIST: return normalize_tv_proj_occur_list(c);				// ?p⊥Xq [X:=[X1]] -> [★]?p;⊥q
		default: return c;
	}
}

// static inline crc* shallow_normalize(crc *c) {
//     switch (c->crckind) {
//         case TV_INJ:
//             c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
//             return normalize_tv_inj(c);
//         case TV_PROJ:
//             c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
//             return normalize_tv_proj(c);
//         case TV_PROJ_INJ:
//             c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
//             return normalize_tv_proj_inj(c);
//         case TV_PROJ_OCCUR:
//             c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
//             return normalize_tv_proj_occur(c);
//         default:
//             return c;
//     }
// }

inline crc *compose_funs(crc *c1, crc *c2) {
	if (c1 == &crc_id) return c2;
	if (c2 == &crc_id) return c1;
	crc *cfun1 = compose(c2->crcdat.two_crc.c1, c1->crcdat.two_crc.c1);
	crc *cfun2 = compose(c1->crcdat.two_crc.c2, c2->crcdat.two_crc.c2);
	if (cfun1 == &crc_id && cfun2 == &crc_id) { //s=>t;;s'=>t' -> id (if s=id and t=id)
		return &crc_id;
	} else {
		return new_fun(cfun1, cfun2);
	}
}

inline crc *compose_lists(crc *c1, crc *c2) {
	if (c1 == &crc_id) return c2;
	if (c2 == &crc_id) return c1;
	crc *clist = compose(c1->crcdat.one_crc, c2->crcdat.one_crc);
	if (clist == &crc_id) {
		return &crc_id;
	} else {
		return new_list(clist);
	}
}

static inline crc *compose_g(crc *c1, crc *c2) {
	if (c2 == &crc_id) return c1; // s;;id -> s
	if (c1 == &crc_id) return c2; // s;;id -> s
	switch(c1->crckind) {
		// case ID: return c2;
		case FUN: return compose_funs(c1, c2);
		case LIST: return compose_lists(c1, c2);
		default: 
			printf("not g is applied to compose_g");
			exit(1);
	}
}

static inline int occur_check(crc* c, const ty *tv) {
	switch (c->crckind) {
		case TV_INJ: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			c = normalize_tv_inj(c);
			if (c->crckind != TV_INJ) goto CASE_SEQ;
			return c->crcdat.seq_tv.ptr.tv == tv;
		}
		case TV_PROJ: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			c = normalize_tv_proj(c);
			if (c->crckind != TV_PROJ) goto CASE_SEQ;
			return c->crcdat.seq_tv.ptr.tv == tv;
		}
		case TV_PROJ_INJ: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			c = normalize_tv_proj_inj(c);
			if (c->crckind != TV_PROJ_INJ) goto CASE_SEQ;
			return c->crcdat.seq_tv.ptr.tv == tv;
		}
		case TV_PROJ_OCCUR: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			c = normalize_tv_proj_occur(c);
			if (c->crckind != TV_PROJ_OCCUR) return 0;
			return c->crcdat.seq_tv.ptr.tv == tv;
		}
		case SEQ_INJ:
		case SEQ_PROJ:
		case SEQ_PROJ_INJ: 
		CASE_SEQ:
			return occur_check(c->crcdat.seq_tv.ptr.s, tv);
		case FUN: return occur_check(c->crcdat.two_crc.c1, tv) || occur_check(c->crcdat.two_crc.c2, tv);
		case LIST: return occur_check(c->crcdat.one_crc, tv);
		default: return 0;
	}
}

inline void dti(const ground_ty g, ty *tv) {
	#ifdef PROFILE
	current_inference++;
	#endif
	switch(g) {
		case G_AR: {
			// printf("DTI : arrow was inferred\n");
			// printf("%p <- X1->X2\n", tv);
			tv->tykind = TYFUN;
			tv->tydat.tyfun.left = newty();
			tv->tydat.tyfun.right = newty();
			return;
		}
		case G_LI: {
			// printf("DTI : list was inferred\n");
			// printf("%p <- [X]\n", tv);
			tv->tykind = TYLIST;
			tv->tydat.tylist = newty();
			return;
		}
		case G_INT: {
			// printf("DTI : int was inferred\n");
			// printf("%p <- int\n", tv);
			*tv = tyint;
			return;
		}
		case G_BOOL: {
			// printf("DTI : bool was inferred\n");
			// printf("%p <- bool\n", tv);
			*tv = tybool;
			return;
		}
		case G_UNIT: {
			// printf("DTI : unit was inferred\n");
			// printf("%p <- unit\n", tv);
			*tv = tyunit;
			return;
		}
		default: {
			printf("got G_NONE");
			exit(1);
		}
	}
}

static crc* internal_compose(crc *c1, crc *c2) {
	// printf("c1: %d, c2: %d\n", c1->crckind, c2->crckind);
	if (c2 == &crc_id) return c1; // s;;id -> s
	// if (c2->crckind == BOT) return c2; 
	  // s;;⊥ は ⊥ ではない (G?p;i;;⊥ -> G?p;⊥)
	if (c1 == &crc_id) return c2; // id;;s -> s

	switch(c1->crckind) {
		// case ID: return c2; 
		case BOT: return c1; // ⊥p;;s -> ⊥p
		case SEQ_PROJ_BOT: return c1; // G?p;⊥q;;s -> G?p;⊥q
		case TV_PROJ_OCCUR: return c1; // ?p⊥Xq;;s -> ?p⊥Xq (normalize will be applied the coercion comes to right side)
		case SEQ_PROJ: // G?p;g;;s
		CASE_SEQ_PROJ: {
			// printf("  c1.g_proj:%d, c1.c:%d\n", c1->g_proj, c1->crcdat.seq_tv.ptr.s->crckind);
			switch(c2->crckind) {
				case TV_INJ: {
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_inj(c2);
				}
				case SEQ_INJ: { // G?p;g1;;g2;H! -> G?p;(g1;;g2);H!
					return new_seq_proj_inj(c1, compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s), c2);
				}
				case BOT: { // G?p;g;;⊥q -> G?p;⊥q
					return new_seq_proj_bot(c1, c2);
				}
				default: { // G?p;g1;;g2 -> G?p;(g1;;g2)
					return new_seq_proj(c1, compose_g(c1->crcdat.seq_tv.ptr.s, c2));
				}
			}
		}
		case SEQ_INJ: 
		CASE_SEQ_INJ: {   // g;G!;;s
			// printf("  c1.c:%d, c1.g_inj:%d\n", c1->crcdat.seq_tv.ptr.s->crckind, c1->g_inj);
			switch(c2->crckind) {
				case SEQ_PROJ: 
				CASE_SEQ_INJ_SEQ_PROJ: { // g;G!;;H?p;g'
					// printf("  c2.g_proj:%d, c2.c2:%d\n", c2->g_proj, c2->crcdat.seq_tv.ptr.s->crckind);
					if (c1->g_inj == c2->g_proj) {   //g;G!;;G?p;g' -> g;;g'
						return compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
					} else {                         // g;G!;;H?p;i -> ⊥p (if G neq H)
						return new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 0);
					}
				}
				case SEQ_PROJ_INJ: 
				CASE_SEQ_INJ_SEQ_PROJ_INJ: { // g;G!;;H?p;g';H'!
					if (c1->g_inj == c2->g_proj) {   // g;G!;;G?p;g';H'! -> (g;;g');H'!
						return new_seq_inj(compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s), c2);
					} else {                         // g;G!;;H?p;g';H'! -> ⊥p (if G neq H)
						return new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 0);
					}
				}
				case SEQ_PROJ_BOT: 
				CASE_SEQ_INJ_SEQ_PROJ_BOT: { // g;G!;;H?p;⊥q
					if (c1->g_inj == c2->g_proj) {   // g;G!;;G?p;⊥q -> ⊥q
						return c2->crcdat.seq_tv.ptr.s;
					} else {                         // g;G!;;H?p;⊥q -> ⊥p (if G neq H)
						return new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 0);
					}
				}
				case TV_PROJ: {										   	// g;G!;;X?p
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj(c2);
					if (c2->crckind != TV_PROJ) goto CASE_SEQ_INJ_SEQ_PROJ;
					if (occur_check(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.tv)) { // g;G!;;X?p -> ⊥p (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1);
					} else { // g;G!;;X?p -> g;;g' (where X?p is normalized to G?p;g')
						dti(c1->g_inj, c2->crcdat.seq_tv.ptr.tv);
						c2 = normalize_tv_proj(c2);
						return compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
					}
				}
				case TV_PROJ_INJ: {									   // g;G!;;?pX!q
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj_inj(c2);
					if (c2->crckind != TV_PROJ_INJ) goto CASE_SEQ_INJ_SEQ_PROJ_INJ;
					if (occur_check(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.tv)) { // g;G!;;?pX!q -> ⊥p (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1);
					} else {  // g;G!;;?pX!q -> (g;;g');G! (where ?pX!q is normalized to G?p;g';G!)
						dti(c1->g_inj, c2->crcdat.seq_tv.ptr.tv);
						c2 = normalize_tv_proj_inj(c2);
						return new_seq_inj(compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s), c2);
					}
				}
				case TV_PROJ_OCCUR: {									   	// g;G!;;?p⊥Xq
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj_occur(c2);
					if (c2->crckind != TV_PROJ_OCCUR) goto CASE_SEQ_INJ_SEQ_PROJ_BOT;
					if (occur_check(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.tv)) { // g;G!;;?p⊥Xq -> ⊥p (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1);
					} else {  // g;G!;;?p⊥Xq -> ⊥q (where ?p⊥Xq is normalized to G?p;⊥q)
						dti(c1->g_inj, c2->crcdat.seq_tv.ptr.tv);
						c2 = normalize_tv_proj_occur(c2);
						return c2->crcdat.seq_tv.ptr.s;
					}
				}
				default: goto COMPOSE_BAD;
			}
		}
		case SEQ_PROJ_INJ: 
		CASE_SEQ_PROJ_INJ: { // G'?p;g;G!;;s
			// printf("  c1.g_proj:%d, c1.c:%d, c1.g_inj:%d\n", c1->g_proj, c1->crcdat.seq_tv.ptr.s->crckind, c1->g_inj);
			switch(c2->crckind) {
				case SEQ_PROJ: 
				CASE_SEQ_PROJ_INJ_SEQ_PROJ: { // G'?p;g;G!;;H?q;g'
					// printf("  c2.g_proj:%d, c2.c:%d\n", c2->g_proj, c2->crcdat.seq_tv.ptr.s->crckind);
					if (c1->g_inj == c2->g_proj) {   // G'?p;g;G!;;G?q;g' -> G'?p;(g;;g')
						return new_seq_proj(c1, compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s));
					} else {                         // G'!p;g;G!;;H?q;g' -> G'!p;⊥q (if G neq H)
						return new_seq_proj_bot(c1, new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 0));
					}
				}
				case SEQ_PROJ_INJ: 
				CASE_SEQ_PROJ_INJ_SEQ_PROJ_INJ: { // G'?p;g;G!;;H?q;g';H'!
					if (c1->g_inj == c2->g_proj) {   // G'?p;g;G!;;G?q;g';H'! -> G'?p;(g;;g');H'!
						return new_seq_proj_inj(c1, compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s), c2);
					} else {                         // G'?p;g;G!;;H?q;g';H'! -> G'?p;⊥q (if G neq H)
						return new_seq_proj_bot(c1, new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 0));
					}
				}
				case SEQ_PROJ_BOT: 
				CASE_SEQ_PROJ_INJ_SEQ_PROJ_BOT: { // G'?p;g;G!;;H?q;⊥r
					if (c1->g_inj == c2->g_proj) {   // G'?p;g;G!;;G?q;⊥r -> G?p;⊥r
						return new_seq_proj_bot(c1, c2->crcdat.seq_tv.ptr.s);
					} else {                         // G'?p;g;G!;;H?q;⊥r -> G'?p;⊥q (if G neq H)
						return new_seq_proj_bot(c1, new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 0));
					}
				}
				case TV_PROJ: {										   	// G'?p;g;G!;;X?q
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj(c2);
					if (c2->crckind != TV_PROJ) goto CASE_SEQ_PROJ_INJ_SEQ_PROJ;
					if (occur_check(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.tv)) { // G'?p;g;G!;;X?q -> G'?p;⊥q (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_seq_proj_bot(c1, new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1));
					} else {   // G'?p;g;G!;;X?q -> G'?p;(g;;g') (where X?q is normalized to G?q;g')
						dti(c1->g_inj, c2->crcdat.seq_tv.ptr.tv);
						c2 = normalize_tv_proj(c2);
						return new_seq_proj(c1, compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s));
					}
				}
				case TV_PROJ_INJ: {									   // G'?p;g;G!;;?qX!r
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj_inj(c2);
					if (c2->crckind != TV_PROJ_INJ) goto CASE_SEQ_PROJ_INJ_SEQ_PROJ_INJ;
					if (occur_check(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.tv)) { // G'?p;g;G!;;?qX!r -> G'?p;⊥q (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_seq_proj_bot(c1, new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1));
					} else {  // G'?p;g;G!;;?qX!r -> G'?p;(g;;g');G! (where ?qX!r is normalized to G?q;g';G!)
						dti(c1->g_inj, c2->crcdat.seq_tv.ptr.tv);
						c2 = normalize_tv_proj_inj(c2);
						return new_seq_proj_inj(c1, compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s), c2);
					}
				}
				case TV_PROJ_OCCUR: {            // G'?p;g;G!;;?q⊥Xr
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj_occur(c2);
					if (c2->crckind != TV_PROJ_OCCUR) goto CASE_SEQ_PROJ_INJ_SEQ_PROJ_BOT;
					if (occur_check(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.tv)) { // G'?p;g;G!;;?q⊥Xr -> G'?p;⊥q (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_seq_proj_bot(c1, new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1));
					} else {  // G'?p;g;G!;;?q⊥Xr -> G'?p;⊥r (where ?q⊥Xr is normalized to G?q;⊥r)
						dti(c1->g_inj, c2->crcdat.seq_tv.ptr.tv);
						c2 = normalize_tv_proj_occur(c2);
						return new_seq_proj_bot(c1, c2->crcdat.seq_tv.ptr.s);
					}
				}
				default: goto COMPOSE_BAD;
			}
		}
		case TV_PROJ: {                                // X?p;;s
			c1->crcdat.seq_tv.ptr.tv = ty_find(c1->crcdat.seq_tv.ptr.tv);
			c1 = normalize_tv_proj(c1);
			if (c1->crckind != TV_PROJ) goto CASE_SEQ_PROJ;
			if (c2->crckind == BOT) { 			// X?p;;⊥q -> ?p⊥Xq
				return new_tv_proj_occur(c1, c2->p_proj, c2->crcdat.seq_tv.rid_proj);
			} else {                            // X?p;;X!q -> ?pX!q
				c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
				return new_tv_proj_inj(c1, c2->crcdat.seq_tv.ptr.tv, c2);
			}
		}
		case TV_INJ: {								    // X!p;;s
			c1->crcdat.seq_tv.ptr.tv = ty_find(c1->crcdat.seq_tv.ptr.tv);
			c1 = normalize_tv_inj(c1);
			if (c1->crckind != TV_INJ) goto CASE_SEQ_INJ;
			switch (c2->crckind) {     
				case SEQ_PROJ: 
				CASE_TV_INJ_SEQ_PROJ: { // X!p;;G?q;g
					// printf("  c2.g_proj:%d, c2.c:%d\n", c2->crcdat.g_proj, c2->crcdat.seq_tv.ptr.s->crckind);
					if (occur_check(c2->crcdat.seq_tv.ptr.s, c1->crcdat.seq_tv.ptr.tv)) { // X!p;;G?q;g -> ⊥q (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1);
					} else { // X!p;;G?q;g -> g';;g (where X!p is normalized to g';G!)
						dti(c2->g_proj, c1->crcdat.seq_tv.ptr.tv);
						c1 = normalize_tv_inj(c1);
						return compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
					}
				}	
				case SEQ_PROJ_INJ: 
				CASE_TV_INJ_SEQ_PROJ_INJ: { // X!p;;G?q;g;G!
					// printf("  c2.g_proj:%d, c2.c:%d, c2.g_inj:%d\n", c2->c_proj, c2->crcdat.seq_tv.ptr.s->crckind, c2->c_inj);
					if (occur_check(c2->crcdat.seq_tv.ptr.s, c1->crcdat.seq_tv.ptr.tv)) { // X!p;;G?q;g;G! -> ⊥q (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1);
					} else { // X!p;;G?q;g;G! -> (g';;g);G! (where X!p is normalized to g';G!)
						dti(c2->g_proj, c1->crcdat.seq_tv.ptr.tv);
						c1 = normalize_tv_inj(c1);
						return new_seq_inj(compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s), c2);
					}
				}	
				case SEQ_PROJ_BOT: 
				CASE_TV_INJ_SEQ_PROJ_BOT: { // X!p;;G?q;⊥r -> ⊥r
					dti(c2->g_proj, c1->crcdat.seq_tv.ptr.tv);
					c1 = normalize_tv_inj(c1);
					return c2->crcdat.seq_tv.ptr.s;
				} 	
				case TV_PROJ: {                                            // X!p;;Y?q
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj(c2);
					if (c2->crckind != TV_PROJ) goto CASE_TV_INJ_SEQ_PROJ;
					ty *tv1 = c1->crcdat.seq_tv.ptr.tv;
					ty *tv2 = c2->crcdat.seq_tv.ptr.tv;
					if (tv1 != tv2) {   // X!p;;Y?q -> id [X:=Y]
						// printf("DTI : tyvar was inferred\n");
						// printf("%p <- %p\n", c1->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv);
						#ifdef PROFILE
						current_inference++;
						#endif
						tv1->tykind = SUBSTITUTED;
						tv1->tydat.tv = tv2;
					}
					return &crc_id; // X!p;;X?q -> id
				}
				case TV_PROJ_INJ: {									    // X!p;;?qY!r
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj_inj(c2);
					if (c2->crckind != TV_PROJ_INJ) goto CASE_TV_INJ_SEQ_PROJ_INJ;
					ty *tv1 = c1->crcdat.seq_tv.ptr.tv;
					ty *tv2 = c2->crcdat.seq_tv.ptr.tv;
					if (tv1 != tv2) {   // X!p;;?qY!r -> Y!r [X:=Y]
						// printf("DTI : tyvar was inferred\n");
						// printf("%p <- %p\n", c1->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv);
						#ifdef PROFILE
						current_inference++;
						#endif
						tv1->tykind = SUBSTITUTED;
						tv1->tydat.tv = tv2;
					}
					return new_tv_inj(tv2, c2); // X!p;;?qX!r -> X!r
				}
				case TV_PROJ_OCCUR: { // X!p;;?q⊥Yr
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj_occur(c2);
					if (c2->crckind != TV_PROJ_OCCUR) goto CASE_TV_INJ_SEQ_PROJ_BOT;
					ty *tv1 = c1->crcdat.seq_tv.ptr.tv;
					ty *tv2 = c2->crcdat.seq_tv.ptr.tv;
					if (tv1 != tv2) {   // X!p;;?q⊥Yr -> ⊥Yr [X:=Y]
						// printf("DTI : tyvar was inferred\n");
						// printf("%p <- %p\n", c1->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv);
						#ifdef PROFILE
						current_inference++;
						#endif
						tv1->tykind = SUBSTITUTED;
						tv1->tydat.tv = tv2;
					}
					return new_bot(c2->p_inj, c2->crcdat.seq_tv.rid_inj, 1); // X!p;;?q⊥Xr -> ⊥r
				}
				default: goto COMPOSE_BAD;
			}
		}
		case TV_PROJ_INJ: {				// ?pX!q;;s
			c1->crcdat.seq_tv.ptr.tv = ty_find(c1->crcdat.seq_tv.ptr.tv);
			c1 = normalize_tv_proj_inj(c1);
			if (c1->crckind != TV_PROJ_INJ) goto CASE_SEQ_PROJ_INJ;
			switch (c2->crckind) {   
				case SEQ_PROJ: 
				CASE_TV_PROJ_INJ_SEQ_PROJ: {  // ?pX!q;;G?r;g 
					// printf("  c2.g_proj:%d, c2.c:%d\n", c2->g_proj, c2->crcdat.seq_tv.ptr.s->crckind);
					if (occur_check(c2->crcdat.seq_tv.ptr.s, c1->crcdat.seq_tv.ptr.tv)) { // ?pX!q;;G?r;g -> ?p⊥Xr (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_tv_proj_occur(c1, c2->p_proj, c2->crcdat.seq_tv.rid_proj);
					} else { // ?pX!q;;G?r;g -> G?p;(g';;g) (where ?pX!q is normalized to G?p;g';G!)
						dti(c2->g_proj, c1->crcdat.seq_tv.ptr.tv);
						c1 = normalize_tv_proj_inj(c1);
						return new_seq_proj(c1, compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s));
					}
				}
				case SEQ_PROJ_INJ: 
				CASE_TV_PROJ_INJ_SEQ_PROJ_INJ: {  // ?pX!q;;G?r;g;G!
					// printf("  c2.g_proj:%d, c2.c:%d, c2.g_inj:%d\n", c2->g_proj, c2->crcdat.seq_tv.ptr.s->crckind, c2->g_inj);
					if (occur_check(c2->crcdat.seq_tv.ptr.s, c1->crcdat.seq_tv.ptr.tv)) { // ?pX!q;;G?r;g;G! -> ?p⊥Xr (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_tv_proj_occur(c1, c2->p_proj, c2->crcdat.seq_tv.rid_proj);
					} else { // ?pX!q;;G?r;g;G! -> G?p;(g';;g);G! (where ?pX!q is normalized to G?p;g';G!)
						dti(c2->g_proj, c1->crcdat.seq_tv.ptr.tv);
						c1 = normalize_tv_proj_inj(c1);
						return new_seq_proj_inj(c1, compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s), c2);
					}
				}
				case SEQ_PROJ_BOT: 
				CASE_TV_PROJ_INJ_SEQ_PROJ_BOT: { // ?pX!q;;G?p';⊥q' -> G?p;⊥q'
					dti(c2->g_proj, c1->crcdat.seq_tv.ptr.tv);
					c1 = normalize_tv_proj_inj(c1);
					return new_seq_proj_bot(c1, c2->crcdat.seq_tv.ptr.s);
				}   
				case TV_PROJ: {                                            // ?pX!q;;Y?r
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj(c2);
					if (c2->crckind != TV_PROJ) goto CASE_TV_PROJ_INJ_SEQ_PROJ;
					ty *tv1 = c1->crcdat.seq_tv.ptr.tv;
					ty *tv2 = c2->crcdat.seq_tv.ptr.tv;
					if (tv1 != tv2) { // ?pX!q;;Y?r -> Y?p [X:=Y]
						// printf("DTI : tyvar was inferred\n");
						// printf("%p <- %p\n", c1->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv);
						#ifdef PROFILE
						current_inference++;
						#endif
						tv1->tykind = SUBSTITUTED;
						tv1->tydat.tv = tv2;
					}
					return new_tv_proj(c1, tv2); // ?pX!q;;X?r -> X?p
				}
				case TV_PROJ_INJ: {									    // ?pX!q;;?p'Y!q'
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj_inj(c2);
					if (c2->crckind != TV_PROJ_INJ) goto CASE_TV_PROJ_INJ_SEQ_PROJ_INJ;
					ty *tv1 = c1->crcdat.seq_tv.ptr.tv;
					ty *tv2 = c2->crcdat.seq_tv.ptr.tv;
					if (tv1 != tv2) { // ?pX!q;;?p'Y!q' -> ?pY!q' [X:=Y]
						// printf("DTI : tyvar was inferred\n");
						// printf("%p <- %p\n", c1->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv);
						#ifdef PROFILE
						current_inference++;
						#endif
						tv1->tykind = SUBSTITUTED;
						tv1->tydat.tv = tv2;
					}
					return new_tv_proj_inj(c1, tv2, c2); // ?pX!q;;?p'X!q' -> ?pX!q'
				}
				case TV_PROJ_OCCUR: {                                            // ?pX!q;;?p'⊥Yq'
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj_occur(c2);
					if (c2->crckind != TV_PROJ_OCCUR) goto CASE_TV_PROJ_INJ_SEQ_PROJ_BOT;
					ty *tv1 = c1->crcdat.seq_tv.ptr.tv;
					ty *tv2 = c2->crcdat.seq_tv.ptr.tv;
					if (tv1 != tv2) { // ?pX!q;;?p'⊥Yq' -> ?p⊥Yq' [X:=Y]
						// printf("DTI : tyvar was inferred\n");
						// printf("%p <- %p\n", c1->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv);
						#ifdef PROFILE
						current_inference++;
						#endif
						tv1->tykind = SUBSTITUTED;
						tv1->tydat.tv = tv2;
					}
					return new_tv_proj_occur(c1, c2->p_inj, c2->crcdat.seq_tv.rid_inj); // ?pX!q;;?p'⊥Xq' -> ?p⊥Xq'
				}
				default: goto COMPOSE_BAD;
			}
		}
		case FUN: {
			switch (c2->crckind) {
				case BOT: return c2; // g;;⊥p -> ⊥p
				case TV_INJ: {
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_inj_fun(c2);
				}
				case SEQ_INJ: { 						// g;;h;G! -> (g;;h);G!
					// printf("  c2.c:%d, c2.g_inj:%d\n", c2->crcdat.seq_tv.ptr.s->crckind, c2->g_inj);
					return new_seq_inj(compose_funs(c1, c2->crcdat.seq_tv.ptr.s), c2);
				}
				case FUN: return compose_funs(c1, c2);  // s=>t;;s'=>t' -> s';;s=>t;;t'
				default: goto COMPOSE_BAD;
			}
		}
		case LIST: {
			switch(c2->crckind) {
				case BOT: return c2; // g;;⊥p -> ⊥p
				case TV_INJ: {
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_inj_list(c2);
				}
				case SEQ_INJ: { 						// g;;h;G! -> (g;;h);G!
					// printf("  c2.c:%d, c2.g_inj:%d\n", c2->crcdat.seq_tv.ptr.s->crckind, c2->g_inj);
					return new_seq_inj(compose_lists(c1, c2->crcdat.seq_tv.ptr.s), c2);
				}
				case LIST: return compose_lists(c1, c2);
				default: goto COMPOSE_BAD;
			}
		}
		default: goto COMPOSE_BAD;
	}

	COMPOSE_BAD: 
	printf("compose bad. c1: %d, c2: %d\n", c1->crckind, c2->crckind);
	exit(1);
}


crc* compose(crc *c1, crc *c2) {
	#ifdef PROFILE
	current_compose++;
	#endif //PROFILE
	#ifdef HASH
    if (c2 == &crc_id) return c1;
    if (c1 == &crc_id) return c2;

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

#endif