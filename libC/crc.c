#if !defined(CAST) && !defined(STATIC)

#include <stdio.h>
#include <stdlib.h> 
#include <gc.h>

#include "crc.h"
#include "capp.h"
#include "ty.h"

crc crc_id = { .crckind = ID };
crc crc_inj_INT = { .crckind = SEQ_INJ, .g_inj = G_INT, .crcdat = { .seq_tv = { .ptr = { .s = &crc_id } } } };
crc crc_inj_BOOL = { .crckind = SEQ_INJ, .g_inj = G_BOOL, .crcdat = { .seq_tv = { .ptr = { .s = &crc_id } } } };
crc crc_inj_UNIT = { .crckind = SEQ_INJ, .g_inj = G_UNIT, .crcdat = { .seq_tv = { .ptr = { .s = &crc_id } } } };

static inline crc *new_bot(const uint8_t p, const uint32_t rid, const uint8_t is_occur) {
	crc *retc = (crc*)GC_MALLOC(sizeof(crc));
	retc->crckind = BOT;
	retc->botkind = is_occur;
	retc->p_proj = p;
	retc->crcdat.seq_tv.rid_proj = rid;
	return retc;
}

static inline crc* new_seq_proj(const crc *base_proj, crc *s_new) {
    crc *c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = SEQ_PROJ;
    c->g_proj = base_proj->g_proj;
    c->p_proj = base_proj->p_proj;
    c->crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    c->crcdat.seq_tv.ptr.s = s_new;
    return c;
}

static inline crc* new_seq_inj(crc *s_new, const crc *base_inj) {
    crc *c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = SEQ_INJ;
    c->g_inj = base_inj->g_inj;
    c->crcdat.seq_tv.ptr.s = s_new;
    return c;
}

static inline crc* new_seq_proj_inj(const crc *base_proj, crc *s_new, const crc *base_inj) {
    crc *c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = SEQ_PROJ_INJ;
    c->g_proj = base_proj->g_proj;
    c->p_proj = base_proj->p_proj;
    c->g_inj = base_inj->g_inj;
    c->crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    c->crcdat.seq_tv.ptr.s = s_new;
    return c;
}

static inline crc *new_seq_proj_bot(const crc *base_proj, crc *bot) {
	crc *retc = (crc*)GC_MALLOC(sizeof(crc));
	retc->crckind = SEQ_PROJ_BOT;
	retc->g_proj = base_proj->g_proj;
	retc->p_proj = base_proj->p_proj;
	retc->crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
	retc->crcdat.seq_tv.ptr.s = bot;
	return retc;
}

static inline crc* new_tv_proj(const crc *base_proj, ty *tv) {
    crc *c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = TV_PROJ;
    c->p_proj = base_proj->p_proj;
    c->crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    c->crcdat.seq_tv.ptr.tv = tv;
    return c;
}

static inline crc* new_tv_inj(ty *tv, const crc *base_inj) {
    crc *c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = TV_INJ;
	c->p_inj = base_inj->p_inj;
    c->crcdat.seq_tv.rid_inj = base_inj->crcdat.seq_tv.rid_inj;
	c->crcdat.seq_tv.ptr.tv = tv;
    return c;
}

static inline crc* new_tv_proj_inj(const crc *base_proj, ty *tv, const crc *base_inj) {
    crc *c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = TV_PROJ_INJ;
    c->p_proj = base_proj->p_proj;
    c->crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
	c->p_inj = base_inj->p_inj;
    c->crcdat.seq_tv.rid_inj = base_inj->crcdat.seq_tv.rid_inj;
    c->crcdat.seq_tv.ptr.tv = tv;
    return c;
}

static inline crc* new_tv_proj_occur(const crc* base_proj, const uint8_t bot_p, const uint32_t bot_rid) {
	crc *c = (crc*)GC_MALLOC(sizeof(crc));
	c->crckind = TV_PROJ_OCCUR;
	c->p_proj = base_proj->p_proj;
	c->p_inj = bot_p;
    c->crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    c->crcdat.seq_tv.rid_inj = bot_rid;
	c->crcdat.seq_tv.ptr.tv = base_proj->crcdat.seq_tv.ptr.tv;
	return c;
}

static inline void normalize_tv_inj_int(crc *c) {
	*c = crc_inj_INT;
	return;
}

static inline void normalize_tv_inj_bool(crc *c) {
	*c = crc_inj_BOOL;
	return;
}

static inline void normalize_tv_inj_unit(crc *c) {
	*c = crc_inj_UNIT;
	return;
}

static inline void normalize_tv_inj_fun(crc *c) {
	crc *cs = (crc*)GC_MALLOC(sizeof(crc) * 3);
	crc *cfun1 = &cs[0];
	crc *cfun2 = &cs[1];
	crc *cfun = &cs[2];
	cfun1->crckind = TV_PROJ;
	cfun1->p_proj = c->p_inj ^ 1;
	cfun1->crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_inj;
	cfun1->crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.left;
	cfun2->crckind = TV_INJ;
	cfun2->p_proj = c->p_inj;
	cfun2->crcdat.seq_tv.rid_inj = c->crcdat.seq_tv.rid_inj;
	cfun2->crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.right;
	cfun->crckind = FUN;
	cfun->crcdat.two_crc.c1 = cfun1;
	cfun->crcdat.two_crc.c2 = cfun2;
	c->crckind = SEQ_INJ;
	c->g_inj = G_AR;
	c->crcdat.seq_tv.ptr.s = cfun;
	return;
}

static inline void normalize_tv_inj_list(crc* c) {
	crc *cs = (crc*)GC_MALLOC(sizeof(crc) * 2);
	crc *clist_ = &cs[0];
	crc *clist = &cs[1];
	clist_->crckind = TV_INJ;
	clist_->p_inj = c->p_inj;
	clist_->crcdat.seq_tv.rid_inj = c->crcdat.seq_tv.rid_inj;
	clist_->crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tylist;
	clist->crckind = LIST;
	clist->crcdat.one_crc = clist_;
	c->crckind = SEQ_INJ;
	c->g_inj = G_LI;
	c->crcdat.seq_tv.ptr.s = clist;
	return;
}

static inline void normalize_tv_inj(crc *c) {
	switch(c->crcdat.seq_tv.ptr.tv->tykind) {
		case BASE_INT: return normalize_tv_inj_int(c); // X! [X:=int] -> id;int!
		case BASE_BOOL: return normalize_tv_inj_bool(c);
		case BASE_UNIT: return normalize_tv_inj_unit(c);
		case TYFUN: return normalize_tv_inj_fun(c);         // X! [X:=X1=>X2] -> X1?p=>X2!;(★→★)!	
		case TYLIST: return normalize_tv_inj_list(c);         // X! [X:=[X1]] -> [X1!];[★]!
		default: return;
	}
}

static inline void normalize_tv_proj_int(crc *c) {
	c->crckind = SEQ_PROJ;
	c->g_proj = G_INT;
	c->crcdat.seq_tv.ptr.s = &crc_id;
	return;
}

static inline void normalize_tv_proj_bool(crc *c) {
	c->crckind = SEQ_PROJ;
	c->g_proj = G_BOOL;
	c->crcdat.seq_tv.ptr.s = &crc_id;
	return;
}

static inline void normalize_tv_proj_unit(crc *c) {
	c->crckind = SEQ_PROJ;
	c->g_proj = G_UNIT;
	c->crcdat.seq_tv.ptr.s = &crc_id;
	return;
}

static inline void normalize_tv_proj_fun(crc *c) {
	crc *cs = (crc*)GC_MALLOC(sizeof(crc) * 3);
	crc *cfun1 = &cs[0];
	crc *cfun2 = &cs[1];
	crc *cfun = &cs[2];
	cfun1->crckind = TV_INJ;
	cfun1->p_inj = c->p_proj ^ 1;
	cfun1->crcdat.seq_tv.rid_inj = c->crcdat.seq_tv.rid_proj;
	cfun1->crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.left;
	cfun2->crckind = TV_PROJ;
	cfun2->p_proj = c->p_proj;
	cfun2->crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
	cfun2->crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.right;
	cfun->crckind = FUN;
	cfun->crcdat.two_crc.c1 = cfun1;
	cfun->crcdat.two_crc.c2 = cfun2;
	c->crckind = SEQ_PROJ;
	c->g_proj = G_AR;
	c->crcdat.seq_tv.ptr.s = cfun;
	return;
}

static inline void normalize_tv_proj_list(crc *c) {
	crc *cs = (crc*)GC_MALLOC(sizeof(crc) * 2);
	crc *clist_ = &cs[0];
	crc *clist = &cs[1];
	clist_->crckind = TV_PROJ;
	clist_->p_proj = c->p_proj;
	clist_->crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
	clist_->crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tylist;
	clist->crckind = LIST;
	clist->crcdat.one_crc = clist_;
	c->crckind = SEQ_PROJ;
	c->g_proj = G_LI;
	c->crcdat.seq_tv.ptr.s = clist;
	return;
}

static inline void normalize_tv_proj(crc *c) {
	switch(c->crcdat.seq_tv.ptr.tv->tykind) {
		case BASE_INT: return normalize_tv_proj_int(c);				// X?p [X:=int] -> int?p;id
		case BASE_BOOL: return normalize_tv_proj_bool(c);
		case BASE_UNIT: return normalize_tv_proj_unit(c);
		case TYFUN: return normalize_tv_proj_fun(c);       // X?p [X:=X1=>X2] -> (★→★)?p;X1!=>X2?p
		case TYLIST: return normalize_tv_proj_list(c);        // X?p [X:=[X1]] -> [★]?p;[X1?p]
		default: return;
	}
}

static inline void normalize_tv_proj_inj_int(crc *c) {
	c->crckind = SEQ_PROJ_INJ;
	c->g_proj = G_INT;
	c->g_inj = G_INT;
	c->crcdat.seq_tv.ptr.s = &crc_id;
	return;
}

static inline void normalize_tv_proj_inj_bool(crc *c) {
	c->crckind = SEQ_PROJ_INJ;
	c->g_proj = G_BOOL;
	c->g_inj = G_BOOL;
	c->crcdat.seq_tv.ptr.s = &crc_id;
	return;
}

static inline void normalize_tv_proj_inj_unit(crc *c) {
	c->crckind = SEQ_PROJ_INJ;
	c->g_proj = G_UNIT;
	c->g_inj = G_UNIT;
	c->crcdat.seq_tv.ptr.s = &crc_id;
	return;
}

static inline void normalize_tv_proj_inj_fun(crc *c) {
	ty *t1 = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.left;
	ty *t2 = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.right;
	crc *cs = (crc*)GC_MALLOC(sizeof(crc) * 3);
	crc *cfun1 = &cs[0];
	crc *cfun2 = &cs[1];
	crc *cfun = &cs[2];
	cfun1->crckind = TV_PROJ_INJ;
	cfun1->p_proj = c->p_inj ^ 1;
	cfun1->p_inj = c->p_proj ^ 1;
	cfun1->crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_inj;
	cfun1->crcdat.seq_tv.rid_inj = c->crcdat.seq_tv.rid_proj;
	cfun1->crcdat.seq_tv.ptr.tv = t1;
	cfun2->crckind = TV_PROJ_INJ;
	cfun2->p_proj = c->p_proj;
	cfun2->p_inj = c->p_inj;
	cfun2->crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
	cfun2->crcdat.seq_tv.rid_inj = c->crcdat.seq_tv.rid_inj;
	cfun2->crcdat.seq_tv.ptr.tv = t2;
	cfun->crckind = FUN;
	cfun->crcdat.two_crc.c1 = cfun1;
	cfun->crcdat.two_crc.c2 = cfun2;
	c->crckind = SEQ_PROJ_INJ;
	c->g_inj = G_AR;
	c->g_proj = G_AR;
	c->crcdat.seq_tv.ptr.s = cfun;
	return;
}

static inline void normalize_tv_proj_inj_list(crc *c) {
	ty *t = c->crcdat.seq_tv.ptr.tv->tydat.tylist;
	crc *cs = (crc*)GC_MALLOC(sizeof(crc) * 2);
	crc *clist_ = &cs[0];
	crc *clist = &cs[1];
	clist_->crckind = TV_PROJ_INJ;
	clist_->p_proj = c->p_proj;
	clist_->p_inj = c->p_inj;
	clist_->crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_proj;
	clist_->crcdat.seq_tv.rid_inj = c->crcdat.seq_tv.rid_inj;
	clist_->crcdat.seq_tv.ptr.tv = t;
	clist->crckind = LIST;
	clist->crcdat.one_crc = clist_;
	c->crckind = SEQ_PROJ_INJ;
	c->g_inj = G_LI;
	c->g_proj = G_LI;
	c->crcdat.seq_tv.ptr.s = clist;
	return;
}

static inline void normalize_tv_proj_inj(crc *c) {
	switch(c->crcdat.seq_tv.ptr.tv->tykind) {
		case BASE_INT: return normalize_tv_proj_inj_int(c);                    // ?pX!q [X:=int] -> int?p;id;int!
		case BASE_BOOL: return normalize_tv_proj_inj_bool(c);
		case BASE_UNIT: return normalize_tv_proj_inj_unit(c);
		case TYFUN: return normalize_tv_proj_inj_fun(c);  				// ?pX!q [X:=X1=>X2] -> (★→★)?p;(?-qX1!-p=>?pX2!q);(★→★)!
		case TYLIST: return normalize_tv_proj_inj_list(c);				// ?pX!q [X:=[X1]] -> [★]?p;[?pX1!q];[★]!
		default: return;
	}
}

static inline void normalize_tv_proj_occur_int(crc *c) {
	c->crckind = SEQ_PROJ_BOT;
	c->g_proj = G_INT;
	crc *bot = new_bot(c->p_proj, c->crcdat.seq_tv.rid_proj, 1);
	bot->p_proj = c->p_inj;
	bot->crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_inj;
	c->crcdat.seq_tv.ptr.s = bot;
	return;
}

static inline void normalize_tv_proj_occur_bool(crc *c) {
	c->crckind = SEQ_PROJ_BOT;
	c->g_proj = G_BOOL;
	crc *bot = new_bot(c->p_proj, c->crcdat.seq_tv.rid_proj, 1);
	bot->p_proj = c->p_inj;
	bot->crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_inj;
	c->crcdat.seq_tv.ptr.s = bot;
	return;
}

static inline void normalize_tv_proj_occur_unit(crc *c) {
	c->crckind = SEQ_PROJ_BOT;
	c->g_proj = G_UNIT;
	crc *bot = new_bot(c->p_proj, c->crcdat.seq_tv.rid_proj, 1);
	bot->p_proj = c->p_inj;
	bot->crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_inj;
	c->crcdat.seq_tv.ptr.s = bot;
	return;
}

static inline void normalize_tv_proj_occur_fun(crc *c) {
	c->crckind = SEQ_PROJ_BOT;
	c->g_proj = G_AR;
	crc *bot = new_bot(c->p_proj, c->crcdat.seq_tv.rid_proj, 1);
	bot->p_proj = c->p_inj;
	bot->crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_inj;
	c->crcdat.seq_tv.ptr.s = bot;
	return;
}

static inline void normalize_tv_proj_occur_list(crc *c) {
	c->crckind = SEQ_PROJ_BOT;
	c->g_proj = G_LI;
	crc *bot = new_bot(c->p_proj, c->crcdat.seq_tv.rid_proj, 1);
	bot->p_proj = c->p_inj;
	bot->crcdat.seq_tv.rid_proj = c->crcdat.seq_tv.rid_inj;
	c->crcdat.seq_tv.ptr.s = bot;
	return;
}

static inline void normalize_tv_proj_occur(crc *c) {
	switch(c->crcdat.seq_tv.ptr.tv->tykind) {
		case BASE_INT: return normalize_tv_proj_occur_int(c);                    // ?p⊥Xq [X:=int] -> int?p;⊥q
		case BASE_BOOL: return normalize_tv_proj_occur_bool(c);
		case BASE_UNIT: return normalize_tv_proj_occur_unit(c);
		case TYFUN: return normalize_tv_proj_occur_fun(c);  				// ?p⊥Xq [X:=X1=>X2] -> (★→★)?p;⊥q
		case TYLIST: return normalize_tv_proj_occur_list(c);				// ?p⊥Xq [X:=[X1]] -> [★]?p;⊥q
		default: return;
	}
}

void normalize_crc(crc *c) {
	switch(c->crckind) {
		case TV_INJ: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			return normalize_tv_inj(c);
		}
		case TV_PROJ: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			return normalize_tv_proj(c);
		}
		case TV_PROJ_INJ: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			return normalize_tv_proj_inj(c);
		}
		case TV_PROJ_OCCUR: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			return normalize_tv_proj_occur(c);
		}
		default:
			printf("normalize_crc bad. crckind: %d", c->crckind);
			exit(1);
	}
}

static inline crc *compose_funs(crc *c1, crc *c2) {
	if (c1->crckind == ID) return c2;
	if (c2->crckind == ID) return c1;
	crc *cfun1 = compose(c2->crcdat.two_crc.c1, c1->crcdat.two_crc.c1);
	crc *cfun2 = compose(c1->crcdat.two_crc.c2, c2->crcdat.two_crc.c2);
	if (cfun1->crckind == ID && cfun2->crckind == ID) { //s=>t;;s'=>t' -> id (if s=id and t=id)
		return &crc_id;
	} else {
		crc *retc = (crc*)GC_MALLOC(sizeof(crc));
		retc->crckind = FUN;
		retc->crcdat.two_crc.c1 = cfun1;
		retc->crcdat.two_crc.c2 = cfun2;
		return retc;
	}
}

static inline crc *compose_lists(crc *c1, crc *c2) {
	if (c1->crckind == ID) return c2;
	if (c2->crckind == ID) return c1;
	crc *clist = compose(c1->crcdat.one_crc, c2->crcdat.one_crc);
	if (clist->crckind == ID) {
		return &crc_id;
	} else {
		crc *retc = (crc*)GC_MALLOC(sizeof(crc));
		retc->crckind = LIST;
		retc->crcdat.one_crc = clist;
		return retc;
	}
}

static inline crc *compose_g(crc *c1, crc *c2) {
	if (c2->crckind == ID) return c1; // s;;id -> s
	switch(c1->crckind) {
		case ID: return c2;
		case FUN: return compose_funs(c1, c2);
		case LIST: return compose_lists(c1, c2);
	}
}

static inline int occur_check(crc* c, const ty *tv) {
	switch (c->crckind) {
		case TV_INJ: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			normalize_tv_inj(c);
			if (c->crckind != TV_INJ) goto CASE_SEQ;
			return c->crcdat.seq_tv.ptr.tv == tv;
		}
		case TV_PROJ: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			normalize_tv_proj(c);
			if (c->crckind != TV_PROJ) goto CASE_SEQ;
			return c->crcdat.seq_tv.ptr.tv == tv;
		}
		case TV_PROJ_INJ: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			normalize_tv_proj_inj(c);
			if (c->crckind != TV_PROJ_INJ) goto CASE_SEQ;
			return c->crcdat.seq_tv.ptr.tv == tv;
		}
		case TV_PROJ_OCCUR: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			normalize_tv_proj_occur(c);
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

static inline void dti(const ground_ty g, ty *tv) {
	#ifdef PROFILE
	current_inference++;
	#endif
	switch(g) {
		case G_AR: {
			// printf("DTI : arrow was inferred\n");
			tv->tykind = TYFUN;
			tv->tydat.tyfun.left = newty();
			tv->tydat.tyfun.right = newty();
			return;
		}
		case G_LI: {
			// printf("DTI : list was inferred\n");
			tv->tykind = TYLIST;
			tv->tydat.tylist = newty();
			return;
		}
		case G_INT: {
			// printf("DTI : int was inferred\n");
			// printf("%p <- int\n", c2->crcdat.seq_tv.ptr.tv);
			*tv = tyint;
			return;
		}
		case G_BOOL: {
			// printf("DTI : bool was inferred\n");
			// printf("%p <- bool\n", c2->crcdat.seq_tv.ptr.tv);
			*tv = tybool;
			return;
		}
		case G_UNIT: {
			// printf("DTI : unit was inferred\n");
			// printf("%p <- unit\n", c2->crcdat.seq_tv.ptr.tv);
			*tv = tyunit;
			return;
		}
	}
}

crc* compose(crc *c1, crc *c2) {
	// printf("c1: %d, c2: %d\n", c1->crckind, c2->crckind);
	if (c2->crckind == ID) return c1; // s;;id -> s
	// if (c2->crckind == BOT) return c2; 
	  // s;;⊥ は ⊥ ではない (G?p;i;;⊥ -> G?p;⊥)

	switch(c1->crckind) {
		case ID: return c2; // id;;s -> s
		case BOT: return c1; // ⊥p;;s -> ⊥p
		case SEQ_PROJ_BOT: return c1; // G?p;⊥q;;s -> G?p;⊥q
		case TV_PROJ_OCCUR: return c1; // ?p⊥Xq;;s -> ?p⊥Xq (normalize will be applied the coercion comes to right side)
		case SEQ_PROJ: // G?p;g;;s
		CASE_SEQ_PROJ: {
			// printf("  c1.g_proj:%d, c1.c:%d\n", c1->g_proj, c1->crcdat.seq_tv.ptr.s->crckind);
			switch(c2->crckind) {
				case TV_INJ: {
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					normalize_tv_inj(c2);
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
					normalize_tv_proj(c2);
					if (c2->crckind != TV_PROJ) goto CASE_SEQ_INJ_SEQ_PROJ;
					if (occur_check(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.tv)) { // g;G!;;X?p -> ⊥p (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1);
					} else { // g;G!;;X?p -> g;;g' (where X?p is normalized to G?p;g')
						dti(c1->g_inj, c2->crcdat.seq_tv.ptr.tv);
						normalize_tv_proj(c2);
						return compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
					}
				}
				case TV_PROJ_INJ: {									   // g;G!;;?pX!q
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					normalize_tv_proj_inj(c2);
					if (c2->crckind != TV_PROJ_INJ) goto CASE_SEQ_INJ_SEQ_PROJ_INJ;
					if (occur_check(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.tv)) { // g;G!;;?pX!q -> ⊥p (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1);
					} else {  // g;G!;;?pX!q -> (g;;g');G! (where ?pX!q is normalized to G?p;g';G!)
						dti(c1->g_inj, c2->crcdat.seq_tv.ptr.tv);
						normalize_tv_proj_inj(c2);
						return new_seq_inj(compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s), c2);
					}
				}
				case TV_PROJ_OCCUR: {									   	// g;G!;;?p⊥Xq
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					normalize_tv_proj_occur(c2);
					if (c2->crckind != TV_PROJ_OCCUR) goto CASE_SEQ_INJ_SEQ_PROJ_BOT;
					if (occur_check(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.tv)) { // g;G!;;?p⊥Xq -> ⊥p (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1);
					} else {  // g;G!;;?p⊥Xq -> ⊥q (where ?p⊥Xq is normalized to G?p;⊥q)
						dti(c1->g_inj, c2->crcdat.seq_tv.ptr.tv);
						normalize_tv_proj_occur(c2);
						return c2->crcdat.seq_tv.ptr.s;
					}
				}
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
					normalize_tv_proj(c2);
					if (c2->crckind != TV_PROJ) goto CASE_SEQ_PROJ_INJ_SEQ_PROJ;
					if (occur_check(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.tv)) { // G'?p;g;G!;;X?q -> G'?p;⊥q (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_seq_proj_bot(c1, new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1));
					} else {   // G'?p;g;G!;;X?q -> G'?p;(g;;g') (where X?q is normalized to G?q;g')
						dti(c1->g_inj, c2->crcdat.seq_tv.ptr.tv);
						normalize_tv_proj(c2);
						return new_seq_proj(c1, compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s));
					}
				}
				case TV_PROJ_INJ: {									   // G'?p;g;G!;;?qX!r
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					normalize_tv_proj_inj(c2);
					if (c2->crckind != TV_PROJ_INJ) goto CASE_SEQ_PROJ_INJ_SEQ_PROJ_INJ;
					if (occur_check(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.tv)) { // G'?p;g;G!;;?qX!r -> G'?p;⊥q (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_seq_proj_bot(c1, new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1));
					} else {  // G'?p;g;G!;;?qX!r -> G'?p;(g;;g');G! (where ?qX!r is normalized to G?q;g';G!)
						dti(c1->g_inj, c2->crcdat.seq_tv.ptr.tv);
						normalize_tv_proj_inj(c2);
						return new_seq_proj_inj(c1, compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s), c2);
					}
				}
				case TV_PROJ_OCCUR: {            // G'?p;g;G!;;?q⊥Xr
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					normalize_tv_proj_occur(c2);
					if (c2->crckind != TV_PROJ_OCCUR) goto CASE_SEQ_PROJ_INJ_SEQ_PROJ_BOT;
					if (occur_check(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.tv)) { // G'?p;g;G!;;?q⊥Xr -> G'?p;⊥q (when X occurs in g)
						// blame(c2->crcdat.seq_tv.rid_proj, c2->p_proj);
						// exit(1);
						return new_seq_proj_bot(c1, new_bot(c2->p_proj, c2->crcdat.seq_tv.rid_proj, 1));
					} else {  // G'?p;g;G!;;?q⊥Xr -> G'?p;⊥r (where ?q⊥Xr is normalized to G?q;⊥r)
						dti(c1->g_inj, c2->crcdat.seq_tv.ptr.tv);
						normalize_tv_proj_occur(c2);
						return new_seq_proj_bot(c1, c2->crcdat.seq_tv.ptr.s);
					}
				}
			}
		}
		case TV_PROJ: {                                // X?p;;s
			c1->crcdat.seq_tv.ptr.tv = ty_find(c1->crcdat.seq_tv.ptr.tv);
			normalize_tv_proj(c1);
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
			normalize_tv_inj(c1);
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
						normalize_tv_inj(c1);
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
						normalize_tv_inj(c1);
						return new_seq_inj(compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s), c2);
					}
				}	
				case SEQ_PROJ_BOT: 
				CASE_TV_INJ_SEQ_PROJ_BOT: { // X!p;;G?q;⊥r -> ⊥r
					dti(c2->g_proj, c1->crcdat.seq_tv.ptr.tv);
					normalize_tv_inj(c1);
					return c2->crcdat.seq_tv.ptr.s;
				} 	
				case TV_PROJ: {                                            // X!p;;Y?q
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					normalize_tv_proj(c2);
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
					normalize_tv_proj_inj(c2);
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
					normalize_tv_proj_occur(c2);
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
			}
		}
		case TV_PROJ_INJ: {				// ?pX!q;;s
			c1->crcdat.seq_tv.ptr.tv = ty_find(c1->crcdat.seq_tv.ptr.tv);
			normalize_tv_proj_inj(c1);
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
						normalize_tv_proj_inj(c1);
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
						normalize_tv_proj_inj(c1);
						return new_seq_proj_inj(c1, compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s), c2);
					}
				}
				case SEQ_PROJ_BOT: 
				CASE_TV_PROJ_INJ_SEQ_PROJ_BOT: { // ?pX!q;;G?p';⊥q' -> G?p;⊥q'
					dti(c2->g_proj, c1->crcdat.seq_tv.ptr.tv);
					normalize_tv_proj_inj(c1);
					return new_seq_proj_bot(c1, c2->crcdat.seq_tv.ptr.s);
				}   
				case TV_PROJ: {                                            // ?pX!q;;Y?r
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					normalize_tv_proj(c2);
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
					normalize_tv_proj_inj(c2);
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
					normalize_tv_proj_occur(c2);
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
			}
		}
		case FUN: {
			switch (c2->crckind) {
				case BOT: return c2; // g;;⊥p -> ⊥p
				case TV_INJ: {
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					normalize_tv_inj_fun(c2);
				}
				case SEQ_INJ: { 						// g;;h;G! -> (g;;h);G!
					// printf("  c2.c:%d, c2.g_inj:%d\n", c2->crcdat.seq_tv.ptr.s->crckind, c2->g_inj);
					return new_seq_inj(compose_funs(c1, c2->crcdat.seq_tv.ptr.s), c2);
				}
				case FUN: return compose_funs(c1, c2);  // s=>t;;s'=>t' -> s';;s=>t;;t'
			}
		}
		case LIST: {
			switch(c2->crckind) {
				case BOT: return c2; // g;;⊥p -> ⊥p
				case TV_INJ: {
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					normalize_tv_inj_list(c2);
				}
				case SEQ_INJ: { 						// g;;h;G! -> (g;;h);G!
					// printf("  c2.c:%d, c2.g_inj:%d\n", c2->crcdat.seq_tv.ptr.s->crckind, c2->g_inj);
					return new_seq_inj(compose_lists(c1, c2->crcdat.seq_tv.ptr.s), c2);
				}
				case LIST: return compose_lists(c1, c2);
			}
		}
	}
	printf("compose bad. c1: %d, c2: %d\n", c1->crckind, c2->crckind);
	exit(1);
}

#endif