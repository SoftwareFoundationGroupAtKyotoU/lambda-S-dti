#ifndef CAST

#include <stdio.h>
#include <stdlib.h> 
#include <gc.h>

#include "crc.h"
#include "ty.h"

crc crc_id = { .crckind = ID };
crc crc_inj_INT = { .crckind = SEQ_INJ, .g_inj = G_INT, .crcdat = { .seq_tv = { .ptr = { .s = &crc_id } } } };
crc crc_inj_BOOL = { .crckind = SEQ_INJ, .g_inj = G_BOOL, .crcdat = { .seq_tv = { .ptr = { .s = &crc_id } } } };
crc crc_inj_UNIT = { .crckind = SEQ_INJ, .g_inj = G_UNIT, .crcdat = { .seq_tv = { .ptr = { .s = &crc_id } } } };

static inline crc *normalize_tv_inj_int(crc *c) {
	*c = crc_inj_INT;
	return c;
}

static inline crc *normalize_tv_inj_bool(crc *c) {
	*c = crc_inj_BOOL;
	return c;
}

static inline crc *normalize_tv_inj_unit(crc *c) {
	*c = crc_inj_UNIT;
	return c;
}

static inline crc *normalize_tv_inj_fun(crc *c) {
	crc *cs = (crc*)GC_MALLOC(sizeof(crc) * 3);
	crc *cfun1 = &cs[0];
	crc *cfun2 = &cs[1];
	crc *cfun = &cs[2];
	cfun1->crckind = TV_PROJ;
	cfun1->crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.left;
	// cfun1->r_p = 
	cfun2->crckind = TV_INJ;
	cfun2->crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.right;
	cfun->crckind = FUN;
	cfun->crcdat.two_crc.c1 = cfun1;
	cfun->crcdat.two_crc.c2 = cfun2;
	c->crckind = SEQ_INJ;
	c->g_inj = G_AR;
	c->crcdat.seq_tv.ptr.s = cfun;
	return c;
}

static inline crc *normalize_tv_inj_list(crc* c) {
	crc *cs = (crc*)GC_MALLOC(sizeof(crc) * 2);
	crc *clist_ = &cs[0];
	crc *clist = &cs[1];
	clist_->crckind = TV_INJ;
	clist_->crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tylist;
	clist->crckind = LIST;
	clist->crcdat.one_crc = clist_;
	c->crckind = SEQ_INJ;
	c->g_inj = G_LI;
	c->crcdat.seq_tv.ptr.s = clist;
	return c;
}

static inline crc *normalize_tv_inj(crc *c) {
	switch(c->crcdat.seq_tv.ptr.tv->tykind) {
		case BASE_INT: return normalize_tv_inj_int(c); // X! [X:=int] -> id;int!
		case BASE_BOOL: return normalize_tv_inj_bool(c);
		case BASE_UNIT: return normalize_tv_inj_unit(c);
		case TYFUN: return normalize_tv_inj_fun(c);         // X! [X:=X1=>X2] -> X1?p=>X2!;(★→★)!	
		case TYLIST: return normalize_tv_inj_list(c);         // X! [X:=[X1]] -> [X1!];[★]!
		default: return c;
	}
}

static inline crc *normalize_tv_proj_int(crc *c) {
	c->crckind = SEQ_PROJ;
	c->g_proj = G_INT;
	c->crcdat.seq_tv.ptr.s = &crc_id;
	return c;
}

static inline crc *normalize_tv_proj_bool(crc *c) {
	c->crckind = SEQ_PROJ;
	c->g_proj = G_BOOL;
	c->crcdat.seq_tv.ptr.s = &crc_id;
	return c;
}

static inline crc *normalize_tv_proj_unit(crc *c) {
	c->crckind = SEQ_PROJ;
	c->g_proj = G_UNIT;
	c->crcdat.seq_tv.ptr.s = &crc_id;
	return c;
}

static inline crc *normalize_tv_proj_fun(crc *c) {
	crc *cs = (crc*)GC_MALLOC(sizeof(crc) * 3);
	crc *cfun1 = &cs[0];
	crc *cfun2 = &cs[1];
	crc *cfun = &cs[2];
	cfun1->crckind = TV_INJ;
	cfun1->crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.left;
	cfun2->crckind = TV_PROJ;
	cfun2->crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.right;
	cfun2->crcdat.seq_tv.rid = c->crcdat.seq_tv.rid;
	cfun->crckind = FUN;
	cfun->crcdat.two_crc.c1 = cfun1;
	cfun->crcdat.two_crc.c2 = cfun2;
	c->crckind = SEQ_PROJ;
	c->g_proj = G_AR;
	c->crcdat.seq_tv.ptr.s = cfun;
	return c;
}

static inline crc *normalize_tv_proj_list(crc *c) {
	crc *cs = (crc*)GC_MALLOC(sizeof(crc) * 2);
	crc *clist_ = &cs[0];
	crc *clist = &cs[1];
	clist_->crckind = TV_PROJ;
	clist_->crcdat.seq_tv.rid = c->crcdat.seq_tv.rid;
	clist_->crcdat.seq_tv.ptr.tv = c->crcdat.seq_tv.ptr.tv->tydat.tylist;
	clist->crckind = LIST;
	clist->crcdat.one_crc = clist_;
	c->crckind = SEQ_PROJ;
	c->g_proj = G_LI;
	c->crcdat.seq_tv.ptr.s = clist;
	return c;
}

static inline crc *normalize_tv_proj(crc *c) {
	switch(c->crcdat.seq_tv.ptr.tv->tykind) {
		case BASE_INT: return normalize_tv_proj_int(c);				// X?p [X:=int] -> int?p;id
		case BASE_BOOL: return normalize_tv_proj_bool(c);
		case BASE_UNIT: return normalize_tv_proj_unit(c);
		case TYFUN: return normalize_tv_proj_fun(c);       // X?p [X:=X1=>X2] -> (★→★)?p;X1!=>X2?p
		case TYLIST: return normalize_tv_proj_list(c);        // X?p [X:=[X1]] -> [★]?p;[X1?p]
		default: return c;
	}
}

static inline crc *normalize_tv_proj_inj_int(crc *c) {
	c->crckind = SEQ_PROJ_INJ;
	c->g_proj = G_INT;
	c->g_inj = G_INT;
	c->crcdat.seq_tv.ptr.s = &crc_id;
	return c;
}

static inline crc *normalize_tv_proj_inj_bool(crc *c) {
	c->crckind = SEQ_PROJ_INJ;
	c->g_proj = G_BOOL;
	c->g_inj = G_BOOL;
	c->crcdat.seq_tv.ptr.s = &crc_id;
	return c;
}

static inline crc *normalize_tv_proj_inj_unit(crc *c) {
	c->crckind = SEQ_PROJ_INJ;
	c->g_proj = G_UNIT;
	c->g_inj = G_UNIT;
	c->crcdat.seq_tv.ptr.s = &crc_id;
	return c;
}

static inline crc *normalize_tv_proj_inj_fun(crc *c) {
	ty *t1 = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.left;
	ty *t2 = c->crcdat.seq_tv.ptr.tv->tydat.tyfun.right;
	crc *cs = (crc*)GC_MALLOC(sizeof(crc) * 3);
	crc *cfun1 = &cs[0];
	crc *cfun2 = &cs[1];
	crc *cfun = &cs[2];
	cfun1->crckind = TV_PROJ_INJ;
	cfun1->crcdat.seq_tv.ptr.tv = t1;
	// cfun1->r_p = ;
	cfun2->crckind = TV_PROJ_INJ;
	cfun2->polarity = c->polarity;
	cfun2->crcdat.seq_tv.ptr.tv = t2;
	cfun2->crcdat.seq_tv.rid = c->crcdat.seq_tv.rid;
	cfun->crckind = FUN;
	cfun->crcdat.two_crc.c1 = cfun1;
	cfun->crcdat.two_crc.c2 = cfun2;
	c->crckind = SEQ_PROJ_INJ;
	c->g_inj = G_AR;
	c->g_proj = G_AR;
	c->crcdat.seq_tv.ptr.s = cfun;
	return c;
}

static inline crc *normalize_tv_proj_inj_list(crc *c) {
	ty *t = c->crcdat.seq_tv.ptr.tv->tydat.tylist;
	crc *cs = (crc*)GC_MALLOC(sizeof(crc) * 2);
	crc *clist_ = &cs[0];
	crc *clist = &cs[1];
	clist_->crckind = TV_PROJ_INJ;
	clist_->polarity = c->polarity;
	clist_->crcdat.seq_tv.rid = c->crcdat.seq_tv.rid;
	clist_->crcdat.seq_tv.ptr.tv = t;
	clist->crckind = LIST;
	clist->crcdat.one_crc = clist_;
	c->crckind = SEQ_PROJ_INJ;
	c->g_inj = G_LI;
	c->g_proj = G_LI;
	c->crcdat.seq_tv.ptr.s = clist;
	return c;
}

static inline crc *normalize_tv_proj_inj(crc *c) {
	switch(c->crcdat.seq_tv.ptr.tv->tykind) {
		case BASE_INT: return normalize_tv_proj_inj_int(c);                    // ?pX! [X:=int] -> int?p;id;int!
		case BASE_BOOL: return normalize_tv_proj_inj_bool(c);
		case BASE_UNIT: return normalize_tv_proj_inj_unit(c);
		case TYFUN: return normalize_tv_proj_inj_fun(c);  				// ?pX! [X:=X1=>X2] -> (★→★)?p(?pX1!=>?pX2!);(★→★)!
		case TYLIST: return normalize_tv_proj_inj_list(c);				// ?pX! [X:=[X1]] -> [★]?p;[?pX1!];[★]!
		default: return c;
	}
}

crc* normalize_crc(crc *c) {
	switch(c->crckind) {
		case TV_INJ: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			return normalize_tv_inj(c);
		}
		case TV_PROJ: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			return normalize_tv_proj(c);
		}
		case SEQ_PROJ_INJ: {
			c->crcdat.seq_tv.ptr.tv = ty_find(c->crcdat.seq_tv.ptr.tv);
			return normalize_tv_proj_inj(c);
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
	if (c2->crckind == BOT) return c2;
	switch(c1->crckind) {
		case ID: return c2;
		case FUN: return compose_funs(c1, c2);
		case LIST: return compose_lists(c1, c2);
	}
}

static inline crc *make_bot(uint32_t rid) {
	crc *retc = (crc*)GC_MALLOC(sizeof(crc));
	retc->crckind = BOT;
	retc->crcdat.rid = rid;
	return retc;
}

crc* compose(crc *c1, crc *c2) {
	// printf("c1: %d, c2: %d\n", c1->crckind, c2->crckind);
	// if (c1->crckind == ID) return c2; // id;;s -> s
	if (c2->crckind == ID) return c1; // s;;id -> s
	// if (c1->crckind == BOT) return c1; // ⊥;;s -> ⊥
	// if (c2->crckind == BOT) return c2; 
	  // s;;⊥ は ⊥ ではない (G?p;i;;⊥ -> G?p;⊥)

	switch(c1->crckind) {
		case ID: return c2;
		case BOT: return c1;
		case SEQ_PROJ: 
		CASE_SEQ_PROJ: { // G?p;g;;s -> G?p;(g;;s)
			crc *retc = (crc*)GC_MALLOC(sizeof(crc));
			retc->g_proj = c1->g_proj;
			retc->polarity = c1->polarity;
			retc->crcdat.seq_tv.rid = c1->crcdat.seq_tv.rid;
			// printf("  c1.g_proj:%d, c1.c:%d\n", c1->g_proj, c1->crcdat.seq_tv.ptr.s->crckind);
			switch(c2->crckind) {
				case TV_INJ: {
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_inj(c2);
				}
				case SEQ_INJ: {
					retc->crckind = SEQ_PROJ_INJ;
					retc->g_inj = c2->g_inj;
					retc->crcdat.seq_tv.ptr.s = compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
					return retc;
				}
				default: {
					retc->crckind = SEQ_PROJ;
					retc->crcdat.seq_tv.ptr.s = compose_g(c1->crcdat.seq_tv.ptr.s, c2);
					return retc;
				}
			}
		}
		case SEQ_PROJ_INJ: 
		CASE_SEQ_PROJ_INJ: { // G?p;g;G!;;s -> G?p;(g;G!;;s)
			// printf("  c1.g_proj:%d, c1.c:%d, c1.g_inj:%d\n", c1->g_proj, c1->crcdat.seq_tv.ptr.s->crckind, c1->g_inj);
			switch(c2->crckind) {
				case SEQ_PROJ: 
				CASE_SEQ_PROJ_INJ_SEQ_PROJ: { //G?p;g;G!;;H?q;g'
					// printf("  c2.g_proj:%d, c2.c:%d\n", c2->g_proj, c2->crcdat.seq_tv.ptr.s->crckind);
					crc *retc = (crc*)GC_MALLOC(sizeof(crc));
					retc->g_proj = c1->g_proj;
					retc->polarity = c1->polarity;
					retc->crcdat.seq_tv.rid = c1->crcdat.seq_tv.rid;
					retc->crckind = SEQ_PROJ;
					if (c1->g_inj == c2->g_proj) {   //G?p;g;G!;;G?q;g' -> G?p;g;;g'
						retc->crcdat.seq_tv.ptr.s = compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
						return retc;
					} else {                         //G!p;g;G!;;H?q;i -> G!p;bot^q (if G neq H)
						retc->crcdat.seq_tv.ptr.s = make_bot(c2->crcdat.seq_tv.rid);
						return retc;
					}
				}
				case SEQ_PROJ_INJ: 
				CASE_SEQ_PROJ_INJ_SEQ_PROJ_INJ: { //G?p;g;G!;;H?q;g';H'!
					crc *retc = (crc*)GC_MALLOC(sizeof(crc));
					retc->g_proj = c1->g_proj;
					retc->polarity = c1->polarity;
					retc->crcdat.seq_tv.rid = c1->crcdat.seq_tv.rid;
					if (c1->g_inj == c2->g_proj) {   //G?p;g;G!;;G?q;g';H'! -> G?p;g;;g';H'!
						retc->crckind = SEQ_PROJ_INJ;
						retc->g_inj = c2->g_inj;
						retc->crcdat.seq_tv.ptr.s = compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
						return retc;
					} else {                                                                 //G?p;g;G!;;H?q;g';H'! -> G?p;bot^q (if G neq H)
						retc->crckind = SEQ_PROJ;
						retc->crcdat.seq_tv.ptr.s = make_bot(c2->crcdat.seq_tv.rid);
						return retc;
					}
				}
				case TV_PROJ: {										   	//G?p;g;G!;;X?q
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj_inj(c2);
					if (c2->crckind != TV_PROJ) goto CASE_SEQ_PROJ_INJ_SEQ_PROJ;
					crc *retc = (crc*)GC_MALLOC(sizeof(crc));
					retc->crckind = SEQ_PROJ;
					retc->g_proj = c1->g_proj;
					retc->polarity = c1->polarity;
					retc->crcdat.seq_tv.rid = c1->crcdat.seq_tv.rid;
					switch(c1->g_inj) {
						case G_AR: {						//G?p;g;(★→★)!;;X?q -> G?p;g;;X1!=>X2?q [X:=X1=>X2]
							// printf("DTI : arrow was inferred\n");
							c2->crcdat.seq_tv.ptr.tv->tykind = TYFUN;
							c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.left = newty();
							c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.right = newty();
							c2 = normalize_tv_proj_inj_fun(c2);
							// printf("%p <- (%p=>%p)\n", c2->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.left, c2->crcdat.tv->tydat.tyfun.right);
							retc->crcdat.seq_tv.ptr.s = compose_funs(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
							return retc;
						}
						case G_LI: {						//G?p;g;[★]!;;X?1 -> G?p;g;;[X1?q] [X:=[X1]]
							// printf("DTI : list was inferred\n");
							c2->crcdat.seq_tv.ptr.tv->tykind = TYLIST;
							c2->crcdat.seq_tv.ptr.tv->tydat.tylist = newty();
							c2 = normalize_tv_proj_list(c2);
							// printf("%p <- [%p]\n", c2->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv->tydat.tylist);
							retc->crcdat.seq_tv.ptr.s = compose_lists(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
							return retc;
						}
						case G_INT: {                      //G?p;g;int!;;X?q -> G?p;g;;id -> G?p;g [X:=int]
							// printf("DTI : int was inferred\n");
							// printf("%p <- int\n", c2->crcdat.seq_tv.ptr.tv);
							*c2->crcdat.seq_tv.ptr.tv = tyint;
							c2 = normalize_tv_proj_int(c2);
							retc->crcdat.seq_tv.ptr.s = c1->crcdat.seq_tv.ptr.s;
							return retc;
						}
						case G_BOOL: {
							// printf("DTI : bool was inferred\n");
							// printf("%p <- bool\n", c2->crcdat.seq_tv.ptr.tv);
							*c2->crcdat.seq_tv.ptr.tv = tybool;
							c2 = normalize_tv_proj_bool(c2);
							retc->crcdat.seq_tv.ptr.s = c1->crcdat.seq_tv.ptr.s;
							return retc;
						}
						case G_UNIT: {
							// printf("DTI : unit was inferred\n");
							// printf("%p <- unit\n", c2->crcdat.seq_tv.ptr.tv);
							*c2->crcdat.seq_tv.ptr.tv = tyunit;
							c2 = normalize_tv_proj_unit(c2);
							retc->crcdat.seq_tv.ptr.s = c1->crcdat.seq_tv.ptr.s;
							return retc;
						}
					}
				}
				case TV_PROJ_INJ: {									   //G?p;g;G!;;?qX!
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj_inj(c2);
					if (c2->crckind != TV_PROJ_INJ) goto CASE_SEQ_PROJ_INJ_SEQ_PROJ_INJ;
					crc *retc = (crc*)GC_MALLOC(sizeof(crc));
					retc->crckind = SEQ_PROJ_INJ;
					retc->g_proj = c1->g_proj;
					retc->polarity = c1->polarity;
					retc->crcdat.seq_tv.rid = c1->crcdat.seq_tv.rid;
					switch (c1->g_inj) {
						case G_AR: {						//G?p;g;(★→★)!;;?qX! -> G?p;g;;X1!=>X2?q;(★->★)! [X:=X1=>X2]
							// printf("DTI : arrow was inferred\n");
							c2->crcdat.seq_tv.ptr.tv->tykind = TYFUN;
							c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.left = newty();
							c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.right = newty();
							// printf("%p <- (%p=>%p)\n", c2->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.left, c2->crcdat.tv->tydat.tyfun.right);
							c2 = normalize_tv_proj_inj_fun(c2);
							retc->g_inj = G_AR;
							retc->crcdat.seq_tv.ptr.s = compose_funs(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
							return retc;
						}
						case G_LI: {						//G?p;g;[★]!;;?qX! -> G?p;g;;[?qX1!];[★]! [X:=[X1]]
							// printf("DTI : list was inferred\n");
							c2->crcdat.seq_tv.ptr.tv->tykind = TYLIST;
							c2->crcdat.seq_tv.ptr.tv->tydat.tylist = newty();
							// printf("%p <- [%p]\n", c2->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv->tydat.tylist);
							c2 = normalize_tv_proj_inj_list(c2);
							retc->g_inj = G_LI;
							retc->crcdat.seq_tv.ptr.s = compose_lists(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
							return retc;
						}
						case G_INT: {                      //G?p;g;int!;;?qX! -> G?p;g;;id;int! -> G?p;g;int! [X:=int]
							// printf("DTI : int was inferred\n");
							// printf("%p <- int\n", c2->crcdat.seq_tv.ptr.tv);
							*c2->crcdat.seq_tv.ptr.tv = tyint;
							c2 = normalize_tv_proj_inj_int(c2);
							retc->g_inj = G_INT;
							retc->crcdat.seq_tv.ptr.s = c1->crcdat.seq_tv.ptr.s;
							return retc;
						}
						case G_BOOL: {
							// printf("DTI : bool was inferred\n");
							// printf("%p <- bool\n", c2->crcdat.seq_tv.ptr.tv);
							*c2->crcdat.seq_tv.ptr.tv = tybool;
							c2 = normalize_tv_proj_inj_bool(c2);
							retc->g_inj = G_BOOL;
							retc->crcdat.seq_tv.ptr.s = c1->crcdat.seq_tv.ptr.s;
							return retc;
						}
						case G_UNIT: {
							// printf("DTI : unit was inferred\n");
							// printf("%p <- unit\n", c2->crcdat.seq_tv.ptr.tv);
							*c2->crcdat.seq_tv.ptr.tv = tyunit;
							c2 = normalize_tv_proj_inj_unit(c2);
							retc->g_inj = G_UNIT;
							retc->crcdat.seq_tv.ptr.s = c1->crcdat.seq_tv.ptr.s;
							return retc;
						}
					}
				}
			}
		}
		case SEQ_INJ: 
		CASE_SEQ_INJ: {   //g;G!;;s
			// printf("  c1.c:%d, c1.g_inj:%d\n", c1->crcdat.seq_tv.ptr.s->crckind, c1->g_inj);
			switch(c2->crckind) {
				case SEQ_PROJ: 
				CASE_SEQ_INJ_SEQ_PROJ: { //g;G!;;H?p;g'
					// printf("  c2.g_proj:%d, c2.c2:%d\n", c2->g_proj, c2->crcdat.seq_tv.ptr.s->crckind);
					if (c1->g_inj == c2->g_proj) {   //g;G!;;G?p;g' -> g;;g'
						return compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
					} else {                                                                 //g;G!;;H?p;i -> bot^p (if G neq H)
						return make_bot(c2->crcdat.seq_tv.rid);
					}
				}
				case SEQ_PROJ_INJ: 
				CASE_SEQ_INJ_SEQ_PROJ_INJ: { //g;G!;;H?p;g';H'!
					if (c1->g_inj == c2->g_proj) {   //g;G!;;G?p;g';H'! -> g;;g';H'!
						crc *retc = (crc*)GC_MALLOC(sizeof(crc));
						retc->crckind = SEQ_INJ;
						retc->g_inj = c2->g_inj;
						retc->crcdat.seq_tv.ptr.s = compose_g(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
						return retc;
					} else {                                                                 //g;G!;;H?p;g';H'! -> bot^p (if G neq H)
						return make_bot(c2->crcdat.seq_tv.rid);
					}
				}
				case TV_PROJ: {										   	//g;G!;;X?p
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj(c2);
					if (c2->crckind != TV_PROJ) goto CASE_SEQ_INJ_SEQ_PROJ;
					switch(c1->g_inj) {
						case G_AR: {						//g;(★→★)!;;X?p -> g;;X1!=>X2?p [X:=X1=>X2]
							// printf("DTI : arrow was inferred\n");
							c2->crcdat.seq_tv.ptr.tv->tykind = TYFUN;
							c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.left = newty();
							c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.right = newty();
							c2 = normalize_tv_proj_fun(c2);
							// printf("%p <- (%p=>%p)\n", c2->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.left, c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.right);
							return compose_funs(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
						}
						case G_LI: {						//g;[★]!;;X?p -> g;;[X1?p] [X:=[X1]]
							// printf("DTI : list was inferred\n");
							c2->crcdat.seq_tv.ptr.tv->tykind = TYLIST;
							c2->crcdat.seq_tv.ptr.tv->tydat.tylist = newty();
							c2 = normalize_tv_proj_list(c2);
							// printf("%p <- [%p]\n", c2->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv->tydat.tylist);
							return compose_lists(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
						}
						case G_INT: {                      //g;int!;;X?p -> g;;id -> g [X:=int]
							// printf("DTI : int was inferred\n");
							// printf("%p <- int\n", c2->crcdat.seq_tv.ptr.tv);
							*c2->crcdat.seq_tv.ptr.tv = tyint;
							c2 = normalize_tv_proj_int(c2);
							return c1->crcdat.seq_tv.ptr.s;
						}
						case G_BOOL: {
							// printf("DTI : bool was inferred\n");
							// printf("%p <- bool\n", c2->crcdat.seq_tv.ptr.tv);
							*c2->crcdat.seq_tv.ptr.tv = tybool;
							c2 = normalize_tv_proj_bool(c2);
							return c1->crcdat.seq_tv.ptr.s;
						}
						case G_UNIT: {
							// printf("DTI : unit was inferred\n");
							// printf("%p <- unit\n", c2->crcdat.seq_tv.ptr.tv);
							*c2->crcdat.seq_tv.ptr.tv = tyunit;
							c2 = normalize_tv_proj_unit(c2);
							return c1->crcdat.seq_tv.ptr.s;
						}
					}
				}
				case TV_PROJ_INJ: {									   //g;G!;;?pX!
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj_inj(c2);
					if (c2->crckind != TV_PROJ_INJ) goto CASE_SEQ_INJ_SEQ_PROJ_INJ;
					switch (c1->g_inj) {
						case G_AR: {						//g;(★→★)!;;?pX! -> g;;X1!=>X2?p;(★->★)! [X:=X1=>X2]
							// printf("DTI : arrow was inferred\n");
							c2->crcdat.seq_tv.ptr.tv->tykind = TYFUN;
							c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.left = newty();
							c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.right = newty();
							// printf("%p <- (%p=>%p)\n", c2->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.left, c2->crcdat.seq_tv.ptr.tv->tydat.tyfun.right);
							c2 = normalize_tv_proj_inj_fun(c2);
							crc *retc = (crc*)GC_MALLOC(sizeof(crc));
							retc->crckind = SEQ_INJ;
							retc->g_inj = G_AR;
							retc->crcdat.seq_tv.ptr.s = compose_funs(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
							return retc;
						}
						case G_LI: {						//g;[★]!;;?pX! -> g;;[?pX1!];[★]! [X:=[X1]]
							// printf("DTI : list was inferred\n");
							c2->crcdat.seq_tv.ptr.tv->tykind = TYLIST;
							c2->crcdat.seq_tv.ptr.tv->tydat.tylist = newty();
							// printf("%p <- [%p]\n", c2->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv->tydat.tylist);
							c2 = normalize_tv_proj_inj_list(c2);
							crc *retc = (crc*)GC_MALLOC(sizeof(crc));
							retc->crckind = SEQ_INJ;
							retc->g_inj = G_LI;
							retc->crcdat.seq_tv.ptr.s = compose_lists(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
							return retc;
						}
						case G_INT: {                      //g;int!;;?pX! -> g;;id;int! -> g;int! [X:=int]
							// printf("DTI : int was inferred\n");
							// printf("%p <- int\n", c2->crcdat.seq_tv.ptr.tv);
							*c2->crcdat.seq_tv.ptr.tv = tyint;
							c2 = normalize_tv_proj_inj_int(c2);
							return c1;
						}
						case G_BOOL: {
							// printf("DTI : bool was inferred\n");
							// printf("%p <- bool\n", c2->crcdat.seq_tv.ptr.tv);
							*c2->crcdat.seq_tv.ptr.tv = tybool;
							c2 = normalize_tv_proj_inj_bool(c2);
							return c1;
						}
						case G_UNIT: {
							// printf("DTI : unit was inferred\n");
							// printf("%p <- unit\n", c2->crcdat.seq_tv.ptr.tv);
							*c2->crcdat.seq_tv.ptr.tv = tyunit;
							c2 = normalize_tv_proj_inj_unit(c2);
							return c1;
						}
					}
				}
			}
		}
		case TV_PROJ: {                                // X?p;;s
			c1->crcdat.seq_tv.ptr.tv = ty_find(c1->crcdat.seq_tv.ptr.tv);
			c1 = normalize_tv_proj(c1);
			if (c1->crckind != TV_PROJ) goto CASE_SEQ_PROJ;
			// X?p;;X! -> ?pX!
			c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
			crc *retc = (crc*)GC_MALLOC(sizeof(crc));
			retc->crckind = TV_PROJ_INJ;
			retc->polarity = c1->polarity;
			retc->crcdat.seq_tv.ptr.tv = c1->crcdat.seq_tv.ptr.tv;
			retc->crcdat.seq_tv.rid = c1->crcdat.seq_tv.rid;		
			return retc;
		}
		case TV_INJ: {								    // X!;;s
			c1->crcdat.seq_tv.ptr.tv = ty_find(c1->crcdat.seq_tv.ptr.tv);
			c1 = normalize_tv_inj(c1);
			if (c1->crckind != TV_INJ) goto CASE_SEQ_INJ;
			switch (c2->crckind) {      
				case SEQ_PROJ: 
				CASE_TV_INJ_SEQ_PROJ: { //X!;;G?p;g
					// printf("  c2.g_proj:%d, c2.c:%d\n", c2->crcdat.g_proj, c2->crcdat.seq_tv.ptr.s->crckind);
					switch(c2->g_proj) {                            
						case G_AR: {    //X!;;(★→★)?p;g -> X1?p=>X2!;;g [X:=X1=>X2]
							// printf("DTI : arrow was inferred\n");
							c1->crcdat.seq_tv.ptr.tv->tykind = TYFUN;
							c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.left = newty();
							c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.right = newty();
							c1 = normalize_tv_inj_fun(c1);
							// printf("%p <- (%p=>%p)\n", c1->crcdat.seq_tv.ptr.tv, c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.left, c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.right);
							return compose_funs(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
						}
						case G_LI: {                       //X!;;[★]?p;g -> [X1!];;g [X:=[X1]]
							// printf("DTI : list was inferred\n");
							c1->crcdat.seq_tv.ptr.tv->tykind = TYLIST;
							c1->crcdat.seq_tv.ptr.tv->tydat.tylist = newty();
							c1 = normalize_tv_inj_list(c1);
							// printf("%p <- [%p]\n", c1->crcdat.seq_tv.ptr.tv, c1->crcdat.seq_tv.ptr.tv->tydat.tylist);
							return compose_lists(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
						}
						case G_INT: {                   //X!;;int?p;g -> id;;g -> g [X:=int]
							// printf("DTI : int was inferred\n");
							// printf("%p <- int\n", c1->crcdat.seq_tv.ptr.tv);
							*c1->crcdat.seq_tv.ptr.tv = tyint;
							*c1 = crc_inj_INT;
							return c2->crcdat.seq_tv.ptr.s;
						}
						case G_BOOL: {
							// printf("DTI : bool was inferred\n");
							// printf("%p <- bool\n", c1->crcdat.seq_tv.ptr.tv);
							*c1->crcdat.seq_tv.ptr.tv = tybool;
							*c1 = crc_inj_BOOL;
							return c2->crcdat.seq_tv.ptr.s;
						}
						case G_UNIT: {
							// printf("DTI : unit was inferred\n");
							// printf("%p <- unit\n", c1->crcdat.seq_tv.ptr.tv);
							*c1->crcdat.seq_tv.ptr.tv = tyunit;
							*c1 = crc_inj_UNIT;
							return c2->crcdat.seq_tv.ptr.s;
						}
					}
				}	
				case SEQ_PROJ_INJ: 
				CASE_TV_INJ_SEQ_PROJ_INJ: { //X!;;G?p;g;G!
					crc *retc = (crc*)GC_MALLOC(sizeof(crc));
					retc->crckind = SEQ_INJ;
					retc->g_inj = c2->g_inj;
					// printf("  c2.g_proj:%d, c2.c:%d, c2.g_inj:%d\n", c2->c_proj, c2->crcdat.seq_tv.ptr.s->crckind, c2->c_inj);
					switch(c2->g_proj) {                            
						case G_AR: {    //X!;;(★→★)?p;g;G! -> X1?p=>X2!;;g;G! [X:=X1=>X2]
							// printf("DTI : arrow was inferred\n");
							c1->crcdat.seq_tv.ptr.tv->tykind = TYFUN;
							c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.left = newty();
							c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.right = newty();
							c1 = normalize_tv_inj_fun(c1);
							// printf("%p <- (%p=>%p)\n", c1->crcdat.seq_tv.ptr.tv, c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.left, c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.right);
							retc->crcdat.seq_tv.ptr.s = compose_funs(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
							return retc;
						}
						case G_LI: {                       //X!;;[★]?p;g;G! -> [X1!];;g;G! [X:=[X1]]
							// printf("DTI : list was inferred\n");
							c1->crcdat.seq_tv.ptr.tv->tykind = TYLIST;
							c1->crcdat.seq_tv.ptr.tv->tydat.tylist = newty();
							c1 = normalize_tv_inj_list(c1);
							// printf("%p <- [%p]\n", c1->crcdat.seq_tv.ptr.tv, c1->crcdat.seq_tv.ptr.tv->tydat.tylist);
							retc->crcdat.seq_tv.ptr.s = compose_lists(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
							return retc;
						}
						case G_INT: {                   //X!;;int?p;g;G! -> id;;g;G! -> g;G! [X:=int]
							// printf("DTI : int was inferred\n");
							// printf("%p <- int\n", c1->crcdat.seq_tv.ptr.tv);
							*c1->crcdat.seq_tv.ptr.tv = tyint;
							c1 = normalize_tv_inj_int(c1);
							retc->crcdat.seq_tv.ptr.s = c2->crcdat.seq_tv.ptr.s;
							return retc;
						}
						case G_BOOL: {
							// printf("DTI : bool was inferred\n");
							// printf("%p <- bool\n", c1->crcdat.seq_tv.ptr.tv);
							*c1->crcdat.seq_tv.ptr.tv = tybool;
							c1 = normalize_tv_inj_bool(c1);
							retc->crcdat.seq_tv.ptr.s = c2->crcdat.seq_tv.ptr.s;
							return retc;
						}
						case G_UNIT: {
							// printf("DTI : unit was inferred\n");
							// printf("%p <- unit\n", c1->crcdat.seq_tv.ptr.tv);
							*c1->crcdat.seq_tv.ptr.tv = tyunit;
							c1 = normalize_tv_inj_unit(c1);
							retc->crcdat.seq_tv.ptr.s = c2->crcdat.seq_tv.ptr.s;
							return retc;
						}
					}
				}		
				case TV_PROJ: {                                            //X!;;Y?p
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj(c2);
					if (c2->crckind != TV_PROJ) goto CASE_TV_INJ_SEQ_PROJ;
					if (c1->crcdat.seq_tv.ptr.tv == c2->crcdat.seq_tv.ptr.tv) {	//X!;;X?p -> id
						return &crc_id;
					} else {                                                                    //X!;;Y?p -> id [X:=Y]
						// printf("DTI : tyvar was inferred\n");
						// printf("%p <- %p\n", c1->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv);
						c1->crcdat.seq_tv.ptr.tv->tykind = SUBSTITUTED;
						c1->crcdat.seq_tv.ptr.tv->tydat.tv = c2->crcdat.seq_tv.ptr.tv;
						return &crc_id;
					}
				}
				case TV_PROJ_INJ: {									    //X!;;?pY!
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj_inj(c2);
					if (c2->crckind != TV_PROJ_INJ) goto CASE_TV_INJ_SEQ_PROJ_INJ;
					if (c1->crcdat.seq_tv.ptr.tv == c2->crcdat.seq_tv.ptr.tv) {                                //X!;;?pX! -> X!
						return c1;												// this is not real, but correct
					} else {																	//X!;;?pY! -> Y! [X:=Y]
						// printf("DTI : tyvar was inferred\n");
						// printf("%p <- %p\n", c1->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv);
						c1->crcdat.seq_tv.ptr.tv->tykind = SUBSTITUTED;
						c1->crcdat.seq_tv.ptr.tv->tydat.tv = c2->crcdat.seq_tv.ptr.tv;
						return c1;
					}
				}
			}
		}
		case TV_PROJ_INJ: {				//?pX!;;s
			c1->crcdat.seq_tv.ptr.tv = ty_find(c1->crcdat.seq_tv.ptr.tv);
			c1 = normalize_tv_proj_inj(c1);
			if (c1->crckind != TV_PROJ_INJ) goto CASE_SEQ_PROJ_INJ;
			switch (c2->crckind) {      
				case SEQ_PROJ: 
				CASE_TV_PROJ_INJ_SEQ_PROJ: {  //?pX!;;G?q;g
					crc *retc = (crc*)GC_MALLOC(sizeof(crc));
					retc->crckind = SEQ_PROJ;
					retc->polarity = c1->polarity;
					retc->crcdat.seq_tv.rid = c1->crcdat.seq_tv.rid;
					// printf("  c2.g_proj:%d, c2.c:%d\n", c2->g_proj, c2->crcdat.seq_tv.ptr.s->crckind);
					switch (c2->g_proj) {
						case G_AR: {                                //?pX!;;(★→★)?q;g -> (★→★)?p;?qX1!=>?pX2!;;g [X:=X1=>X2]
							// printf("DTI : arrow was inferred\n");
							c1->crcdat.seq_tv.ptr.tv->tykind = TYFUN;
							c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.left = newty();
							c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.right = newty();
							c1 = normalize_tv_proj_inj_fun(c1);
							// printf("%p <- (%p=>%p)\n", c1->crcdat.seq_tv.ptr.tv, c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.left, c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.right);
							retc->g_proj = c1->g_proj;
							retc->crcdat.seq_tv.ptr.s = compose_funs(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
							return retc;
						}
						case G_LI: {                                //?pX!;;[★]?q;g -> [★]?p;[?qX1!];;g [X:=[X1]]
							// printf("DTI : list was inferred\n");
							c1->crcdat.seq_tv.ptr.tv->tykind = TYLIST;
							c1->crcdat.seq_tv.ptr.tv->tydat.tylist = newty();
							c1 = normalize_tv_proj_inj_list(c1);
							// printf("%p <- [%p])\n", c1->crcdat.seq_tv.ptr.tv, c1->crcdat.seq_tv.ptr.tv->tydat.tylist);
							retc->g_proj = c1->g_proj;
							retc->crcdat.seq_tv.ptr.s = compose_lists(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
							return retc;
						}
						case G_INT: {                     //?pX!;;int?q;g -> int?p;id;;g -> int?p;g [X:=int]
							// printf("DTI : int was inferred\n");
							// printf("%p <- int\n", c1->crcdat.seq_tv.ptr.tv);
							*c1->crcdat.seq_tv.ptr.tv = tyint;
							c1 = normalize_tv_proj_inj_int(c1);
							retc->g_proj = c1->g_proj;
							retc->crcdat.seq_tv.ptr.s = c2->crcdat.seq_tv.ptr.s;
							return retc;
						}
						case G_BOOL: {
							// printf("DTI : bool was inferred\n");
							// printf("%p <- bool\n", c1->crcdat.seq_tv.ptr.tv);
							*c1->crcdat.seq_tv.ptr.tv = tybool;
							c1 = normalize_tv_proj_inj_bool(c1);
							retc->g_proj = c1->g_proj;
							retc->crcdat.seq_tv.ptr.s = c2->crcdat.seq_tv.ptr.s;
							return retc;
						}
						case G_UNIT: {
							// printf("DTI : unit was inferred\n");
							// printf("%p <- unit\n", c1->crcdat.seq_tv.ptr.tv);
							*c1->crcdat.seq_tv.ptr.tv = tyunit;
							c1 = normalize_tv_proj_inj_unit(c1);
							retc->g_proj = c1->g_proj;
							retc->crcdat.seq_tv.ptr.s = c2->crcdat.seq_tv.ptr.s;
							return retc;
						}
					}
				}
				case SEQ_PROJ_INJ: 
				CASE_TV_PROJ_INJ_SEQ_PROJ_INJ: {  //?pX!;;G?q;g;G!
					crc *retc = (crc*)GC_MALLOC(sizeof(crc));
					retc->crckind = SEQ_PROJ_INJ;
					retc->g_inj = c2->g_inj;
					retc->polarity = c1->polarity;
					retc->crcdat.seq_tv.rid = c1->crcdat.seq_tv.rid;
					// printf("  c2.g_proj:%d, c2.c:%d, c2.g_inj:%d\n", c2->g_proj, c2->crcdat.seq_tv.ptr.s->crckind, c2->g_inj);
					switch (c2->g_proj) {
						case G_AR: {                                //?pX!;;(★→★)?q;g;G! -> (★→★)?p;?qX1!=>?pX2!;;g;G! [X:=X1=>X2]
							// printf("DTI : arrow was inferred\n");
							c1->crcdat.seq_tv.ptr.tv->tykind = TYFUN;
							c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.left = newty();
							c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.right = newty();
							c1 = normalize_tv_proj_inj_fun(c1);
							// printf("%p <- (%p=>%p)\n", c1->crcdat.seq_tv.ptr.tv, c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.left, c1->crcdat.seq_tv.ptr.tv->tydat.tyfun.right);
							retc->g_proj = c1->g_proj;
							retc->crcdat.seq_tv.ptr.s = compose_funs(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
							return retc;
						}
						case G_LI: {                                //?pX!;;[★]?q;g -> [★]?p;[?qX1!];;g;G! [X:=[X1]]
							// printf("DTI : list was inferred\n");
							c1->crcdat.seq_tv.ptr.tv->tykind = TYLIST;
							c1->crcdat.seq_tv.ptr.tv->tydat.tylist = newty();
							c1 = normalize_tv_proj_inj_list(c1);
							// printf("%p <- [%p])\n", c1->crcdat.seq_tv.ptr.tv, c1->crcdat.seq_tv.ptr.tv->tydat.tylist);
							retc->g_proj = c1->g_proj;
							retc->crcdat.seq_tv.ptr.s = compose_lists(c1->crcdat.seq_tv.ptr.s, c2->crcdat.seq_tv.ptr.s);
							return retc;
						}
						case G_INT: {                     //?pX!;;int?q;g -> int?p;id;;g -> int?p;g;G! [X:=int]
							// printf("DTI : int was inferred\n");
							// printf("%p <- int\n", c1->crcdat.seq_tv.ptr.tv);
							*c1->crcdat.seq_tv.ptr.tv = tyint;
							c1 = normalize_tv_proj_inj_int(c1);
							retc->g_proj = c1->g_proj;
							retc->crcdat.seq_tv.ptr.s = c2->crcdat.seq_tv.ptr.s;
							return retc;
						}
						case G_BOOL: {
							// printf("DTI : bool was inferred\n");
							// printf("%p <- bool\n", c1->crcdat.seq_tv.ptr.tv);
							*c1->crcdat.seq_tv.ptr.tv = tybool;
							c1 = normalize_tv_proj_inj_bool(c1);
							retc->g_proj = c1->g_proj;
							retc->crcdat.seq_tv.ptr.s = c2->crcdat.seq_tv.ptr.s;
							return retc;
						}
						case G_UNIT: {
							// printf("DTI : unit was inferred\n");
							// printf("%p <- unit\n", c1->crcdat.seq_tv.ptr.tv);
							*c1->crcdat.seq_tv.ptr.tv = tyunit;
							c1 = normalize_tv_proj_inj_unit(c1);
							retc->g_proj = c1->g_proj;
							retc->crcdat.seq_tv.ptr.s = c2->crcdat.seq_tv.ptr.s;
							return retc;
						}
					}
				}
				case TV_PROJ: {                                            //?pX!;;Y?q
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj(c2);
					if (c2->crckind != TV_PROJ) goto CASE_TV_PROJ_INJ_SEQ_PROJ;
					if (c1->crcdat.seq_tv.ptr.tv == c2->crcdat.seq_tv.ptr.tv) {								//?pX!;;X?q -> X?p
						c2->polarity = c1->polarity;
						c2->crcdat.seq_tv.rid = c1->crcdat.seq_tv.rid;
						return c2;
					} else {                                                                    //?pX!;;Y?q -> Y?p [X:=Y]
						// printf("DTI : tyvar was inferred\n");
						// printf("%p <- %p\n", c1->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv);
						c1->crcdat.seq_tv.ptr.tv->tykind = SUBSTITUTED;
						c1->crcdat.seq_tv.ptr.tv->tydat.tv = c2->crcdat.seq_tv.ptr.tv;
						c2->polarity = c1->polarity;
						c2->crcdat.seq_tv.rid = c1->crcdat.seq_tv.rid;
						return c2;
					}
				}
				case TV_PROJ_INJ: {									    //?pX!;;?qY!
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_proj_inj(c2);
					if (c2->crckind != TV_PROJ_INJ) {
						return compose(c1, c2);
					} else if (c1->crcdat.seq_tv.ptr.tv == c2->crcdat.seq_tv.ptr.tv) {                                //?pX!;;?qX! -> ?pX!
						return c1;												// this is not real, but correct
					} else {																    //?pX!;;?pY! -> ?pY! [X:=Y]
						// printf("DTI : tyvar was inferred\n");
						// printf("%p <- %p\n", c1->crcdat.seq_tv.ptr.tv, c2->crcdat.seq_tv.ptr.tv);
						c1->crcdat.seq_tv.ptr.tv->tykind = SUBSTITUTED;
						c1->crcdat.seq_tv.ptr.tv->tydat.tv = c2->crcdat.seq_tv.ptr.tv;
						return c1;
					}
				}
			}
		}
		case FUN: {
			switch (c2->crckind) {
				case FUN: return compose_funs(c1, c2);  //s=>t;;s'=>t' -> s';;s=>t;;t'
				case BOT: return c2;
				case TV_INJ: {
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_inj_fun(c2);
				}
				case SEQ_INJ: { 						//g;;h;G! -> (g;;h);G!
					// printf("  c2.c:%d, c2.g_inj:%d\n", c2->crcdat.seq_tv.ptr.s->crckind, c2->g_inj);
					crc *retc = (crc*)GC_MALLOC(sizeof(crc));
					retc->crckind = SEQ_INJ;
					retc->g_inj = c2->g_inj;
					retc->crcdat.seq_tv.ptr.s = compose_funs(c1, c2->crcdat.seq_tv.ptr.s);
					return retc;
				}
			}
		}
		case LIST: {
			switch(c2->crckind) {
				case LIST: return compose_lists(c1, c2);
				case BOT: return c2;
				case TV_INJ: {
					c2->crcdat.seq_tv.ptr.tv = ty_find(c2->crcdat.seq_tv.ptr.tv);
					c2 = normalize_tv_inj_list(c2);
				}
				case SEQ_INJ: { 						//g;;h;G! -> (g;;h);G!
					// printf("  c2.c:%d, c2.g_inj:%d\n", c2->crcdat.seq_tv.ptr.s->crckind, c2->g_inj);
					crc *retc = (crc*)GC_MALLOC(sizeof(crc));
					retc->crckind = SEQ_INJ;
					retc->g_inj = c2->g_inj;
					retc->crcdat.seq_tv.ptr.s = compose_lists(c1, c2->crcdat.seq_tv.ptr.s);
					return retc;
				}
			}
		}
	}

	printf("compose bad. c1: %d, c2: %d\n", c1->crckind, c2->crckind);
	exit(1);
}

#endif