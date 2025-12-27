#include <stdio.h>
#include <stdlib.h> //for abort
#include "coerce.h"
#include "gc.h"

ty tydyn = { .tykind = DYN };
ty tyint = { .tykind = BASE_INT };
ty tybool = { .tykind = BASE_BOOL };
ty tyunit = { .tykind = BASE_UNIT };
ty tyar = { .tykind = TYFUN, .tydat = { .tyfun = { .left = &tydyn, .right = &tydyn } } };
ty tyli = { .tykind = TYLIST, .tydat = { .tylist = &tydyn } };

crc crc_id = { .crckind = ID };
crc inj_INT = { .crckind = INJ, .crcdat = { .g = G_INT } };
crc crc_inj_INT = { .crckind = SEQ, .crcdat = { .two_crc = { .c1 = &crc_id, .c2=&inj_INT } } };
crc inj_BOOL = { .crckind = INJ, .crcdat = { .g = G_BOOL } };
crc crc_inj_BOOL = { .crckind = SEQ, .crcdat = { .two_crc = { .c1 = &crc_id, .c2=&inj_BOOL } } };
crc inj_UNIT = { .crckind = INJ, .crcdat = { .g = G_UNIT } };
crc crc_inj_UNIT = { .crckind = SEQ, .crcdat = { .two_crc = { .c1 = &crc_id, .c2=&inj_UNIT } } };
crc inj_AR = { .crckind = INJ, .crcdat = { .g = G_AR } };
crc inj_LI = { .crckind = INJ, .crcdat = { .g = G_LI } };

crc *make_crc_inj_ar (crc *g){
	crc *retcrc = (crc*)GC_MALLOC(sizeof(crc));
	retcrc->crckind = SEQ;
	retcrc->crcdat.two_crc.c1 = g;
	retcrc->crcdat.two_crc.c2 = &inj_AR;
	return retcrc;
}

crc *make_crc_inj_li (crc *g){
	crc *retcrc = (crc*)GC_MALLOC(sizeof(crc));
	retcrc->crckind = SEQ;
	retcrc->crcdat.two_crc.c1 = g;
	retcrc->crcdat.two_crc.c2 = &inj_LI;
	return retcrc;
}

crc *make_crc_proj(ground_ty g, ran_pol r_p, crc* i){
	crc *retcrc = (crc*)GC_MALLOC(sizeof(crc));
	retcrc->crckind = SEQ;
	retcrc->crcdat.two_crc.c1 = (crc*)GC_MALLOC(sizeof(crc));
	retcrc->crcdat.two_crc.c1->crckind = PROJ;
	retcrc->crcdat.two_crc.c1->crcdat.g = g;
	retcrc->crcdat.two_crc.c1->r_p = r_p;
	retcrc->crcdat.two_crc.c2 = i;
	return retcrc;
}

crc *make_crc_fun(crc *c1, crc *c2) {
	crc *retcrc = (crc*)GC_MALLOC(sizeof(crc));
	retcrc->crckind = FUN;
	retcrc->crcdat.two_crc.c1 = c1;
	retcrc->crcdat.two_crc.c2 = c2;	
	return retcrc;
}

crc *make_crc_list(crc *c) {
	crc *retcrc = (crc*)GC_MALLOC(sizeof(crc));
	retcrc->crckind = LIST;
	retcrc->crcdat.one_crc = c;
	return retcrc;
}

ty *newty() {
	ty *retty = (ty*)GC_MALLOC(sizeof(ty));
	retty->tykind = TYVAR;
	return retty;
}

int blame(ran_pol r_p){
	if(r_p.polarity==1) {
		printf("Blame on the expression side:\n");
	} else {
		printf("Blame on the environment side:\n");
	}
	printf("%sline %d, character %d -- line %d, character %d\n", r_p.filename, r_p.startline, r_p.startchr, r_p.endline, r_p.endchr);
	return 0;
}

ty *ty_find(ty *t) {
	// printf("tyfind: %p\n", t);
	if (t->tykind == SUBSTITUTED) {
		ty *t_ = ty_find(t->tydat.tv);
		// if (t_->tykind != TYVAR) {
		// 	*t = *t_;
		// } else {
			t->tydat.tv = t_;
		// }
		return t->tydat.tv;
	}
	return t;
}

crc* normalize_crc(crc *c) {
	// if (c->crckind == SEQ || c->crckind == FUN) {
	// 	c->crcdat.two_crc.c1 = normalize_crc(c->crcdat.two_crc.c1);
	// 	c->crcdat.two_crc.c2 = normalize_crc(c->crcdat.two_crc.c2);
	// 	return c;
	// } else 
	if (c->crckind == INJ_TV) {
		if (c->crcdat.tv->tykind == BASE_INT) {             // X! [X:=int] -> id;int!
			return &crc_inj_INT;
		} else if (c->crcdat.tv->tykind == BASE_BOOL) {
			return &crc_inj_BOOL;
		} else if (c->crcdat.tv->tykind == BASE_UNIT) {
			return &crc_inj_UNIT;
		} else if (c->crcdat.tv->tykind == TYFUN) {         // X! [X:=X1=>X2] -> X1?p=>X2!;(★→★)!
			crc *c1 = (crc*)GC_MALLOC(sizeof(crc));
			c1->crckind = PROJ_TV;
			c1->crcdat.tv = c->crcdat.tv->tydat.tyfun.left;
			// c1->r_p = 
			crc *c2 = (crc*)GC_MALLOC(sizeof(crc));
			c2->crckind = INJ_TV;
			c2->crcdat.tv = c->crcdat.tv->tydat.tyfun.right;
			crc *cfun = make_crc_fun(c1, c2);
			return make_crc_inj_ar(cfun);
		} else if (c->crcdat.tv->tykind == TYLIST) {         // X! [X:=[X1]] -> [X1!];[★]!
			crc *clist_ = (crc*)GC_MALLOC(sizeof(crc));
			clist_->crckind = INJ_TV;
			clist_->crcdat.tv = c->crcdat.tv->tydat.tylist;
			crc *clist = make_crc_list(clist_);
			return make_crc_inj_li(clist);
		} else if (c->crcdat.tv->tykind == SUBSTITUTED) {
			c->crcdat.tv = ty_find(c->crcdat.tv);
			return normalize_crc(c);
		} else {
			return c;
		}
	} else if (c->crckind == PROJ_TV) {
		if (c->crcdat.tv->tykind == BASE_INT) {				// X?p [X:=int] -> int?p;id
			return make_crc_proj(G_INT, c->r_p, &crc_id);
		} else if (c->crcdat.tv->tykind == BASE_BOOL) {
			return make_crc_proj(G_BOOL, c->r_p, &crc_id);
		} else if (c->crcdat.tv->tykind == BASE_UNIT) {
			return make_crc_proj(G_UNIT, c->r_p, &crc_id);
		} else if (c->crcdat.tv->tykind == TYFUN) {        // X?p [X:=X1=>X2] -> (★→★)?p;X1!=>X2?p
			crc *c1 = (crc*)GC_MALLOC(sizeof(crc));
			c1->crckind = INJ_TV;
			c1->crcdat.tv = c->crcdat.tv->tydat.tyfun.left;
			crc *c2 = (crc*)GC_MALLOC(sizeof(crc));
			c2->crckind = PROJ_TV;
			c2->crcdat.tv = c->crcdat.tv->tydat.tyfun.right;
			c2->r_p = c->r_p;
			crc *cfun = make_crc_fun(c1, c2);
			return make_crc_proj(G_AR, c->r_p, cfun);
		} else if (c->crcdat.tv->tykind == TYLIST) {        // X?p [X:=[X1]] -> [★]?p;[X1?p]
			crc *clist_ = (crc*)GC_MALLOC(sizeof(crc));
			clist_->crckind = PROJ_TV;
			clist_->r_p = c->r_p;
			clist_->crcdat.tv = c->crcdat.tv->tydat.tylist;
			crc *clist = make_crc_list(clist_);
			return make_crc_proj(G_LI, c->r_p, clist);
		} else if (c->crcdat.tv->tykind == SUBSTITUTED) {
			c->crcdat.tv = ty_find(c->crcdat.tv);
			return normalize_crc(c);
		} else {
			return c;
		}
	} else if (c->crckind == PROJ_INJ_TV) {
		if (c->crcdat.tv->tykind == BASE_INT) {                    // ?pX! [X:=int] -> int?p;id;int!
			return make_crc_proj(G_INT, c->r_p, &crc_inj_INT);
		} else if (c->crcdat.tv->tykind == BASE_BOOL) {
			return make_crc_proj(G_BOOL, c->r_p, &crc_inj_BOOL);
		} else if (c->crcdat.tv->tykind == BASE_UNIT) {
			return make_crc_proj(G_UNIT, c->r_p, &crc_inj_UNIT);
		} else if (c->crcdat.tv->tykind == TYFUN) {   				// ?pX! [X:=X1=>X2] -> (★→★)?p(?pX1!=>?pX2!);(★→★)!
			ty *t1 = c->crcdat.tv->tydat.tyfun.left;
			ty *t2 = c->crcdat.tv->tydat.tyfun.right;
			crc *c1 = (crc*)GC_MALLOC(sizeof(crc));
			c1->crckind = PROJ_INJ_TV;
			c1->crcdat.tv = t1;
			// c1->r_p = ;
			crc *c2 = (crc*)GC_MALLOC(sizeof(crc));
			c2->crckind = PROJ_INJ_TV;
			c2->crcdat.tv = t2;
			c2->r_p = c->r_p;
			crc *cfun = make_crc_fun(c1, c2);
			crc *car = make_crc_inj_ar(cfun);
			return make_crc_proj(G_AR, c->r_p, car);
		} else if (c->crcdat.tv->tykind == TYLIST) {				// ?pX! [X:=[X1]] -> [★]?p[?pX1!];[★]!
			ty *t = c->crcdat.tv->tydat.tylist;
			crc *clist_ = (crc*)GC_MALLOC(sizeof(crc));
			clist_->crckind = PROJ_INJ_TV;
			clist_->crcdat.tv = t;
			clist_->r_p = c->r_p;
			crc *clist = make_crc_list(clist_);
			crc *cli = make_crc_inj_li(clist);
			return make_crc_proj(G_LI, c->r_p, cli);
		} else if (c->crcdat.tv->tykind == SUBSTITUTED) {
			c->crcdat.tv = ty_find(c->crcdat.tv);
			return normalize_crc(c);
		} else {
			return c;
		}
	}
	printf("normalize_crc bad. crckind: %d", c->crckind);
	exit(1);
}

crc* compose(crc *c1, crc *c2) {
	// printf("c1: %d, c2: %d\n", c1->crckind, c2->crckind);
	if (c1->crckind == ID) {                                           // id;;s -> s
		return c2;
	} else if (c2->crckind == ID) {		 							   // s;;id -> s
		return c1;
	} else if (c1->crckind == SEQ && c1->crcdat.two_crc.c1->crckind == PROJ) { // G?p;i;;s -> G?p;(i;;s)
		// printf("  c1.c1:%d, c1.c2:%d\n", c1->crcdat.two_crc.c1->crckind, c1->crcdat.two_crc.c2->crckind);
		crc *retc = (crc*)GC_MALLOC(sizeof(crc));
		retc->crckind = SEQ;
		retc->crcdat.two_crc.c1 = c1->crcdat.two_crc.c1;
		retc->crcdat.two_crc.c2 = compose(c1->crcdat.two_crc.c2, c2);
		return retc;
	} else if (c1->crckind == PROJ_TV) {                                // X?p;;s
		c1 = normalize_crc(c1);
		if (c1->crckind != PROJ_TV) {
			return compose(c1, c2);
		// } else if (c2->crckind == ID) {
		// 	return c1;
		} else if (c2->crckind == INJ_TV) {                              // X?p;;X! -> ?pX!
			c2 = normalize_crc(c2);
			if (c2->crckind != INJ_TV) {
				return compose(c1, c2);
			} else {
				crc *retc = (crc*)GC_MALLOC(sizeof(crc));
				retc->crckind = PROJ_INJ_TV;
				retc->crcdat.tv = c1->crcdat.tv;
				retc->r_p = c1->r_p;				
				return retc;
			} 
		} 
	} else if (c1->crckind == INJ_TV) {								    // X!;;s
		c1 = normalize_crc(c1);
		if (c1->crckind != INJ_TV) {								    
			return compose(c1, c2);
		} else if (c2->crckind == SEQ && c2->crcdat.two_crc.c1->crckind == PROJ) {      //X!;;G?p;i
			// printf("  c2.c1:%d, c2.c2:%d\n", c2->crcdat.two_crc.c1->crckind, c2->crcdat.two_crc.c2->crckind);
			if (c2->crcdat.two_crc.c1->crcdat.g == G_AR) {                                //X!;;(★→★)?p;i -> X1?p=>X2!;;i [X:=X1=>X2]
				// printf("DTI : arrow was inferred\n");
				c1->crcdat.tv->tykind = TYFUN;
				c1->crcdat.tv->tydat.tyfun.left = newty();
				c1->crcdat.tv->tydat.tyfun.right = newty();
				// printf("%p <- (%p=>%p)\n", c1->crcdat.tv, c1->crcdat.tv->tydat.tyfun.left, c1->crcdat.tv->tydat.tyfun.right);
				crc *cfun1 = (crc*)GC_MALLOC(sizeof(crc));
				cfun1->crckind = PROJ_TV;
				cfun1->crcdat.tv = c1->crcdat.tv->tydat.tyfun.left;
				crc *cfun2 = (crc*)GC_MALLOC(sizeof(crc));
				cfun2->crckind = INJ_TV;
				cfun2->crcdat.tv = c1->crcdat.tv->tydat.tyfun.right;
				crc *cfun = make_crc_fun(cfun1, cfun2);
				return compose(cfun, c2->crcdat.two_crc.c2);
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_LI) {                        //X!;;[★]?p;i -> [X1!];;i [X:=[X1]]
				// printf("DTI : list was inferred\n");
				c1->crcdat.tv->tykind = TYLIST;
				c1->crcdat.tv->tydat.tylist = newty();
				// printf("%p <- [%p]\n", c1->crcdat.tv, c1->crcdat.tv->tydat.tylist);
				crc *clist_ = (crc*)GC_MALLOC(sizeof(crc));
				clist_->crckind = INJ_TV;
				clist_->crcdat.tv = c1->crcdat.tv->tydat.tylist;
				crc *clist = make_crc_list(clist_);
				return compose(clist, c2->crcdat.two_crc.c2);
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_INT) {                     //X!;;int?p;i -> i [X:=int]
				// printf("DTI : int was inferred\n");
				// printf("%p <- int\n", c1->crcdat.tv);
				*c1->crcdat.tv = tyint;
				return c2->crcdat.two_crc.c2;
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_BOOL) {
				// printf("DTI : bool was inferred\n");
				// printf("%p <- bool\n", c1->crcdat.tv);
				*c1->crcdat.tv = tybool;
				return c2->crcdat.two_crc.c2;
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_UNIT) {
				// printf("DTI : unit was inferred\n");
				// printf("%p <- unit\n", c1->crcdat.tv);
				*c1->crcdat.tv = tyunit;
				return c2->crcdat.two_crc.c2;
			}		
		} else if (c2->crckind == PROJ_TV) {                                            //X!;;Y?p
			c2 = normalize_crc(c2);
			if (c2->crckind != PROJ_TV) {
				return compose(c1, c2);
			} else if (c1->crcdat.tv == c2->crcdat.tv) {								//X!;;X?p -> id
				return &crc_id;
			} else {                                                                    //X!;;Y?p -> id [X:=Y]
				// printf("DTI : tyvar was inferred\n");
				// printf("%p <- %p\n", c1->crcdat.tv, c2->crcdat.tv);
				c1->crcdat.tv->tykind = SUBSTITUTED;
				c1->crcdat.tv->tydat.tv = c2->crcdat.tv;
				return &crc_id;
			}
		} else if (c2->crckind == PROJ_INJ_TV) {									    //X!;;?pY!
			c2 = normalize_crc(c2);
			if (c2->crckind != PROJ_INJ_TV) {
				return compose(c1, c2);
			} else if (c1->crcdat.tv == c2->crcdat.tv) {                                //X!;;?pX! -> X!
				return c1;												// this is not real, but correct
			} else {																	//X!;;?pY! -> Y! [X:=Y]
				// printf("DTI : tyvar was inferred\n");
				// printf("%p <- %p\n", c1->crcdat.tv, c2->crcdat.tv);
				c1->crcdat.tv->tykind = SUBSTITUTED;
				c1->crcdat.tv->tydat.tv = c2->crcdat.tv;
				return c1;
			}
		}
	} else if (c1->crckind == PROJ_INJ_TV) {											//?pX!;;s
		c1 = normalize_crc(c1);
		if (c1->crckind != PROJ_INJ_TV) {
			return compose(c1, c2);
		} else if (c2->crckind == SEQ && c2->crcdat.two_crc.c1->crckind == PROJ) {      //?pX!;;G?q;i
			// printf("  c2.c1:%d, c2.c2:%d\n", c2->crcdat.two_crc.c1->crckind, c2->crcdat.two_crc.c2->crckind);
			if (c2->crcdat.two_crc.c1->crcdat.g == G_AR) {                                //?pX!;;(★→★)?q;i -> (★→★)?p;?qX1!=>?pX2!;;i [X:=X1=>X2]
				// printf("DTI : arrow was inferred\n");
				c1->crcdat.tv->tykind = TYFUN;
				c1->crcdat.tv->tydat.tyfun.left = newty();
				c1->crcdat.tv->tydat.tyfun.right = newty();
				// printf("%p <- (%p=>%p)\n", c1->crcdat.tv, c1->crcdat.tv->tydat.tyfun.left, c1->crcdat.tv->tydat.tyfun.right);
				crc *cfun1 = (crc*)GC_MALLOC(sizeof(crc));
				cfun1->crckind = PROJ_INJ_TV;
				cfun1->crcdat.tv = c1->crcdat.tv->tydat.tyfun.left;
				// cfun1->r_p = 
				crc *cfun2 = (crc*)GC_MALLOC(sizeof(crc));
				cfun2->crckind = PROJ_INJ_TV;
				cfun2->crcdat.tv = c1->crcdat.tv->tydat.tyfun.right;
				cfun2->r_p = c1->r_p;
				crc *cfun = make_crc_fun(cfun1, cfun2);
				crc *cprojfun = make_crc_proj(G_AR, c1->r_p, cfun);
				return compose(cprojfun, c2->crcdat.two_crc.c2);
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_LI) {                                //?pX!;;[★]?q;i -> [★]?p;[?qX1!];;i [X:=[X1]]
				// printf("DTI : list was inferred\n");
				c1->crcdat.tv->tykind = TYLIST;
				c1->crcdat.tv->tydat.tylist = newty();
				// printf("%p <- [%p])\n", c1->crcdat.tv, c1->crcdat.tv->tydat.tylist);
				crc *clist_ = (crc*)GC_MALLOC(sizeof(crc));
				clist_->crckind = PROJ_INJ_TV;
				clist_->crcdat.tv = c1->crcdat.tv->tydat.tylist;
				// clist_->r_p = c1->r_p;
				crc *clist = make_crc_list(clist_);
				crc *cprojlist = make_crc_proj(G_LI, c1->r_p, clist);
				return compose(cprojlist, c2->crcdat.two_crc.c2);
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_INT) {                     //?pX!;;int?q;i -> int?p;i [X:=int]
				// printf("DTI : int was inferred\n");
				// printf("%p <- int\n", c1->crcdat.tv);
				*c1->crcdat.tv = tyint;
				return make_crc_proj(G_INT, c1->r_p, c2->crcdat.two_crc.c2);
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_BOOL) {
				// printf("DTI : bool was inferred\n");
				// printf("%p <- bool\n", c1->crcdat.tv);
				*c1->crcdat.tv = tybool;
				return make_crc_proj(G_BOOL, c1->r_p, c2->crcdat.two_crc.c2);
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_UNIT) {
				// printf("DTI : unit was inferred\n");
				// printf("%p <- unit\n", c1->crcdat.tv);
				*c1->crcdat.tv = tyunit;
				return make_crc_proj(G_UNIT, c1->r_p, c2->crcdat.two_crc.c2);
			}		
		} else if (c2->crckind == PROJ_TV) {                                            //?pX!;;Y?q
			c2 = normalize_crc(c2);
			if (c2->crckind != PROJ_TV) {
				return compose(c1, c2);
			} else if (c1->crcdat.tv == c2->crcdat.tv) {								//?pX!;;X?q -> X?p
				c2->r_p = c1->r_p;
				return c2;
			} else {                                                                    //?pX!;;Y?q -> Y?p [X:=Y]
				// printf("DTI : tyvar was inferred\n");
				// printf("%p <- %p\n", c1->crcdat.tv, c2->crcdat.tv);
				c1->crcdat.tv->tykind = SUBSTITUTED;
				c1->crcdat.tv->tydat.tv = c2->crcdat.tv;
				c2->r_p = c1->r_p;
				return c2;
			}
		} else if (c2->crckind == PROJ_INJ_TV) {									    //?pX!;;?qY!
			c2 = normalize_crc(c2);
			if (c2->crckind != PROJ_INJ_TV) {
				return compose(c1, c2);
			} else if (c1->crcdat.tv == c2->crcdat.tv) {                                //?pX!;;?qX! -> ?pX!
				return c1;												// this is not real, but correct
			} else {																    //?pX!;;?pY! -> ?pY! [X:=Y]
				// printf("DTI : tyvar was inferred\n");
				// printf("%p <- %p\n", c1->crcdat.tv, c2->crcdat.tv);
				c1->crcdat.tv->tykind = SUBSTITUTED;
				c1->crcdat.tv->tydat.tv = c2->crcdat.tv;
				return c1;
			}
		}
	} else if (c1->crckind == SEQ && c1->crcdat.two_crc.c2->crckind == INJ) {           //g;G!;;s
		// printf("  c1.c1:%d, c1.c2:%d\n", c1->crcdat.two_crc.c1->crckind, c1->crcdat.two_crc.c2->crckind);
		if (c2->crckind == SEQ && c2->crcdat.two_crc.c1->crckind == PROJ) {              //g;G!;;H?p;i
			// printf("  c2.c1:%d, c2.c2:%d\n", c2->crcdat.two_crc.c1->crckind, c2->crcdat.two_crc.c2->crckind);
			// printf("    c1.c2.g:%d, c2.c1.g:%d\n", c1->crcdat.two_crc.c2->crcdat.g, c2->crcdat.two_crc.c1->crcdat.g);
			if (c1->crcdat.two_crc.c2->crcdat.g == c2->crcdat.two_crc.c1->crcdat.g) {   //g;G!;;G?p;i -> g;;i
				return compose(c1->crcdat.two_crc.c1, c2->crcdat.two_crc.c2);
			} else {                                                                 //g;G!;;H?p;i -> bot^p (if G neq H)
				crc *retc = (crc*)GC_MALLOC(sizeof(crc));
				retc->crckind = BOT;
				retc->r_p = c2->crcdat.two_crc.c1->r_p;
				return retc;
			}
		} else if (c2->crckind == PROJ_TV) {										   	//g;G!;;X?p
			c2 = normalize_crc(c2);
			if (c2->crckind != PROJ_TV) {
				return compose(c1, c2);
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_AR) {						//g;(★→★)!;;X?p -> g;;X1!=>X2?p [X:=X1=>X2]
				// printf("DTI : arrow was inferred\n");
				c2->crcdat.tv->tykind = TYFUN;
				c2->crcdat.tv->tydat.tyfun.left = newty();
				c2->crcdat.tv->tydat.tyfun.right = newty();
				// printf("%p <- (%p=>%p)\n", c2->crcdat.tv, c2->crcdat.tv->tydat.tyfun.left, c2->crcdat.tv->tydat.tyfun.right);
				crc *cfun1 = (crc*)GC_MALLOC(sizeof(crc));
				cfun1->crckind = INJ_TV;
				cfun1->crcdat.tv = c2->crcdat.tv->tydat.tyfun.left;
				crc *cfun2 = (crc*)GC_MALLOC(sizeof(crc));
				cfun2->crckind = PROJ_TV;
				cfun2->crcdat.tv = c2->crcdat.tv->tydat.tyfun.right;
				crc *cfun = make_crc_fun(cfun1, cfun2);
				return compose(c1->crcdat.two_crc.c1, cfun);
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_LI) {						//g;[★]!;;X?p -> g;;[X1?p] [X:=[X1]]
				// printf("DTI : list was inferred\n");
				c2->crcdat.tv->tykind = TYLIST;
				c2->crcdat.tv->tydat.tylist = newty();
				// printf("%p <- [%p]\n", c2->crcdat.tv, c2->crcdat.tv->tydat.tylist);
				crc *clist_ = (crc*)GC_MALLOC(sizeof(crc));
				clist_->crckind = PROJ_TV;
				clist_->crcdat.tv = c2->crcdat.tv->tydat.tylist;
				crc *clist = make_crc_list(clist_);
				return compose(c1->crcdat.two_crc.c1, clist);
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_INT) {                      //g;int!;;X?p -> g [X:=int]
				// printf("DTI : int was inferred\n");
				// printf("%p <- int\n", c2->crcdat.tv);
				*c2->crcdat.tv = tyint;
				return c1->crcdat.two_crc.c1;
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_BOOL) {
				// printf("DTI : bool was inferred\n");
				// printf("%p <- bool\n", c2->crcdat.tv);
				*c2->crcdat.tv = tybool;
				return c1->crcdat.two_crc.c1;
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_UNIT) {
				// printf("DTI : unit was inferred\n");
				// printf("%p <- unit\n", c2->crcdat.tv);
				*c2->crcdat.tv = tyunit;
				return c1->crcdat.two_crc.c1;
			}
		} else if (c2->crckind == PROJ_INJ_TV) {									   //g;G!;;?pX!
			c2 = normalize_crc(c2);
			if (c2->crckind != PROJ_INJ_TV) {
				return compose(c1, c2);
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_AR) {						//g;(★→★)!;;?pX! -> g;;X1!=>X2?p;(★->★)! [X:=X1=>X2]
				// printf("DTI : arrow was inferred\n");
				c2->crcdat.tv->tykind = TYFUN;
				c2->crcdat.tv->tydat.tyfun.left = newty();
				c2->crcdat.tv->tydat.tyfun.right = newty();
				// printf("%p <- (%p=>%p)\n", c2->crcdat.tv, c2->crcdat.tv->tydat.tyfun.left, c2->crcdat.tv->tydat.tyfun.right);
				crc *cfun1 = (crc*)GC_MALLOC(sizeof(crc));
				cfun1->crckind = PROJ_INJ_TV;
				cfun1->crcdat.tv = c2->crcdat.tv->tydat.tyfun.left;
				crc *cfun2 = (crc*)GC_MALLOC(sizeof(crc));
				cfun2->crckind = PROJ_INJ_TV;
				cfun2->crcdat.tv = c2->crcdat.tv->tydat.tyfun.right;
				crc *cfun = make_crc_fun(cfun1, cfun2);
				crc *cfuninj = make_crc_inj_ar(cfun);
				return compose(c1->crcdat.two_crc.c1, cfuninj);
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_LI) {						//g;[★]!;;?pX! -> g;;[?pX1!];[★]! [X:=[X1]]
				// printf("DTI : list was inferred\n");
				c2->crcdat.tv->tykind = TYLIST;
				c2->crcdat.tv->tydat.tylist = newty();
				// printf("%p <- [%p]\n", c2->crcdat.tv, c2->crcdat.tv->tydat.tylist);
				crc *clist_ = (crc*)GC_MALLOC(sizeof(crc));
				clist_->crckind = PROJ_INJ_TV;
				clist_->crcdat.tv = c2->crcdat.tv->tydat.tylist;
				crc *clist = make_crc_list(clist_);
				crc *clistinj = make_crc_inj_li(clist);
				return compose(c1->crcdat.two_crc.c1, clistinj);
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_INT) {                      //g;int!;;?pX! -> g;;id;int! -> g;int! [X:=int]
				// printf("DTI : int was inferred\n");
				// printf("%p <- int\n", c2->crcdat.tv);
				*c2->crcdat.tv = tyint;
				return c1;
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_BOOL) {
				// printf("DTI : bool was inferred\n");
				// printf("%p <- bool\n", c2->crcdat.tv);
				*c2->crcdat.tv = tybool;
				return c1;
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_UNIT) {
				// printf("DTI : unit was inferred\n");
				// printf("%p <- unit\n", c2->crcdat.tv);
				*c2->crcdat.tv = tyunit;
				return c1;
			}
		}
	} else if (c1->crckind == BOT) {
		return c1;
	} else if (c2->crckind == INJ_TV) {
		return compose(c1, normalize_crc(c2));
	} else if (c2->crckind == BOT) {
		return c2;
	} else if (c2->crckind == SEQ && c2->crcdat.two_crc.c2->crckind == INJ) {          //g;;h;G! -> (g;;h);G!
		// printf("  c2.c1:%d, c2.c2:%d\n", c2->crcdat.two_crc.c1->crckind, c2->crcdat.two_crc.c2->crckind);
		crc *retc = (crc*)GC_MALLOC(sizeof(crc));
		retc->crckind = SEQ;
		retc->crcdat.two_crc.c1 = compose(c1, c2->crcdat.two_crc.c1);
		retc->crcdat.two_crc.c2 = c2->crcdat.two_crc.c2;
		return retc;
	} else if (c1->crckind == FUN && c2->crckind == FUN) {                             //s=>t;;s'=>t' -> s';;s=>t;;t'
		crc *retc = (crc*)GC_MALLOC(sizeof(crc));
		retc->crckind = FUN;
		retc->crcdat.two_crc.c1 = compose(c2->crcdat.two_crc.c1, c1->crcdat.two_crc.c1);
		retc->crcdat.two_crc.c2 = compose(c1->crcdat.two_crc.c2, c2->crcdat.two_crc.c2);
		if (retc->crcdat.two_crc.c1->crckind == ID && retc->crcdat.two_crc.c2->crckind == ID) { //s=>t;;s'=>t' -> id (if s=id and t=id)
			return &crc_id;
		} else {
			return retc;
		}
	} else if (c1->crckind == LIST && c2->crckind == LIST) {
		crc *retc = (crc*)GC_MALLOC(sizeof(crc));
		retc->crckind = LIST;
		retc->crcdat.one_crc = compose(c1->crcdat.one_crc, c2->crcdat.one_crc);
		if (retc->crcdat.one_crc->crckind == ID) {
			return &crc_id;
		} else {
			return retc;
		}
	}
	printf("compose bad. c1: %d, c2: %d\n", c1->crckind, c2->crckind);
	exit(1);
}

int did_not_match() {
	printf("didn't match");
	exit(1);
}