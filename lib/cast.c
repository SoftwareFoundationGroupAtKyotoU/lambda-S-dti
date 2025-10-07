#include <stdio.h>
#include <stdlib.h> //for abort
#include "cast.h"
#include "gc.h"

ty tydyn = { .tykind = DYN };
ty tyint = { .tykind = BASE_INT };
ty tybool = { .tykind = BASE_BOOL };
ty tyunit = { .tykind = BASE_UNIT };
ty tyar = { .tykind = TYFUN, .tydat = { .tyfun = { .left = &tydyn, .right = &tydyn } } };

crc crc_id = { .crckind = ID };
crc inj_INT = { .crckind = INJ, .crcdat = { .g = G_INT } };
crc crc_inj_INT = { .crckind = SEQ, .crcdat = { .two_crc = { .c1 = &crc_id, .c2=&inj_INT } } };
crc inj_BOOL = { .crckind = INJ, .crcdat = { .g = G_BOOL } };
crc crc_inj_BOOL = { .crckind = SEQ, .crcdat = { .two_crc = { .c1 = &crc_id, .c2=&inj_BOOL } } };
crc inj_UNIT = { .crckind = INJ, .crcdat = { .g = G_UNIT } };
crc crc_inj_UNIT = { .crckind = SEQ, .crcdat = { .two_crc = { .c1 = &crc_id, .c2=&inj_UNIT } } };
crc inj_AR = { .crckind = INJ, .crcdat = { .g = G_AR } };

crc *make_crc_inj_ar (crc *g){
	crc *retcrc = (crc*)GC_MALLOC(sizeof(crc));
	retcrc->crckind = SEQ;
	retcrc->crcdat.two_crc.c1 = g;
	retcrc->crcdat.two_crc.c2 = &inj_AR;
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
	printf("tyfind: %p\n", t);
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
			return make_crc_proj(G_UNIT, c->r_p, &crc_inj_UNIT);   // ?pX! [X:=X1=>X2] -> (★→★)?p(?pX1!=>?pX2!);(★→★)!
		} else if (c->crcdat.tv->tykind == TYFUN) {
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
	} else if (c1->crckind == INJ_TV) {								    // X!
		c1 = normalize_crc(c1);
		if (c1->crckind != INJ_TV) {								    
			return compose(c1, c2);
		} else if (c2->crckind == SEQ && c2->crcdat.two_crc.c1->crckind == PROJ) {      //X!;;G?p;i
			// printf("  c2.c1:%d, c2.c2:%d\n", c2->crcdat.two_crc.c1->crckind, c2->crcdat.two_crc.c2->crckind);
			if (c2->crcdat.two_crc.c1->crcdat.g == G_AR) {                                //X!;;(★→★)?p;i -> X1?p=>X2!;;i [X:=X1=>X2]
				printf("DTI : arrow was inferred\n");
				c1->crcdat.tv->tykind = TYFUN;
				c1->crcdat.tv->tydat.tyfun.left = newty();
				c1->crcdat.tv->tydat.tyfun.right = newty();
				printf("%p <- (%p=>%p)\n", c1->crcdat.tv, c1->crcdat.tv->tydat.tyfun.left, c1->crcdat.tv->tydat.tyfun.right);
				crc *cfun1 = (crc*)GC_MALLOC(sizeof(crc));
				cfun1->crckind = PROJ_TV;
				cfun1->crcdat.tv = c1->crcdat.tv->tydat.tyfun.left;
				crc *cfun2 = (crc*)GC_MALLOC(sizeof(crc));
				cfun2->crckind = INJ_TV;
				cfun2->crcdat.tv = c1->crcdat.tv->tydat.tyfun.right;
				crc *cfun = make_crc_fun(cfun1, cfun2);
				return compose(cfun, c2->crcdat.two_crc.c2);
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_INT) {                     //X!;;int?p;i -> i [X:=int]
				printf("DTI : int was inferred\n");
				printf("%p <- int\n", c1->crcdat.tv);
				*c1->crcdat.tv = tyint;
				return c2->crcdat.two_crc.c2;
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_BOOL) {
				printf("DTI : bool was inferred\n");
				printf("%p <- bool\n", c1->crcdat.tv);
				*c1->crcdat.tv = tybool;
				return c2->crcdat.two_crc.c2;
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_UNIT) {
				printf("DTI : unit was inferred\n");
				printf("%p <- unit\n", c1->crcdat.tv);
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
				printf("DTI : tyvar was inferred\n");
				printf("%p <- %p\n", c1->crcdat.tv, c2->crcdat.tv);
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
				printf("DTI : tyvar was inferred\n");
				printf("%p <- %p\n", c1->crcdat.tv, c2->crcdat.tv);
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
				printf("DTI : arrow was inferred\n");
				c1->crcdat.tv->tykind = TYFUN;
				c1->crcdat.tv->tydat.tyfun.left = newty();
				c1->crcdat.tv->tydat.tyfun.right = newty();
				printf("%p <- (%p=>%p)\n", c1->crcdat.tv, c1->crcdat.tv->tydat.tyfun.left, c1->crcdat.tv->tydat.tyfun.right);
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
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_INT) {                     //?pX!;;int?q;i -> int?p;i [X:=int]
				printf("DTI : int was inferred\n");
				printf("%p <- int\n", c1->crcdat.tv);
				*c1->crcdat.tv = tyint;
				return make_crc_proj(G_INT, c1->r_p, c2->crcdat.two_crc.c2);
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_BOOL) {
				printf("DTI : bool was inferred\n");
				printf("%p <- bool\n", c1->crcdat.tv);
				*c1->crcdat.tv = tybool;
				return make_crc_proj(G_BOOL, c1->r_p, c2->crcdat.two_crc.c2);
			} else if (c2->crcdat.two_crc.c1->crcdat.g == G_UNIT) {
				printf("DTI : unit was inferred\n");
				printf("%p <- unit\n", c1->crcdat.tv);
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
				printf("DTI : tyvar was inferred\n");
				printf("%p <- %p\n", c1->crcdat.tv, c2->crcdat.tv);
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
				printf("DTI : tyvar was inferred\n");
				printf("%p <- %p\n", c1->crcdat.tv, c2->crcdat.tv);
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
			if (c1->crcdat.two_crc.c2->crcdat.g == c2->crcdat.two_crc.c1->crcdat.g) {   //g;G!;;G?pi -> g;;i
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
				printf("DTI : arrow was inferred\n");
				c2->crcdat.tv->tykind = TYFUN;
				c2->crcdat.tv->tydat.tyfun.left = newty();
				c2->crcdat.tv->tydat.tyfun.right = newty();
				printf("%p <- (%p=>%p)\n", c2->crcdat.tv, c2->crcdat.tv->tydat.tyfun.left, c2->crcdat.tv->tydat.tyfun.right);
				crc *cfun1 = (crc*)GC_MALLOC(sizeof(crc));
				cfun1->crckind = INJ_TV;
				cfun1->crcdat.tv = c2->crcdat.tv->tydat.tyfun.left;
				crc *cfun2 = (crc*)GC_MALLOC(sizeof(crc));
				cfun2->crckind = PROJ_TV;
				cfun2->crcdat.tv = c2->crcdat.tv->tydat.tyfun.right;
				crc *cfun = make_crc_fun(cfun1, cfun2);
				return compose(c1->crcdat.two_crc.c1, cfun);
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_INT) {                      //g;int!;;X?p -> g [X:=int]
				printf("DTI : int was inferred\n");
				printf("%p <- int\n", c2->crcdat.tv);
				*c2->crcdat.tv = tyint;
				return c1->crcdat.two_crc.c1;
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_BOOL) {
				printf("DTI : bool was inferred\n");
				printf("%p <- bool\n", c2->crcdat.tv);
				*c2->crcdat.tv = tybool;
				return c1->crcdat.two_crc.c1;
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_UNIT) {
				printf("DTI : unit was inferred\n");
				printf("%p <- unit\n", c2->crcdat.tv);
				*c2->crcdat.tv = tyunit;
				return c1->crcdat.two_crc.c1;
			}
		} else if (c2->crckind == PROJ_INJ_TV) {									   //g;G!;;?pX!
			c2 = normalize_crc(c2);
			if (c2->crckind != PROJ_INJ_TV) {
				return compose(c1, c2);
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_AR) {						//g;(★→★)!;;X?p -> g;;X1!=>X2?p [X:=X1=>X2]
				printf("DTI : arrow was inferred\n");
				c2->crcdat.tv->tykind = TYFUN;
				c2->crcdat.tv->tydat.tyfun.left = newty();
				c2->crcdat.tv->tydat.tyfun.right = newty();
				printf("%p <- (%p=>%p)\n", c2->crcdat.tv, c2->crcdat.tv->tydat.tyfun.left, c2->crcdat.tv->tydat.tyfun.right);
				crc *cfun1 = (crc*)GC_MALLOC(sizeof(crc));
				cfun1->crckind = PROJ_INJ_TV;
				cfun1->crcdat.tv = c2->crcdat.tv->tydat.tyfun.left;
				crc *cfun2 = (crc*)GC_MALLOC(sizeof(crc));
				cfun2->crckind = PROJ_INJ_TV;
				cfun2->crcdat.tv = c2->crcdat.tv->tydat.tyfun.right;
				crc *cfun = make_crc_fun(cfun1, cfun2);
				crc *cfuninj = make_crc_inj_ar(cfun);
				return compose(c1->crcdat.two_crc.c1, cfuninj);
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_INT) {                      //g;int!;;X?p -> g [X:=int]
				printf("DTI : int was inferred\n");
				printf("%p <- int\n", c2->crcdat.tv);
				*c2->crcdat.tv = tyint;
				return c1;
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_BOOL) {
				printf("DTI : bool was inferred\n");
				printf("%p <- bool\n", c2->crcdat.tv);
				*c2->crcdat.tv = tybool;
				return c1;
			} else if (c1->crcdat.two_crc.c2->crcdat.g == G_UNIT) {
				printf("DTI : unit was inferred\n");
				printf("%p <- unit\n", c2->crcdat.tv);
				*c2->crcdat.tv = tyunit;
				return c1;
			}
		}
	} else if (c1->crckind == BOT) {
		return c1;
	} else if (c2->crckind == BOT) {
		return c2;
	} else if (c2->crckind == SEQ && c2->crcdat.two_crc.c2->crckind == INJ) {          //g;;h;G! -> (g;;h);G!
		// printf("  c2.c1:%d, c2.c2:%d\n", c2->crcdat.two_crc.c1->crckind, c2->crcdat.two_crc.c2->crckind);
		crc *retc = (crc*)GC_MALLOC(sizeof(crc));
		retc->crckind = SEQ;
		retc->crcdat.two_crc.c1 = compose(c1, c2->crcdat.two_crc.c1);
		retc = c2->crcdat.two_crc.c2;
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
	}
	printf("compose bad. c1: %d, c2: %d\n", c1->crckind, c2->crckind);
	exit(1);
}

value coerce(value v, crc *s) {
	// printf("coerce c:%d\n", s->crckind);
	value retv;

	if (s->crckind == ID) { // v<id> -> v
		retv = v;
	} else if (s->crckind = BOT) { // v<bot^p> -> blame p
		blame(s->r_p);
		exit(1);
	} else if (s->crckind == FUN) { // v<s'=>t'>
		if (v.f->funkind == WRAPPED) { // u<<s=>t>><s'=>t'>
			crc *c1 = compose(s->crcdat.two_crc.c1, v.f->fundat.wrap.c_arg);
			crc *c2 = compose(v.f->fundat.wrap.c_res, s->crcdat.two_crc.c2);
			if (c1->crckind == ID && c2->crckind == ID) {    // u<<s=>t>><s'=>t'> -> u<id> -> u
				retv.f = v.f->fundat.wrap.w;
			} else {										 // u<<s=>t>><s'=>t'> -> u<s';;s=>t;;t'> -> u<<s';;s=>t;;t'>>
				retv.f = (fun*)GC_MALLOC(sizeof(fun));
				retv.f->funkind = WRAPPED;
				retv.f->fundat.wrap.w = v.f->fundat.wrap.w;
				retv.f->fundat.wrap.c_arg = c1;
				retv.f->fundat.wrap.c_res = c2;
			}
		} else {                   // u<s'=>t'> -> u<<s'=>t'>>
			retv.f = (fun*)GC_MALLOC(sizeof(fun));
			retv.f->funkind = WRAPPED;
			retv.f->fundat.wrap.w = v.f;
			retv.f->fundat.wrap.c_arg = s->crcdat.two_crc.c1;
			retv.f->fundat.wrap.c_res = s->crcdat.two_crc.c2;
		}
	} else if (s->crckind == SEQ && s->crcdat.two_crc.c1->crckind == FUN) { // v<s'=>t';G!>
		retv.d = (dyn*)GC_MALLOC(sizeof(dyn));
		retv.d->v = (value*)GC_MALLOC(sizeof(value));
		if (v.f->funkind == WRAPPED) {                                      // u<<s=>t>><s'=>t';G!>
			crc *c1 = compose(s->crcdat.two_crc.c1->crcdat.two_crc.c1, v.f->fundat.wrap.c_arg);
			crc *c2 = compose(v.f->fundat.wrap.c_res, s->crcdat.two_crc.c1->crcdat.two_crc.c2);
			retv.d->v->f = v.f->fundat.wrap.w;
			retv.d->d = (crc*)GC_MALLOC(sizeof(crc));
			retv.d->d->crckind = SEQ;
			retv.d->d->crcdat.two_crc.c2 = s->crcdat.two_crc.c2;
			if (c1->crckind == ID && c2->crckind == ID) { // u<<s=>t>><s'=>t';G!> -> u<id;G!> -> u<<id;G!>>
				retv.d->d->crcdat.two_crc.c1 = c1;
			} else { 									// u<<s=>t>><s'=>t';G!> -> u<s';;s=>t;;t';G!> -> u<<s';;s=>t;;t';G!>>
				retv.d->d->crcdat.two_crc.c1 = (crc*)GC_MALLOC(sizeof(crc));
				retv.d->d->crcdat.two_crc.c1->crckind = FUN;
				retv.d->d->crcdat.two_crc.c1->crcdat.two_crc.c1 = c1;
				retv.d->d->crcdat.two_crc.c1->crcdat.two_crc.c2 = c2;
			}
		} else { // u<s'=>t';G!> -> u<<s'=>t';G!>>
			retv.d->v->f = v.f;
			retv.d->d = s;
		}
	} else if (s->crckind == SEQ && s->crcdat.two_crc.c2->crckind == INJ) { // v<id;G!> -> v<<id;G!>>
		retv.d = (dyn*)GC_MALLOC(sizeof(dyn)); 
		retv.d->v = (value*)GC_MALLOC(sizeof(value));
		*retv.d->v = v;
		retv.d->d = s;
	 } else if (s->crckind == INJ_TV) {
		retv = coerce(v, normalize_crc(s));
	 	// retv.d = (dyn*)GC_MALLOC(sizeof(dyn));
	 	// retv.d->v = (value*)GC_MALLOC(sizeof(value));
	 	// *retv.d->v = v;
	 	// retv.d->d = s;
	} else {									// v<G?p;i> = u<<d>><G?p;i>, v<X?p> = u<<d>><X?p>, v<?pX!> = u<<d>><?pX!>
		crc *c1 = compose(v.d->d, s);
		// printf("composed c:%d\n", c1->crckind);
		if (c1->crckind == ID) {                // u<<d>><s> -> u<id> -> u
			retv = *v.d->v;
		} else if (c1->crckind == FUN) {        // u<<d>><s> -> u<s=>t> -> u<<s=>t>>
			retv.f = (fun*)GC_MALLOC(sizeof(fun));
			retv.f->funkind = WRAPPED;
			retv.f->fundat.wrap.w = v.d->v->f;
			retv.f->fundat.wrap.c_arg = c1->crcdat.two_crc.c1;
			retv.f->fundat.wrap.c_res = c1->crcdat.two_crc.c2;
		} else {                                // u<<d>><s> -> u<d> -> u<<d>>
			retv.d = (dyn*)GC_MALLOC(sizeof(dyn));
			retv.d->v = v.d->v;
			retv.d->d = c1;
		}
	}
	
	return retv;
}			

value app(value f, value v, value w) {									// reduction of f(v)
	value retx;

	fun *g;

	value arg;
	value s;
	// s.s = (crc*)GC_MALLOC(sizeof(crc));

	value (*l)(value, value);
	value (*c)(value, value, value*);
	value (*pl)(value, value, ty**);
	value (*pc)(value, value, value*, ty**);
// 	ran_pol neg_r_p;

    if (f.f->funkind == WRAPPED) {
		s.s = compose(f.f->fundat.wrap.c_res, w.s);
		arg = coerce(v, f.f->fundat.wrap.c_arg);
		g = f.f->fundat.wrap.w;
	} else {
		s.s = w.s;
		arg = v;
		g = f.f;
	}

	switch(g->funkind) {
		case(LABEL):												// if f is "label" function
		l = g->fundat.label;							// R_BETA : return f(v)
		retx = l(arg, s);
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		break;

		case(POLY_LABEL):
		pl = g->fundat.poly_label;
		retx = pl(arg, s, g->tas);
		break;

		case(CLOSURE):												// if f is closure
		c = g->fundat.closure.cls;				// R_BETA : return f(v, fvs)
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		retx = c(arg, s, g->fundat.closure.fvs);
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		break;

		case(POLY_CLOSURE):												// if f is closure
		pc = g->fundat.poly_closure.pcls;				// R_BETA : return f(v, fvs)
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		retx = pc(arg, s, g->fundat.poly_closure.fvs, g->tas);
		//printf("Heap size = %d\n", (int)GC_get_heap_size());
		break;
	}
	return retx;
}

value fun_print_int(value v, value w) {
	value retv;
	printf("%d", v.i_b_u);
	retv.i_b_u = 0;
	return coerce(retv, w.s);
}

value fun_print_bool(value v, value w) {
	value retv;
	int i = v.i_b_u;
	if (i == 1) {
		printf("true");
	} else if (i == 0) {
		printf("false");
	} else {
		printf("error:not boolean value is applied to print_bool");
		exit(1);
	}
	retv.i_b_u = 0;
	return coerce(retv, w.s);
}

value fun_print_newline(value v, value w) {
	value retv;
	int i = v.i_b_u;
	if (i == 0) {
		printf("\n");
	} else {
		printf("error:not unit value is applied to print_newline");
		exit(1);
	}
	retv.i_b_u = 0;
	return coerce(retv, w.s);
}

value print_int;
value print_bool;
value print_newline;

int stdlib() {
	print_int.f = (fun*)GC_MALLOC(sizeof(fun));
	print_int.f->fundat.label = fun_print_int;
	print_int.f->funkind = LABEL;
	print_bool.f = (fun*)GC_MALLOC(sizeof(fun));
	print_bool.f->fundat.label = fun_print_bool;
	print_bool.f->funkind = LABEL;
	print_newline.f = (fun*)GC_MALLOC(sizeof(fun));
	print_newline.f->fundat.label = fun_print_newline;
	print_newline.f->funkind = LABEL;
	return 0;
}

//value print_newline_ = { .f = { .fundat = { .label = fun_print_newline }, .funkind = LABEL } };