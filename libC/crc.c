#ifndef CAST

#include "gc.h"
#include "crc.h"
#include "ty.h"
#include "value.h"
#include <stdio.h>
#include <stdlib.h> 

crc crc_id = { .crckind = ID };
crc inj_INT = { .crckind = INJ, .crcdat = { .g = G_INT } };
crc crc_inj_INT = { .crckind = SEQ, .crcdat = { .two_crc = { .c1 = &crc_id, .c2=&inj_INT } } };
crc inj_BOOL = { .crckind = INJ, .crcdat = { .g = G_BOOL } };
crc crc_inj_BOOL = { .crckind = SEQ, .crcdat = { .two_crc = { .c1 = &crc_id, .c2=&inj_BOOL } } };
crc inj_UNIT = { .crckind = INJ, .crcdat = { .g = G_UNIT } };
crc crc_inj_UNIT = { .crckind = SEQ, .crcdat = { .two_crc = { .c1 = &crc_id, .c2=&inj_UNIT } } };
crc inj_AR = { .crckind = INJ, .crcdat = { .g = G_AR } };
crc inj_LI = { .crckind = INJ, .crcdat = { .g = G_LI } };
value crc_id_value = { .s = &crc_id };

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

crc* normalize_crc(crc *c) {
	switch (c->crckind) {
        case INJ_TV:
        case PROJ_TV:
        case PROJ_INJ_TV:
            c->crcdat.tv = ty_find(c->crcdat.tv);
            break;
        default:
			printf("normalize_crc bad. crckind: %d", c->crckind);
			exit(1);
    }

    ty *tv = c->crcdat.tv;
    enum tykind tk = tv->tykind;

	switch(c->crckind) {
		case INJ_TV: {
			switch(tk) {
				case BASE_INT: return &crc_inj_INT;              // X! [X:=int] -> id;int!
				case BASE_BOOL: return &crc_inj_BOOL;
				case BASE_UNIT: return &crc_inj_UNIT;
				case TYFUN: {         // X! [X:=X1=>X2] -> X1?p=>X2!;(★→★)!
					crc *children = (crc*)GC_MALLOC(sizeof(crc) * 2);
					crc *c1 = &children[0];
					crc *c2 = &children[1];
					c1->crckind = PROJ_TV;
					c1->crcdat.tv = c->crcdat.tv->tydat.tyfun.left;
					// c1->r_p = 
					c2->crckind = INJ_TV;
					c2->crcdat.tv = c->crcdat.tv->tydat.tyfun.right;
					crc *cfun = make_crc_fun(c1, c2);
					return make_crc_inj_ar(cfun);
				}
				case TYLIST: {         // X! [X:=[X1]] -> [X1!];[★]!
					crc *clist_ = (crc*)GC_MALLOC(sizeof(crc));
					clist_->crckind = INJ_TV;
					clist_->crcdat.tv = c->crcdat.tv->tydat.tylist;
					crc *clist = make_crc_list(clist_);
					return make_crc_inj_li(clist);
				}
				default: return c;
			}
		}
		case PROJ_TV: {
			switch(tk) {
				case BASE_INT: return make_crc_proj(G_INT, c->r_p, &crc_id);				// X?p [X:=int] -> int?p;id
				case BASE_BOOL: return make_crc_proj(G_BOOL, c->r_p, &crc_id);
				case BASE_UNIT: return make_crc_proj(G_UNIT, c->r_p, &crc_id);
				case TYFUN: {        // X?p [X:=X1=>X2] -> (★→★)?p;X1!=>X2?p
					crc *children = (crc*)GC_MALLOC(sizeof(crc) * 2);
					crc *c1 = &children[0];
					crc *c2 = &children[1];
					c1->crckind = INJ_TV;
					c1->crcdat.tv = c->crcdat.tv->tydat.tyfun.left;
					c2->crckind = PROJ_TV;
					c2->crcdat.tv = c->crcdat.tv->tydat.tyfun.right;
					c2->r_p = c->r_p;
					crc *cfun = make_crc_fun(c1, c2);
					return make_crc_proj(G_AR, c->r_p, cfun);
				}
				case TYLIST: {        // X?p [X:=[X1]] -> [★]?p;[X1?p]
					crc *clist_ = (crc*)GC_MALLOC(sizeof(crc));
					clist_->crckind = PROJ_TV;
					clist_->r_p = c->r_p;
					clist_->crcdat.tv = c->crcdat.tv->tydat.tylist;
					crc *clist = make_crc_list(clist_);
					return make_crc_proj(G_LI, c->r_p, clist);
				}
				default: return c;
			}
		}
		case PROJ_INJ_TV: {
			switch(tk) {
				case BASE_INT: return make_crc_proj(G_INT, c->r_p, &crc_inj_INT);                    // ?pX! [X:=int] -> int?p;id;int!
				case BASE_BOOL: return make_crc_proj(G_BOOL, c->r_p, &crc_inj_BOOL);
				case BASE_UNIT: return make_crc_proj(G_UNIT, c->r_p, &crc_inj_UNIT);
				case TYFUN: {   				// ?pX! [X:=X1=>X2] -> (★→★)?p(?pX1!=>?pX2!);(★→★)!
					ty *t1 = c->crcdat.tv->tydat.tyfun.left;
					ty *t2 = c->crcdat.tv->tydat.tyfun.right;
					crc *children = (crc*)GC_MALLOC(sizeof(crc) * 2);
					crc *c1 = &children[0];
					crc *c2 = &children[1];
					c1->crckind = PROJ_INJ_TV;
					c1->crcdat.tv = t1;
					// c1->r_p = ;
					c2->crckind = PROJ_INJ_TV;
					c2->crcdat.tv = t2;
					c2->r_p = c->r_p;
					crc *cfun = make_crc_fun(c1, c2);
					crc *car = make_crc_inj_ar(cfun);
					return make_crc_proj(G_AR, c->r_p, car);
				}
				case TYLIST: {				// ?pX! [X:=[X1]] -> [★]?p[?pX1!];[★]!
					ty *t = c->crcdat.tv->tydat.tylist;
					crc *clist_ = (crc*)GC_MALLOC(sizeof(crc));
					clist_->crckind = PROJ_INJ_TV;
					clist_->crcdat.tv = t;
					clist_->r_p = c->r_p;
					crc *clist = make_crc_list(clist_);
					crc *cli = make_crc_inj_li(clist);
					return make_crc_proj(G_LI, c->r_p, cli);
				}
			}
		}
	}
}

crc* compose(crc *c1, crc *c2) {
	// printf("c1: %d, c2: %d\n", c1->crckind, c2->crckind);
	if (c1->crckind == ID) return c2; // id;;s -> s
	if (c2->crckind == ID) return c1; // s;;id -> s
	if (c1->crckind == BOT) return c1; // ⊥;;s -> ⊥
	if (c2->crckind == BOT) return c2; // s;;⊥ -> ⊥

	switch(c1->crckind) {
		case SEQ: { 
			if (c1->crcdat.two_crc.c1->crckind == PROJ) { // G?p;i;;s -> G?p;(i;;s)
				// printf("  c1.c1:%d, c1.c2:%d\n", c1->crcdat.two_crc.c1->crckind, c1->crcdat.two_crc.c2->crckind);
				crc *retc = (crc*)GC_MALLOC(sizeof(crc));
				retc->crckind = SEQ;
				retc->crcdat.two_crc.c1 = c1->crcdat.two_crc.c1;
				retc->crcdat.two_crc.c2 = compose(c1->crcdat.two_crc.c2, c2);
				return retc;
			} else if (c1->crcdat.two_crc.c2->crckind == INJ) {           //g;G!;;s
				// printf("  c1.c1:%d, c1.c2:%d\n", c1->crcdat.two_crc.c1->crckind, c1->crcdat.two_crc.c2->crckind);
				switch(c2->crckind) {
					case SEQ: {
						if (c2->crcdat.two_crc.c1->crckind == PROJ) {              //g;G!;;H?p;i
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
						}
						break;
					}
					case PROJ_TV: {										   	//g;G!;;X?p
						c2 = normalize_crc(c2);
						if (c2->crckind != PROJ_TV) {
							return compose(c1, c2);
						} 
						switch(c1->crcdat.two_crc.c2->crcdat.g) {
							case G_AR: {						//g;(★→★)!;;X?p -> g;;X1!=>X2?p [X:=X1=>X2]
								// printf("DTI : arrow was inferred\n");
								c2->crcdat.tv->tykind = TYFUN;
								c2->crcdat.tv->tydat.tyfun.left = newty();
								c2->crcdat.tv->tydat.tyfun.right = newty();
								// printf("%p <- (%p=>%p)\n", c2->crcdat.tv, c2->crcdat.tv->tydat.tyfun.left, c2->crcdat.tv->tydat.tyfun.right);
								crc *children = (crc*)GC_MALLOC(sizeof(crc) * 2);
								crc *cfun1 = &children[0];
								crc *cfun2 = &children[1];
								cfun1->crckind = INJ_TV;
								cfun1->crcdat.tv = c2->crcdat.tv->tydat.tyfun.left;
								cfun2->crckind = PROJ_TV;
								cfun2->crcdat.tv = c2->crcdat.tv->tydat.tyfun.right;
								crc *cfun = make_crc_fun(cfun1, cfun2);
								return compose(c1->crcdat.two_crc.c1, cfun);
							}
							case G_LI: {						//g;[★]!;;X?p -> g;;[X1?p] [X:=[X1]]
								// printf("DTI : list was inferred\n");
								c2->crcdat.tv->tykind = TYLIST;
								c2->crcdat.tv->tydat.tylist = newty();
								// printf("%p <- [%p]\n", c2->crcdat.tv, c2->crcdat.tv->tydat.tylist);
								crc *clist_ = (crc*)GC_MALLOC(sizeof(crc));
								clist_->crckind = PROJ_TV;
								clist_->crcdat.tv = c2->crcdat.tv->tydat.tylist;
								crc *clist = make_crc_list(clist_);
								return compose(c1->crcdat.two_crc.c1, clist);
							}
							case G_INT: {                      //g;int!;;X?p -> g [X:=int]
								// printf("DTI : int was inferred\n");
								// printf("%p <- int\n", c2->crcdat.tv);
								*c2->crcdat.tv = tyint;
								return c1->crcdat.two_crc.c1;
							}
							case G_BOOL: {
								// printf("DTI : bool was inferred\n");
								// printf("%p <- bool\n", c2->crcdat.tv);
								*c2->crcdat.tv = tybool;
								return c1->crcdat.two_crc.c1;
							}
							case G_UNIT: {
								// printf("DTI : unit was inferred\n");
								// printf("%p <- unit\n", c2->crcdat.tv);
								*c2->crcdat.tv = tyunit;
								return c1->crcdat.two_crc.c1;
							}
						}
					}
					case PROJ_INJ_TV: {									   //g;G!;;?pX!
						c2 = normalize_crc(c2);
						if (c2->crckind != PROJ_INJ_TV) {
							return compose(c1, c2);
						} 
						switch (c1->crcdat.two_crc.c2->crcdat.g) {
							case G_AR: {						//g;(★→★)!;;?pX! -> g;;X1!=>X2?p;(★->★)! [X:=X1=>X2]
								// printf("DTI : arrow was inferred\n");
								c2->crcdat.tv->tykind = TYFUN;
								c2->crcdat.tv->tydat.tyfun.left = newty();
								c2->crcdat.tv->tydat.tyfun.right = newty();
								// printf("%p <- (%p=>%p)\n", c2->crcdat.tv, c2->crcdat.tv->tydat.tyfun.left, c2->crcdat.tv->tydat.tyfun.right);
								crc *children = (crc*)GC_MALLOC(sizeof(crc) * 2);
								crc *cfun1 = &children[0];
								crc *cfun2 = &children[1];
								cfun1->crckind = PROJ_INJ_TV;
								cfun1->crcdat.tv = c2->crcdat.tv->tydat.tyfun.left;
								cfun2->crckind = PROJ_INJ_TV;
								cfun2->crcdat.tv = c2->crcdat.tv->tydat.tyfun.right;
								crc *cfun = make_crc_fun(cfun1, cfun2);
								crc *cfuninj = make_crc_inj_ar(cfun);
								return compose(c1->crcdat.two_crc.c1, cfuninj);
							}
							case G_LI: {						//g;[★]!;;?pX! -> g;;[?pX1!];[★]! [X:=[X1]]
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
							}
							case G_INT: {                      //g;int!;;?pX! -> g;;id;int! -> g;int! [X:=int]
								// printf("DTI : int was inferred\n");
								// printf("%p <- int\n", c2->crcdat.tv);
								*c2->crcdat.tv = tyint;
								return c1;
							}
							case G_BOOL: {
								// printf("DTI : bool was inferred\n");
								// printf("%p <- bool\n", c2->crcdat.tv);
								*c2->crcdat.tv = tybool;
								return c1;
							}
							case G_UNIT: {
								// printf("DTI : unit was inferred\n");
								// printf("%p <- unit\n", c2->crcdat.tv);
								*c2->crcdat.tv = tyunit;
								return c1;
							}
						}
					}
				}
			} 
			break;
		}
		case PROJ_TV: {                                // X?p;;s
			c1 = normalize_crc(c1);
			if (c1->crckind != PROJ_TV) {
				return compose(c1, c2);
			} else if (c2->crckind == INJ_TV) {  // X?p;;X! -> ?pX!
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
			} else {
				printf("cannot compose PROJ_TV;;s");
				exit(1);
			}
		}
		case INJ_TV: {								    // X!;;s
			c1 = normalize_crc(c1);
			if (c1->crckind != INJ_TV) {								    
				return compose(c1, c2);
			} 
			switch (c2->crckind) {      //X!;;G?p;i
				case SEQ: {
					if (c2->crcdat.two_crc.c1->crckind == PROJ) {
						// printf("  c2.c1:%d, c2.c2:%d\n", c2->crcdat.two_crc.c1->crckind, c2->crcdat.two_crc.c2->crckind);
						switch(c2->crcdat.two_crc.c1->crcdat.g) {                            
							case G_AR: {    //X!;;(★→★)?p;i -> X1?p=>X2!;;i [X:=X1=>X2]
								// printf("DTI : arrow was inferred\n");
								c1->crcdat.tv->tykind = TYFUN;
								c1->crcdat.tv->tydat.tyfun.left = newty();
								c1->crcdat.tv->tydat.tyfun.right = newty();
								// printf("%p <- (%p=>%p)\n", c1->crcdat.tv, c1->crcdat.tv->tydat.tyfun.left, c1->crcdat.tv->tydat.tyfun.right);
								crc *children = (crc*)GC_MALLOC(sizeof(crc) * 2);
								crc *cfun1 = &children[0];
								crc *cfun2 = &children[1];
								cfun1->crckind = PROJ_TV;
								cfun1->crcdat.tv = c1->crcdat.tv->tydat.tyfun.left;
								cfun2->crckind = INJ_TV;
								cfun2->crcdat.tv = c1->crcdat.tv->tydat.tyfun.right;
								crc *cfun = make_crc_fun(cfun1, cfun2);
								return compose(cfun, c2->crcdat.two_crc.c2);
							}
							case G_LI: {                       //X!;;[★]?p;i -> [X1!];;i [X:=[X1]]
								// printf("DTI : list was inferred\n");
								c1->crcdat.tv->tykind = TYLIST;
								c1->crcdat.tv->tydat.tylist = newty();
								// printf("%p <- [%p]\n", c1->crcdat.tv, c1->crcdat.tv->tydat.tylist);
								crc *clist_ = (crc*)GC_MALLOC(sizeof(crc));
								clist_->crckind = INJ_TV;
								clist_->crcdat.tv = c1->crcdat.tv->tydat.tylist;
								crc *clist = make_crc_list(clist_);
								return compose(clist, c2->crcdat.two_crc.c2);
							}
							case G_INT: {                   //X!;;int?p;i -> i [X:=int]
								// printf("DTI : int was inferred\n");
								// printf("%p <- int\n", c1->crcdat.tv);
								*c1->crcdat.tv = tyint;
								return c2->crcdat.two_crc.c2;
							}
							case G_BOOL: {
								// printf("DTI : bool was inferred\n");
								// printf("%p <- bool\n", c1->crcdat.tv);
								*c1->crcdat.tv = tybool;
								return c2->crcdat.two_crc.c2;
							}
							case G_UNIT: {
								// printf("DTI : unit was inferred\n");
								// printf("%p <- unit\n", c1->crcdat.tv);
								*c1->crcdat.tv = tyunit;
								return c2->crcdat.two_crc.c2;
							}
						}
					} 
					break;
				}		
				case PROJ_TV: {                                            //X!;;Y?p
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
				}
				case PROJ_INJ_TV: {									    //X!;;?pY!
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
			}
			break;
		}
		case PROJ_INJ_TV: {											//?pX!;;s
			c1 = normalize_crc(c1);
			if (c1->crckind != PROJ_INJ_TV) {
				return compose(c1, c2);
			} 
			switch (c2->crckind) {      
				case SEQ: {
					if (c2->crcdat.two_crc.c1->crckind == PROJ) {   //?pX!;;G?q;i
						// printf("  c2.c1:%d, c2.c2:%d\n", c2->crcdat.two_crc.c1->crckind, c2->crcdat.two_crc.c2->crckind);
						switch (c2->crcdat.two_crc.c1->crcdat.g) {
							case G_AR: {                                //?pX!;;(★→★)?q;i -> (★→★)?p;?qX1!=>?pX2!;;i [X:=X1=>X2]
								// printf("DTI : arrow was inferred\n");
								c1->crcdat.tv->tykind = TYFUN;
								c1->crcdat.tv->tydat.tyfun.left = newty();
								c1->crcdat.tv->tydat.tyfun.right = newty();
								// printf("%p <- (%p=>%p)\n", c1->crcdat.tv, c1->crcdat.tv->tydat.tyfun.left, c1->crcdat.tv->tydat.tyfun.right);
								crc *children = (crc*)GC_MALLOC(sizeof(crc) * 2);
								crc *cfun1 = &children[0];
								crc *cfun2 = &children[1];
								cfun1->crckind = PROJ_INJ_TV;
								cfun1->crcdat.tv = c1->crcdat.tv->tydat.tyfun.left;
								// cfun1->r_p = 
								cfun2->crckind = PROJ_INJ_TV;
								cfun2->crcdat.tv = c1->crcdat.tv->tydat.tyfun.right;
								cfun2->r_p = c1->r_p;
								crc *cfun = make_crc_fun(cfun1, cfun2);
								crc *cprojfun = make_crc_proj(G_AR, c1->r_p, cfun);
								return compose(cprojfun, c2->crcdat.two_crc.c2);
							}
							case G_LI: {                                //?pX!;;[★]?q;i -> [★]?p;[?qX1!];;i [X:=[X1]]
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
							}
							case G_INT: {                     //?pX!;;int?q;i -> int?p;i [X:=int]
								// printf("DTI : int was inferred\n");
								// printf("%p <- int\n", c1->crcdat.tv);
								*c1->crcdat.tv = tyint;
								return make_crc_proj(G_INT, c1->r_p, c2->crcdat.two_crc.c2);
							}
							case G_BOOL: {
								// printf("DTI : bool was inferred\n");
								// printf("%p <- bool\n", c1->crcdat.tv);
								*c1->crcdat.tv = tybool;
								return make_crc_proj(G_BOOL, c1->r_p, c2->crcdat.two_crc.c2);
							}
							case G_UNIT: {
								// printf("DTI : unit was inferred\n");
								// printf("%p <- unit\n", c1->crcdat.tv);
								*c1->crcdat.tv = tyunit;
								return make_crc_proj(G_UNIT, c1->r_p, c2->crcdat.two_crc.c2);
							}
						}	
					} 
					break;
				}
				case PROJ_TV: {                                            //?pX!;;Y?q
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
				}
				case PROJ_INJ_TV: {									    //?pX!;;?qY!
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
			}
			break;
		}
		case FUN: {
			if (c2->crckind == FUN) {                             //s=>t;;s'=>t' -> s';;s=>t;;t'
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
			break;
		}
		case LIST: {
			if (c2->crckind == LIST) {
				crc *retc = (crc*)GC_MALLOC(sizeof(crc));
				retc->crckind = LIST;
				retc->crcdat.one_crc = compose(c1->crcdat.one_crc, c2->crcdat.one_crc);
				if (retc->crcdat.one_crc->crckind == ID) {
					return &crc_id;
				} else {
					return retc;
				}
			} 
			break;
		}
	}

	switch(c2->crckind) {
		case INJ_TV: return compose(c1, normalize_crc(c2));
		case SEQ: {
			if (c2->crcdat.two_crc.c2->crckind == INJ) {          //g;;h;G! -> (g;;h);G!
				// printf("  c2.c1:%d, c2.c2:%d\n", c2->crcdat.two_crc.c1->crckind, c2->crcdat.two_crc.c2->crckind);
				crc *retc = (crc*)GC_MALLOC(sizeof(crc));
				retc->crckind = SEQ;
				retc->crcdat.two_crc.c1 = compose(c1, c2->crcdat.two_crc.c1);
				retc->crcdat.two_crc.c2 = c2->crcdat.two_crc.c2;
				return retc;
			}
			break;
		}
	}

	printf("compose bad. c1: %d, c2: %d\n", c1->crckind, c2->crckind);
	exit(1);
}

#endif