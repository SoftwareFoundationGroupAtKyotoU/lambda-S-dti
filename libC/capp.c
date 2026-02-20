#ifndef STATIC

#include <stdio.h>
#include <stdlib.h> //for abort
#include <gc.h>

#include "crc.h"
#include "fun.h"
#include "dyn.h"
#include "lst.h"
#include "value.h"

#include "capp.h"

#ifdef PROFILE
static inline void update_longest(int new) {
	if (new > current_longest) {
		current_longest = new;
	}
	return;
}
#endif

static inline uint8_t tag_of(value v) {
	return (v.i_b_u & 0b111);
}

static inline value tag_value(value v, uint8_t t) {
	#ifdef CAST
	switch(t) {
		case G_INT:
		case G_BOOL:
		case G_UNIT:
			return (value){ .d = (v.i_b_u << 3 | t) };
		case G_AR:
		case G_LI:
			return (value){ .d = (v.i_b_u | t) };
		default: {
			printf("%d is not ground_ty", t);
			exit(1);
		}
	}
	#else
	#ifdef PROFILE
	update_longest(1);
	#endif
	return (value){ .d.atom = (v.i_b_u << 3 | t) };
	#endif
}

static inline value untag_value(value v, uint8_t t) {
	#ifdef CAST
	switch(t) {
		case G_INT:
		case G_BOOL:
		case G_UNIT:
			return (value){ .i_b_u = v.d >> 3 };
		case G_AR:
		case G_LI:
			return (value){ .i_b_u = v.d & ~0b111 };
		default: {
			printf("%d is not ground_ty", t);
			exit(1);
		}
	}
	#else
	return (value){ .i_b_u = v.d.atom >> 3 };
	#endif
}

#ifdef CAST
#include "ty.h"

int ty_equal (ty *t1, ty *t2) {
	if (t1 == t2) return 1;
	enum tykind tk1 = t1->tykind;
	enum tykind tk2 = t2->tykind;
	if (t1->tykind == t2->tykind) {
		switch (t1->tykind) {
			case DYN:
			case BASE_INT:
			case BASE_BOOL:
			case BASE_UNIT:
				return 1;
			case TYFUN:
				return ty_equal(t1->tydat.tyfun.left, t2->tydat.tyfun.left) && ty_equal(t1->tydat.tyfun.right, t2->tydat.tyfun.right);
			case TYLIST:
				return ty_equal(t1->tydat.tylist, t2->tydat.tylist);
			case TYVAR:
				return t1 == t2;
		} 
	} else {
		return 0;
	}
}

value cast(value x, ty *t1, ty *t2, uint32_t rid, uint8_t polarity) {			// input = x:t1=>t2
	#ifdef PROFILE
	current_cast++;
	#endif
	// when t1 and t2 are same // R_ID (x:U=>U -> x)
	if (t1 == t2) return x;
	if (ty_equal(t1, t2)) return x;

	enum tykind tk1 = t1->tykind;
	enum tykind tk2 = t2->tykind;
	
	switch(tk1) {
		case BASE_INT: {			// when t1 is ground and t2 is ?
			switch(tk2) {
				case DYN: return tag_value(x, G_INT); // define x:G=>? as dynamic type value
				default: break;
			}
			break;
		}
		case BASE_BOOL: {
			switch(tk2) {
				case DYN: return tag_value(x, G_BOOL); // define x:G=>? as dynamic type value
				default: break;
			}
			break;
		}
		case BASE_UNIT: {
			switch(tk2) {
				case DYN: return tag_value(x, G_UNIT); // define x:G=>? as dynamic type value
				default: break;
			}
			break;
		}
		case TYFUN: {
			switch(tk2) {
				case TYFUN: { 				// when t1 and t2 are function type
					#ifdef PROFILE
					int cur = 1;
					fun *tmp = x.f;
					while(tmp->funkind != WRAPPED) {
						cur++;
						tmp = tmp->fundat.wrap.w;
					}
					update_longest(cur);
					#endif
					value retx;
					// printf("defined as a wrapped function\n");						// define x:U1->U2=>U3->U4 as wrapped function
					retx.f = (fun*)GC_MALLOC(sizeof(fun));
					retx.f->fundat.wrap.w = (fun*)GC_MALLOC(sizeof(fun));
					retx.f->fundat.wrap.w = x.f;
					retx.f->fundat.wrap.u1 = t1;
					retx.f->fundat.wrap.u2 = t2;
					retx.f->rid = rid;
					retx.f->polarity = polarity;
					retx.f->funkind = WRAPPED;
					return retx;
				}
				case DYN: {
					if (t1->tydat.tyfun.left->tykind == DYN && t1->tydat.tyfun.right->tykind == DYN) {
						#ifdef PROFILE
						int cur = 1;
						fun *tmp = x.f;
						while(tmp->funkind != WRAPPED) {
							cur++;
							tmp = tmp->fundat.wrap.w;
						}
						update_longest(cur);
						#endif
						return tag_value(x, G_AR); // define x:G=>? as dynamic type value
					} else {			// when t1 is function type and t2 is ?
						// printf("cast ground\n");
						value x_ = cast(x, t1, &tyar, rid, polarity);									// R_GROUND (x:U=>? -> x:U=>G=>?)
						return cast(x_, &tyar, t2, rid, polarity);
					}
				}
				default: break;
			}
			break;
		}
		case TYLIST: {
			switch(tk2) {
				case TYLIST: {
					#ifdef EAGER
					value retv = { .l = NULL };
    				value *dest = &retv;
    				value curr_src = x;
					ty *tylist1 = t1->tydat.tylist;
					ty *tylist2 = t2->tydat.tylist;
    				while(curr_src.l != NULL) {
    				    lst *new_lst = (lst*)GC_MALLOC(sizeof(lst));        
    				    dest->l = new_lst;
    				    new_lst->h = cast(curr_src.l->h, tylist1, tylist2, rid, polarity);
    				    dest = &new_lst->t;
    				    curr_src = curr_src.l->t;
    				}
    				dest->l = NULL;
    				return retv;
					#else
					#ifdef PROFILE
					int cur = 1;
					lst *tmp = x.l;
					while(tmp->lstkind != WRAPPED_LIST) {
						cur++;
						tmp = tmp->lstdat.wrap_l.w;
					}
					update_longest(cur);
					#endif
					value retx;
					// printf("defined as a wrapped list\n");						// define x:[U1]=>[U2] as wrapped list
					retx.l = (lst*)GC_MALLOC(sizeof(lst));
					retx.l->lstdat.wrap_l.w = (lst*)GC_MALLOC(sizeof(lst));
					retx.l->lstdat.wrap_l.w = x.l;
					retx.l->lstdat.wrap_l.u1 = t1;
					retx.l->lstdat.wrap_l.u2 = t2;
					retx.l->rid = rid;
					retx.l->polarity = polarity;
					retx.l->lstkind = WRAPPED_LIST;
					return retx;
					#endif
				}
				case DYN: {
					if (t1->tydat.tylist->tykind == DYN) {
						#ifdef PROFILE
						int cur = 1;
						#ifdef EAGER
						update_longest(1);
						#else
						lst *tmp = x.l;
						while(tmp->lstkind != WRAPPED_LIST) {
							cur++;
							tmp = tmp->lstdat.wrap_l.w;
						}
						update_longest(cur);
						#endif
						#endif
						return tag_value(x, G_AR); // define x:G=>? as dynamic type value
					} else {			// when t1 is list type and t2 is ?
						// printf("cast ground\n");
						value x_ = cast(x, t1, &tyli, rid, polarity);									// R_GROUND (x:U=>? -> x:U=>G=>?)
						return cast(x_, &tyli, t2, rid, polarity);
					}
				}
				default: break;
			}
			break;
		}
		case DYN: {
			switch(tk2) {
				case BASE_INT: {			// when t1 is ? and t2 is ground type
					if (tag_of(x) == G_INT) {													// when t1's injection ground type equals t2
						// printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
						return untag_value(x, G_INT);
					} else {											// when t1's injection ground type dosen't equal t2
						// printf("cast fail. t:%d, t_:%d\n", t, G_INT);											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
						blame(rid, polarity);
					}
				}
				case BASE_BOOL: {
					if (tag_of(x) == G_BOOL) {													// when t1's injection ground type equals t2
						// printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
						return untag_value(x, G_BOOL);
					} else {											// when t1's injection ground type dosen't equal t2
						// printf("cast fail. t:%d, t_:%d\n", x.d->g, G_BOOL);											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
						blame(rid, polarity);
					}
				}
				case BASE_UNIT: {
					if (tag_of(x) == G_UNIT) {													// when t1's injection ground type equals t2
						// printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
						return untag_value(x, G_UNIT);
					} else {											// when t1's injection ground type dosen't equal t2
						// printf("cast fail. t:%d, t_:%d\n", x.d->g, G_UNIT);											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
						blame(rid, polarity);
					}
				}
				case TYFUN: {
					if (t2->tydat.tyfun.left->tykind == DYN && t2->tydat.tyfun.right->tykind == DYN) {
						if (tag_of(x) == G_AR) {													// when t1's injection ground type equals t2
							// printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
							return untag_value(x, G_AR);
						} else {											// when t1's injection ground type dosen't equal t2
							// printf("cast fail. t:%d, t_:%d\n", x.d->g, G_AR);											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
							blame(rid, polarity);
						}
					} else {			// when t1 is ? and t2 is function type
						// printf("cast expand\n");
						value x_ = cast(x, t1, &tyar, rid, polarity);									// R_EXPAND (x:?=>U -> x:?=>G=>U)
						return cast(x_, &tyar, t2, rid, polarity);
					}
				}
				case TYLIST: {
					if (t2->tydat.tylist->tykind == DYN) {
						if (tag_of(x) == G_LI) {													// when t1's injection ground type equals t2
							// printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
							return untag_value(x, G_LI);
						} else {											// when t1's injection ground type dosen't equal t2
							// printf("cast fail. t:%d, t_:%d\n", x.d->g, G_LI);											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
							blame(rid, polarity);
						}
					} else {			// when t1 is ? and t2 is function type
						// printf("cast expand\n");
						value x_ = cast(x, t1, &tyli, rid, polarity);									// R_EXPAND (x:?=>U -> x:?=>G=>U)
						return cast(x_, &tyli, t2, rid, polarity); 
					}
				}
				case TYVAR: {			// when t1 is ? and t2 is type variable
					switch(tag_of(x)) {
						case(G_INT): {											// when t1's injection ground type is int
							// printf("DTI : int was inferred\n");							// R_INSTBASE (x':int=>?=>X -[X:=int]> x')
							#ifdef PROFILE
							current_inference++;
							#endif
							*t2 = tyint;
							return untag_value(x, G_INT);
						}
						case(G_BOOL): {												// when t1's injection ground type is bool	
							// printf("DTI : bool was inferred\n");							// R_INSTBASE (x':bool=>?=>X -[X:=bool]> x')
							#ifdef PROFILE
							current_inference++;
							#endif
							*t2 = tybool;
							return untag_value(x, G_BOOL);
						}
						case(G_UNIT): {											// when t1's injection ground type is unit
							// printf("DTI : unit was inferred\n");							// R_INSTBASE (x':unit=>?=>X -[X:=unit]> x')
							#ifdef PROFILE
							current_inference++;
							#endif
							*t2 = tyunit;
							return untag_value(x, G_UNIT);
						}
						case(G_AR):	{												// when t1's injection ground type is ?->?
							// printf("DTI : arrow was inferenced\n");							// R_INSTARROW (x':?->?=>?=>X -[X:=X_1->X_2]> x':?->?=>X_1->X_2)
							#ifdef PROFILE
							current_inference++;
							#endif
							t2->tykind = TYFUN;
							t2->tydat.tyfun.left = (ty*)GC_MALLOC(sizeof(ty));
							t2->tydat.tyfun.right = (ty*)GC_MALLOC(sizeof(ty));
							t2->tydat.tyfun.left->tykind = TYVAR;
							t2->tydat.tyfun.right->tykind = TYVAR;
							return cast(untag_value(x, G_AR), &tyar, t2, rid, polarity);
						}
						case(G_LI):	{												// when t1's injection ground type is [?]
							// printf("DTI : list was inferenced\n");							// R_INSTLIST (x':[?]=>?=>X -[X:=X_1->X_2]> x':[?]=>[X_1])
							#ifdef PROFILE
							current_inference++;
							#endif
							t2->tykind = TYLIST;
							t2->tydat.tylist = (ty*)GC_MALLOC(sizeof(ty));
							t2->tydat.tylist->tykind = TYVAR;
							return cast(untag_value(x, G_LI), &tyli, t2, rid, polarity);
						}
					}
				}
				case DYN: {
					printf("Dyn and Dyn should be omitted by id");
					exit(1);
				}
			}
		}
		default: break;
	}
	
	printf("cast cannot be resolved. t1: %d, t2: %d\n", t1->tykind, t2->tykind);
	exit(1);
}
#else
value coerce(value v, crc *s) {
	// printf("coerce c:%d\n", s->crckind);
	#ifdef PROFILE
	current_cast++;
	#endif
	if (s == &crc_id) return v; // v<id> -> v
	if (s == &crc_inj_INT) return tag_value(v, G_INT);
	if (s == &crc_inj_BOOL) return tag_value(v, G_BOOL);
	if (s == &crc_inj_UNIT) return tag_value(v, G_UNIT);
	switch (s->crckind) {
		case ID: goto OPTIMIZATION_UNCAUGHT;
		case BOT: blame(s->crcdat.seq_tv.rid_proj, s->p_proj); // v<bot^p> -> blame p
		case FUN: { // v<s'=>t'>
			if (v.f->funkind == WRAPPED) { // u<<s=>t>><s'=>t'>
				crc *c = compose(v.f->fundat.wrap.c, s);
				if (c->crckind == ID) {    // u<<s=>t>><s'=>t'> -> u<id> -> u
					return (value){ .f = v.f->fundat.wrap.w };
				} else {										 // u<<s=>t>><s'=>t'> -> u<s';;s=>t;;t'> -> u<<s';;s=>t;;t'>>
					value retv;
					retv.f = (fun*)GC_MALLOC(sizeof(fun));
					retv.f->funkind = WRAPPED;
					retv.f->fundat.wrap.w = v.f->fundat.wrap.w;
					retv.f->fundat.wrap.c = c;
					return retv;
				}
			} else {                   // u<s'=>t'> -> u<<s'=>t'>>
				#ifdef PROFILE
				update_longest(1);
				#endif
				value retv;
				retv.f = (fun*)GC_MALLOC(sizeof(fun));
				retv.f->funkind = WRAPPED;
				retv.f->fundat.wrap.w = v.f;
				retv.f->fundat.wrap.c = s;
				return retv;
			}
		}
		case LIST: { // v<[s']>
			#ifdef EAGER
			value retv = { .l = NULL };
    		value *dest = &retv;
    		value curr_src = v;
			crc *clist = s->crcdat.one_crc;
    		while (curr_src.l != NULL) {
    		    lst *new_lst = (lst*)GC_MALLOC(sizeof(lst));        
    		    dest->l = new_lst;
    		    new_lst->h = coerce(curr_src.l->h, clist);
    		    dest = &new_lst->t;
    		    curr_src = curr_src.l->t;
    		}
    		dest->l = NULL;
    		return retv;
			#else
			if (v.l != NULL && v.l->lstkind == WRAPPED_LIST) { // u<<[s]>><[s']>
				crc *c = compose(v.l->lstdat.wrap_l.c, s);
				if (c->crckind == ID) {    						// u<<[s]>><[s']> -> u<id> -> u
					return (value){ .l = v.l->lstdat.wrap_l.w };
				} else {										// u<<[s]>><[s']> -> u<[s;;s']> -> u<<[s;;s']>>
					value retv;
					retv.l = (lst*)GC_MALLOC(sizeof(lst));
					retv.l->lstkind = WRAPPED_LIST;
					retv.l->lstdat.wrap_l.w = v.l->lstdat.wrap_l.w;
					retv.l->lstdat.wrap_l.c = c;
					return retv;
				}
			} else {                   // u<[s']> -> u<<[s']>>
				#ifdef PROFILE
				update_longest(1);
				#endif
				value retv;
				retv.l = (lst*)GC_MALLOC(sizeof(lst));
				retv.l->lstkind = WRAPPED_LIST;
				retv.l->lstdat.wrap_l.w = v.l;
				retv.l->lstdat.wrap_l.c = s;
				return retv;
			}
			#endif
		}
		case TV_INJ: {
			s = normalize_crc(s);
			if (s == &crc_inj_INT) return tag_value(v, G_INT);
			if (s == &crc_inj_BOOL) return tag_value(v, G_BOOL);
			if (s == &crc_inj_UNIT) return tag_value(v, G_UNIT);
			// return coerce(v, s);
		}
		case SEQ_INJ: 
		switch(s->crcdat.seq_tv.ptr.s->crckind) {
			case FUN: { // v<s'=>t';G!>
				value retv;
				retv.d.non_atom = (v_d*)GC_MALLOC(sizeof(v_d));
				if (v.f->funkind == WRAPPED) {                                      // u<<s=>t>><s'=>t';G!>
					crc *c = compose(v.f->fundat.wrap.c, s->crcdat.seq_tv.ptr.s);
					retv.d.non_atom->v.f = v.f->fundat.wrap.w;
					retv.d.non_atom->d = (crc*)GC_MALLOC(sizeof(crc));
					retv.d.non_atom->d->crckind = SEQ_INJ;
					retv.d.non_atom->d->g_inj = s->g_inj;
					retv.d.non_atom->d->crcdat.seq_tv.ptr.s = c;
					return retv;
				} else { // u<s'=>t';G!> -> u<<s'=>t';G!>>
					#ifdef PROFILE
					update_longest(1);
					#endif
					retv.d.non_atom->v.f = v.f;
					retv.d.non_atom->d = s;
					return retv;
				}
			}
			case LIST: { // v<[s'];G!>
				value retv;
				retv.d.non_atom = (v_d*)GC_MALLOC(sizeof(v_d));
				#ifdef EAGER
				#ifdef PROFILE
				update_longest(1);
				#endif
				retv.d.non_atom->v.l = v.l;
				retv.d.non_atom->d = s;
				return retv;
				#else
				if (v.l != NULL && v.l->lstkind == WRAPPED_LIST) {   // u<<[s]>><[s'];G!>
					crc *c = compose(v.l->lstdat.wrap_l.c, s->crcdat.seq_tv.ptr.s);
					retv.d.non_atom->v.l = v.l->lstdat.wrap_l.w;
					retv.d.non_atom->d = (crc*)GC_MALLOC(sizeof(crc));
					retv.d.non_atom->d->crckind = SEQ_INJ;
					retv.d.non_atom->d->g_inj = s->g_inj;
					retv.d.non_atom->d->crcdat.seq_tv.ptr.s = c;
					return retv;
				} else { // u<[s'];G!> -> u<<[s'];G!>>
					#ifdef PROFILE
					update_longest(1);
					#endif
					retv.d.non_atom->v.l = v.l;
					retv.d.non_atom->d = s;
					return retv;
				}
				#endif
			}
			default: {// v<id;G!> -> v<<id;G!>>
				// 関数とリストの id;G! のみがここでdynにされる
				value retv;
				retv.d.non_atom = (v_d*)GC_MALLOC(sizeof(v_d));
				retv.d.non_atom->v = v;
				retv.d.non_atom->d = s;
				return retv;
			}	
		}

		default: {									// v<G?p;i> = u<<d>><G?p;i>, v<X?p> = u<<d>><X?p>, v<?pX!> = u<<d>><?pX!>
			uint8_t tag = tag_of(v);
			switch(tag) {
				case G_INT: {
					s = compose(&crc_inj_INT, s); 
					v = untag_value(v, G_INT); 
					break;
				}
				case G_BOOL: {
					s = compose(&crc_inj_BOOL, s); 
					v = untag_value(v, G_BOOL); 
					break;
				}
				case G_UNIT: {
					s = compose(&crc_inj_UNIT, s); 
					v = untag_value(v, G_UNIT); 
					break;
				}
				default: {
					s = compose(v.d.non_atom->d, s); 
					break;
				}
			}

			// printf("composed c:%d\n", c1->crckind);
			if (s == &crc_id) return v; // u<<d>><s> -> u<id> -> u
			if (s == &crc_inj_INT) return tag_value(v, G_INT);
			if (s == &crc_inj_BOOL) return tag_value(v, G_BOOL);
			if (s == &crc_inj_UNIT) return tag_value(v, G_UNIT);

			switch(s->crckind) {
				case ID: goto OPTIMIZATION_UNCAUGHT;
				case BOT: blame(s->crcdat.seq_tv.rid_proj, s->p_proj);
				case FUN: {        // u<<d>><s> -> u<s=>t> -> u<<s=>t>>
					value retv;
					retv.f = (fun*)GC_MALLOC(sizeof(fun));
					retv.f->funkind = WRAPPED;
					retv.f->fundat.wrap.w = v.d.non_atom->v.f;
					retv.f->fundat.wrap.c = s;
					return retv;
				}
				case LIST: {        // u<<d>><s> -> u<[s]> -> u<<[s]>>
					#ifdef EAGER
					value retv = { .l = NULL };
    				value *dest = &retv;
    				value curr_src = v.d.non_atom->v;
					crc *clist = s->crcdat.one_crc;
    				while (curr_src.l != NULL) {
    				    lst *new_lst = (lst*)GC_MALLOC(sizeof(lst));        
    				    dest->l = new_lst;
    				    new_lst->h = coerce(curr_src.l->h, clist);
    				    dest = &new_lst->t;
    				    curr_src = curr_src.l->t;
    				}
    				dest->l = NULL;
    				return retv;
					#else
					value retv;
					retv.l = (lst*)GC_MALLOC(sizeof(lst));
					retv.l->lstkind = WRAPPED_LIST;
					retv.l->lstdat.wrap_l.w = v.d.non_atom->v.l;
					retv.l->lstdat.wrap_l.c = s;
					return retv;
					#endif
				}

				default: {    // u<<d>><s> -> u<d> -> u<<d>>
					value retv;
					retv.d.non_atom = (v_d*)GC_MALLOC(sizeof(v_d));
					retv.d.non_atom->v = v.d.non_atom->v;
					retv.d.non_atom->d = s;
					return retv;
				}
			}
		}
	}

	OPTIMIZATION_UNCAUGHT: 
	printf("optimization for coercion %d is not caught", s->crckind);
	exit(1);
}		
#endif	

__attribute__((noreturn)) void blame(uint32_t rid, uint8_t polarity) {
	if(polarity == 1) {
		printf("Blame on the expression side:\n");
	} else {
		printf("Blame on the environment side:\n");
	}
	range r = range_list[rid];
	printf("%sline %d, character %d -- line %d, character %d\n", r.filename, r.startline, r.startchr, r.endline, r.endchr);
	exit(0);
}

#endif