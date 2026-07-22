#ifndef STATIC

#include <stdio.h>
#include <stdlib.h> //for abort
#include <gc.h>

#include "crc.h"
#include "fun.h"
#include "lst.h"
#include "tpl.h"
#include "ref.h"
#include "app.h"
#include "ty.h"
#include "blame.h"

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
	return (v & 0b111);
}

static inline value tag_value(value v, uint8_t t) {
	#ifdef PROFILE
	update_longest(1);
	#endif
	switch(t) {
		case G_INT:
		case G_BOOL:
		case G_UNIT:
			return (value)(v << 3 | t);
		case G_FN:
		case G_LI:
		case G_TP:
		case G_RF:
			return (value)(v | t);
		default: {
			printf("%d is not ground_ty", t);
			exit(1);
		}
	}
}

static inline value untag_value(value v, uint8_t t) {
	switch(t) {
		case G_INT:
		case G_BOOL:
		case G_UNIT:
			return (value)(v >> 3);
		case G_FN:
		case G_LI:
		case G_TP:
		case G_RF:
			return (value)(v & ~0b111);
		default: {
			printf("%d is not ground_ty", t);
			exit(1);
		}
	}
}

static inline uint16_t size_of(value v) {
	switch(tag_of(v)) {
		case G_TP: {
			#ifdef EAGER
			return ((tpl*)untag_value(v, G_TP))->hdr.size;
			#else
			return ((tpl*)untag_value(v, G_TP))->size;
			#endif
		}
		default: return 0;
	}
}

#ifdef CAST
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
					fun *tmp = (fun*)x;
					while(tmp->funcM != fun_wrapped_call_funcM) {
						cur++;
						tmp = (fun*)tmp->env[0];
					}
					update_longest(cur);
					#endif
					value retx;
					// printf("defined as a wrapped function\n");						// define x:U1->U2=>U3->U4 as wrapped function
					retx = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 5);
					((fun*)retx)->funcM = fun_wrapped_call_funcM;
					((fun*)retx)->env[0] = (void*)((fun*)x);
					((fun*)retx)->env[1] = (void*)t1;
					((fun*)retx)->env[2] = (void*)t2;
					((fun*)retx)->env[3] = (void*)(uintptr_t)rid;
					((fun*)retx)->env[4] = (void*)(uintptr_t)polarity;
					return retx;
				}
				case DYN: {
					if (t1->tydat.tyfun.left->tykind == DYN && t1->tydat.tyfun.right->tykind == DYN) {
						#ifdef PROFILE
						int cur = 1;
						fun *tmp = (fun*)x;
						while(tmp->funcM != fun_wrapped_call_funcM) {
							cur++;
							tmp = (fun*)tmp->env[0];
						}
						update_longest(cur);
						#endif
						return tag_value(x, G_FN); // define x:G=>? as dynamic type value
					} else {			// when t1 is function type and t2 is ?
						// printf("cast ground\n");
						value x_ = cast(x, t1, &tyfn, rid, polarity);									// R_GROUND (x:U=>? -> x:U=>G=>?)
						return cast(x_, &tyfn, t2, rid, polarity);
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
					value retv = 0;
    				value *dest = &retv;
    				value curr_src = x;
					ty *tylist1 = t1->tydat.tylist;
					ty *tylist2 = t2->tydat.tylist;
    				while((lst*)curr_src != NULL) {
    				    lst *new_lst = (lst*)GC_MALLOC(sizeof(lst));
    				    *dest = (value)new_lst;
    				    new_lst->h = cast(((lst*)curr_src)->h, tylist1, tylist2, rid, polarity);
    				    dest = &new_lst->t;
    				    curr_src = ((lst*)curr_src)->t;
    				}
    				*dest = (value)NULL;
    				return retv;
					#else
					#ifdef PROFILE
					int cur = 1;
					lst *tmp = (lst*)x;
					while(tmp->t & 0b1 != 1) {
						cur++;
						tmp = tmp->w;
					}
					update_longest(cur);
					#endif
					value retx;
					// printf("defined as a wrapped list\n");						// define x:[U1]=>[U2] as wrapped list
					retx = (value)GC_MALLOC(sizeof(lst));
					((lst*)retx)->w = (lst*)x;
					((lst*)retx)->wrap_info.u1_tag = (uintptr_t)t1 | 0b1;
					((lst*)retx)->wrap_info.u2_p = (uintptr_t)t2 | polarity;
					((lst*)retx)->wrap_info.rid = rid;
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
						lst *tmp = (lst*)x;
						while(tmp->t & 0b1 != 1) {
							cur++;
							tmp = tmp->w;
						}
						update_longest(cur);
						#endif
						#endif
						return tag_value(x, G_LI); // define x:G=>? as dynamic type value
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
		case TYTUPLE: {
			uint16_t size = t1->tydat.tytuple.size;
			switch(tk2) {
				case TYTUPLE: {
					#ifdef EAGER
					value retv = (value)GC_MALLOC(sizeof(tpl) + sizeof(value) * size);
					((tpl*)retv)->hdr.size = size;
					for (int i = 0; i < size; i++) {
						value inner_val = ((tpl*)x)->fields[i];
						((tpl*)retv)->fields[i] = cast(inner_val, t1->tydat.tytuple.tys[i], t2->tydat.tytuple.tys[i], rid, polarity);
					}
					return retv;

					#else // not EAGER
					#ifdef PROFILE
					int cur = 1;
					tpl *tmp = (tpl*)x;
					while(tmp->wrap == 1) {
						cur++;
						tmp = (tpl*)((tpl_wrap*)tmp)->w;
					}
					update_longest(cur);
					#endif
					value retx = (value)GC_MALLOC(sizeof(tpl_wrap));
					((tpl_wrap*)retx)->hdr.size = size;
					((tpl_wrap*)retx)->hdr.wrap = 1;
                    ((tpl_wrap*)retx)->hdr.rid = rid;
                    ((tpl_wrap*)retx)->hdr.polarity = polarity;
					((tpl_wrap*)retx)->w = (tpl*)x;
					((tpl_wrap*)retx)->u1 = t1->tydat.tytuple.tys;
					((tpl_wrap*)retx)->u2 = t2->tydat.tytuple.tys;
					return retx;
					#endif
				}
				case DYN: {
					int all_dyn = 1;
					for(int i = 0; i < size; i++) {
						if (t1->tydat.tytuple.tys[i]->tykind != DYN) { all_dyn = 0; break; }
					}
					if (all_dyn) {
						#ifdef PROFILE
						int cur = 1;
						#ifdef EAGER
						update_longest(1);
						#else
						tpl *tmp = (tpl*)x;
						while(tmp->wrap != 1) {
							cur++;
							tmp = (tpl*)((tpl_wrap*)tmp)->w;
						}
						update_longest(cur);
						#endif
						#endif
						return tag_value(x, G_TP);
					} else {
						ty *dyn_tuple = get_dyn_tuple_ty(size);
						value x_ = cast(x, t1, dyn_tuple, rid, polarity);
						return cast(x_, dyn_tuple, t2, rid, polarity);
					}
				}
				default: break;
			}
			break;
		}
		case TYREF: {
			switch(tk2) {
				case TYREF: { 				// when t1 and t2 are reference type
					#ifdef PROFILE
					int cur = 1;
					ref *tmp = (ref*)x;
					while(tmp->u1_tag & 0b1) {
						cur++;
						tmp = tmp->w;
					}
					update_longest(cur);
					#endif
					value retx;
					// printf("defined as a wrapped function\n");						// define x:U1->U2=>U3->U4 as wrapped function
					retx = (value)GC_MALLOC(sizeof(ref));
					((ref*)retx)->w = (ref*)x;
					((ref*)retx)->u1_tag = (uintptr_t)t1 | 0b1;
					((ref*)retx)->u2_p = (uintptr_t)t2 | polarity;
					((ref*)retx)->rid = rid;
					return retx;
				}
				case DYN: {
					if (t1->tydat.tyref->tykind == DYN) {
						#ifdef PROFILE
						int cur = 1;
						ref *tmp = (ref*)x;
						while(tmp->u1_tag & 0b1) {
							cur++;
							tmp = (ref*)tmp->w;
						}
						update_longest(cur);
						#endif
						return tag_value(x, G_RF); // define x:G=>? as dynamic type value
					} else {			// when t1 is reference type and t2 is ?
						// printf("cast ground\n");
						value x_ = cast(x, t1, &tyrf, rid, polarity);									// R_GROUND (x:U=>? -> x:U=>G=>?)
						return cast(x_, &tyrf, t2, rid, polarity);
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
						if (tag_of(x) == G_FN) {													// when t1's injection ground type equals t2
							// printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
							return untag_value(x, G_FN);
						} else {											// when t1's injection ground type dosen't equal t2
							// printf("cast fail. t:%d, t_:%d\n", x.d->g, G_FN);											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
							blame(rid, polarity);
						}
					} else {			// when t1 is ? and t2 is function type
						// printf("cast expand\n");
						value x_ = cast(x, t1, &tyfn, rid, polarity);									// R_EXPAND (x:?=>U -> x:?=>G=>U)
						return cast(x_, &tyfn, t2, rid, polarity);
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
				case TYTUPLE: {
					int all_dyn = 1;
					uint16_t size = t2->tydat.tytuple.size;
					for(int i = 0; i < size; i++) {
						if (t2->tydat.tytuple.tys[i]->tykind != DYN) { all_dyn = 0; break; }
					}
					if (all_dyn) {
						if (tag_of(x) == G_TP) {
							value t = untag_value(x, G_TP);
							if (size_of(x) == size) {
								return t;
							} else {
								blame(rid, polarity);
							}
						} else {
							blame(rid, polarity);
						}
					} else {
						if (tag_of(x) == G_TP) {
							ty *dyn_tuple = get_dyn_tuple_ty(size_of(x));
							value x_ = cast(x, t1, dyn_tuple, rid, polarity);
							return cast(x_, dyn_tuple, t2, rid, polarity); 
						} else {
							blame(rid, polarity);
						}
					}
				}
				case TYREF: {
					if (t2->tydat.tyref->tykind == DYN) {
						if (tag_of(x) == G_RF) {													// when t1's injection ground type equals t2
							// printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
							return untag_value(x, G_RF);
						} else {											// when t1's injection ground type dosen't equal t2
							// printf("cast fail. t:%d, t_:%d\n", x.d->g, G_LI);											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
							blame(rid, polarity);
						}
					} else {			// when t1 is ? and t2 is function type
						// printf("cast expand\n");
						value x_ = cast(x, t1, &tyrf, rid, polarity);									// R_EXPAND (x:?=>U -> x:?=>G=>U)
						return cast(x_, &tyrf, t2, rid, polarity); 
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
						case(G_FN):	{												// when t1's injection ground type is ?->?
							// printf("DTI : arrow was inferenced\n");							// R_INSTARROW (x':?->?=>?=>X -[X:=X_1->X_2]> x':?->?=>X_1->X_2)
							#ifdef PROFILE
							current_inference++;
							#endif
							t2->tykind = TYFUN;
							t2->tydat.tyfun.left = (ty*)GC_MALLOC(sizeof(ty));
							t2->tydat.tyfun.right = (ty*)GC_MALLOC(sizeof(ty));
							t2->tydat.tyfun.left->tykind = TYVAR;
							t2->tydat.tyfun.right->tykind = TYVAR;
							return cast(untag_value(x, G_FN), &tyfn, t2, rid, polarity);
						}
						case(G_LI):	{												// when t1's injection ground type is [?]
							// printf("DTI : list was inferenced\n");							// R_INSTLIST (x':[?]=>?=>X -[X:=[X_1]]> x':[?]=>[X_1])
							#ifdef PROFILE
							current_inference++;
							#endif
							t2->tykind = TYLIST;
							t2->tydat.tylist = (ty*)GC_MALLOC(sizeof(ty));
							t2->tydat.tylist->tykind = TYVAR;
							return cast(untag_value(x, G_LI), &tyli, t2, rid, polarity);
						}
						case(G_TP):	{												// when t1's injection ground type is (?,...,?)
							// printf("DTI : list was inferenced\n");							// R_INSTTUPLE (x':(?,...,?)=>?=>X -[X:=(X_1,...,Xn)]> x':(?,...,?)=>(X_1,...,Xn))
							#ifdef PROFILE
							current_inference++;
							#endif
							uint16_t size = size_of(x);
							t2->tykind = TYTUPLE;
							t2->tydat.tytuple.size = size;
							t2->tydat.tytuple.tys = (ty**)GC_MALLOC(sizeof(ty*) * size);
							ty *new_tvs = (ty*)GC_MALLOC(sizeof(ty) * size);
							for (int i = 0; i < size; i++) {
								t2->tydat.tytuple.tys[i] = &new_tvs[i];
								t2->tydat.tytuple.tys[i]->tykind = TYVAR;
							}
							return cast(untag_value(x, G_TP), get_dyn_tuple_ty(size), t2, rid, polarity);
						}
						case(G_RF):	{												// when t1's injection ground type is ? ref
							// printf("DTI : list was inferenced\n");							// R_INSTLIST (x':? ref=>?=>X -[X:=X_1 ref]> x':? ref=>X_1 ref)
							#ifdef PROFILE
							current_inference++;
							#endif
							t2->tykind = TYREF;
							t2->tydat.tyref = (ty*)GC_MALLOC(sizeof(ty));
							t2->tydat.tyref->tykind = TYVAR;
							return cast(untag_value(x, G_RF), &tyrf, t2, rid, polarity);
						}
					}
				}
				case DYN: {
					printf("Dyn and Dyn should be omitted by id");
					exit(1);
				}
				default: {
					printf("yet");
					exit(1);
				}
			}
		}
		default: break;
	}
	
	printf("cast cannot be resolved. t1: %d, t2: %d\n", t1->tykind, t2->tykind);
	exit(1);
}
#else // CAST

#ifdef MONOTONIC
SuspendedCasts psi = { NULL, 0, 0 };

void sc_init(uint64_t initial_capacity) {
    psi.data = (RefTyPair*)GC_MALLOC(sizeof(RefTyPair) * initial_capacity);
    psi.count = 0;
    psi.capacity = initial_capacity;
}

void sc_push(ref* r, ty* u) {
    if (psi.count == psi.capacity) {
        psi.capacity *= 2;
        RefTyPair* new_data = (RefTyPair*)GC_REALLOC(psi.data, sizeof(RefTyPair) * psi.capacity);
        psi.data = new_data;
    }
    psi.data[psi.count].r = r;
    psi.data[psi.count].u = u;
    psi.count++;
}

void consume(void) {
	uint64_t cursor = 0;
	while (cursor < psi.count) {
        ref* r = psi.data[cursor].r;
		ty* u = psi.data[cursor].u;
		value v = r->v;
		ty* u_ = r->u;
		ty* u__ = unify_meet(u, u_);
		if (!ty_equal(u_, u__)) {
			crc* s = make_s_coercion(u_, u__);
			value v_ = coerce(v, s);
			r->v = v_;
			r->u = u__;
		}
		psi.data[cursor].r = NULL;
		psi.data[cursor].u = NULL;
        cursor++;
	}
	psi.count = 0;
}
#endif

static inline value remove_inj(const value v, const ground_ty g, const uint16_t size, const crc *s) {
	if (s->has_proj) {
		if (tag_of(v) != g || size_of(v) != size) {
			blame(s->rid_proj, s->p_proj);
		}
		return untag_value(v, g);
	} else {
		return v;
	}
}

static inline value apply_inj(const value v, const ground_ty g, const crc *s) {
	if (s->has_inj) {
		return tag_value(v, g);
	} else {
		return v;
	}
}

value coerce(value v, crc *s) {
	// printf("coerce c:%d\n", s->crckind);
	#ifdef PROFILE
	current_cast++;
	#endif
	if (s == &crc_id) return v; // v<id> -> v
	if (s == &crc_inj_INT) return tag_value(v, G_INT);
	if (s == &crc_inj_BOOL) return tag_value(v, G_BOOL);
	if (s == &crc_inj_UNIT) return tag_value(v, G_UNIT);
	if (s == &crc_inj_FN) return tag_value(v, G_FN);
	if (s == &crc_inj_LI) return tag_value(v, G_LI);
	// tuple is intentionally omitted
	if (s == &crc_inj_RF) return tag_value(v, G_RF);
	switch (s->crckind) {
		case C_ID: { // v<(G?;)id(;G!)>
			value retv = remove_inj(v, s->crcdat.id.g, s->crcdat.id.size, s);
			return apply_inj(retv, s->crcdat.id.g, s);
		}
		case C_FUN: { // v<(G?p;)s'=>t'(;G!)>
			v = remove_inj(v, G_FN, 0, s);
			fun *f;
			crc *c1, *c2;
			if (((fun*)v)->funcD == fun_wrapped_call_funcD) { // u<<s=>t>><s'=>t'>
				f = (fun*)(((fun*)v)->env[0]);
				c1 = compose(s->crcdat.fun_crc.c1, (crc*)((fun*)v)->env[1]);
				c2 = compose((crc*)((fun*)v)->env[2], s->crcdat.fun_crc.c2);
				if (c1 == &crc_id && c2 == &crc_id) {    // u<<s=>t>><s'=>t'> -> u<id> -> u
					return apply_inj((value)f, G_FN, s);
				}
			} else {                   // u<s'=>t'> -> u<<s'=>t'>>
				#ifdef PROFILE
				update_longest(1);
				#endif
				f = (fun*)v;
				c1 = s->crcdat.fun_crc.c1;
				c2 = s->crcdat.fun_crc.c2;
			}
			value retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 3);
			((fun*)retv)->funcD = fun_wrapped_call_funcD;
			#ifdef ALT
			((fun*)retv)->funcM = fun_wrapped_call_funcM;
			#endif // ALT
			((fun*)retv)->env[0] = (void*)f;
			((fun*)retv)->env[1] = (void*)c1;
			((fun*)retv)->env[2] = (void*)c2;
			return apply_inj(retv, G_FN, s);
		}
		case C_LIST: { // v<(G?p;)[s'](;G!)>
			v = remove_inj(v, G_LI, 0, s);
			#ifdef EAGER
			value retv = 0;
			value *dest = &retv;
			value curr_src = v;
			crc *clist = s->crcdat.lst_crc;
			while ((lst*)curr_src != NULL) {
			    lst *new_lst = (lst*)GC_MALLOC(sizeof(lst));
			    *dest = (value)new_lst;
			    new_lst->h = coerce(((lst*)curr_src)->h, clist);
			    dest = &new_lst->t;
			    curr_src = ((lst*)curr_src)->t;
			}
			*dest = 0;
			return apply_inj(retv, G_LI, s);
			#else
			lst *w;
			crc *c;
			if ((lst*)v != NULL && (((lst*)v)->c_tag & 0b1)) { // u<<[s]>><[s']>
				w = ((lst*)v)->w;
				c = compose((crc*)(((lst*)v)->c_tag & ~0b1), s->crcdat.lst_crc);
				if (c == &crc_id) return apply_inj((value)w, G_LI, s); // u<<[s]>><[s']> -> u<id> -> u
			} else {                   // u<[s']> -> u<<[s']>>
				#ifdef PROFILE
				update_longest(1);
				#endif
				w = (lst*)v;
				c = s->crcdat.lst_crc;
			}
			value retv = (value)GC_MALLOC(sizeof(lst));
			((lst*)retv)->w = w;
			((lst*)retv)->c_tag = (uintptr_t)c | 0b1;
			return apply_inj(retv, G_LI, s);
			#endif
		}
		case C_TUPLE: { // v<(G?p;)(s1*...*sn)(;G!)>
			uint16_t size = s->crcdat.tpl_crc.size;
			v = remove_inj(v, G_TP, size, s);
			#ifdef EAGER
			value retv = (value)GC_MALLOC(sizeof(tpl) + sizeof(value) * size);
			((tpl*)retv)->hdr.size = size;
			for (int i = 0; i < size; i++) {
				value inner_val = ((tpl*)v)->fields[i];
				((tpl*)retv)->fields[i] = coerce(inner_val, s->crcdat.tpl_crc.crcs[i]);
			}
			return apply_inj(retv, G_TP, s);
			#else // not EAGER
			tpl_header *w;
			crc **cs;
			if (((tpl_header*)v)->wrap) { // u<<(s1*...*sn)>><(s'1*...*s'n)>
				tpl_wrap *vw = (tpl_wrap*)v;
				w = vw->w;
				cs = (crc**)GC_MALLOC(sizeof(crc*) * size);
				int all_id = 1;
				for (int i = 0; i < size; i++) {
					cs[i] = compose(vw->cs[i], s->crcdat.tpl_crc.crcs[i]);
					if (cs[i] != &crc_id) all_id = 0;
				}
				if (all_id) return apply_inj((value)w, G_TP, s); // u<<(s1*...*sn)>><(s'1*...*s'n)> -> u<id> -> u
			} else { // u<(s'1*...*s'n)> -> u<<(s'1*...*s'n)>>
				#ifdef PROFILE
				update_longest(1);
				#endif
				w = (tpl_header*)v;
				cs = s->crcdat.tpl_crc.crcs;
			}
			value retv = (value)GC_MALLOC(sizeof(tpl_wrap));
			((tpl_wrap*)retv)->hdr.size = size;
			((tpl_wrap*)retv)->hdr.wrap = 1;
			((tpl_wrap*)retv)->w = w;
			((tpl_wrap*)retv)->cs = cs;
			return apply_inj(retv, G_TP, s);
			#endif
		}
		case C_REF: { // v<(G?p;)ref(s')(;G!)>
			v = remove_inj(v, G_RF, 0, s);
			#ifdef MONOTONIC
			sc_push((ref*)v, s->crcdat.mref_crc);
			return apply_inj(v, G_RF, s);
			#else
			ref *w;
			crc *c1, *c2;
			if (((ref*)v)->c1_tag & 0b1) { // u<<ref(s)>><ref(s')>
				w = ((ref*)v)->w;
				c1 = compose((crc*)(((ref*)v)->c1_tag & ~0b1), s->crcdat.ref_crc.c1); // read: old then new
				c2 = compose(s->crcdat.ref_crc.c2, (crc*)((ref*)v)->c2);              // write: new then old
				if (c1 == &crc_id && c2 == &crc_id) return apply_inj((value)w, G_RF, s); // u<<ref(s)>><ref(s')> -> u<id> -> u
			} else {                   // u<ref(s')> -> u<<ref(s')>>
				#ifdef PROFILE
				update_longest(1);
				#endif
				w = (ref*)v;
				c1 = s->crcdat.ref_crc.c1;
				c2 = s->crcdat.ref_crc.c2;
			}
			value retv = (value)GC_MALLOC(sizeof(ref));
			((ref*)retv)->w = w;
			((ref*)retv)->c1_tag = (uintptr_t)c1 | 0b1;
			((ref*)retv)->c2 = (uintptr_t)c2;
			return apply_inj(retv, G_RF, s);
			#endif
		}
		case C_TV: { // v<?pX!q>, v<X?p>, v<X!q>
			ty *tv = s->crcdat.tv.tv_ptr;
			switch (tv->tykind) {
				case TYVAR: { // s should not be X!q
					dti(tag_of(v), size_of(v), tv);
					break;
				}
				case SUBSTITUTED: {
					s->crcdat.tv.tv_ptr = ty_find(tv);
					break;
				}
				default: break;
			}
			return coerce(v, normalize_tv(s));
		}
		case C_BOT: { // v<(G?p;)⊥q>
			remove_inj(v, s->crcdat.bot.g, s->crcdat.bot.size, s);
			blame(s->crcdat.bot.rid_bot, s->crcdat.bot.p_bot); // v<bot^p> -> blame p
		}
	}
}		
#endif	

#endif