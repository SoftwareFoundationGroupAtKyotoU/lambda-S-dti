#ifndef STATIC

#include <gc.h>
#include <stdio.h>
#include <stdlib.h>
#include "ty.h"
#include "blame.h"

ty tydyn = { .tykind = DYN };
ty tyint = { .tykind = BASE_INT };
ty tybool = { .tykind = BASE_BOOL };
ty tyunit = { .tykind = BASE_UNIT };
ty tyfn = { .tykind = TYFUN, .tydat = { .tyfun = { .left = &tydyn, .right = &tydyn } } };
ty tyli = { .tykind = TYLIST, .tydat = { .tylist = &tydyn } };
ty tyrf = { .tykind = TYREF, .tydat = { .tyref = &tydyn } };

inline ty *newty() {
	ty *retty = (ty*)GC_MALLOC(sizeof(ty));
	retty->tykind = TYVAR;
	return retty;
}

inline void dti(const ground_ty g, const uint16_t size, ty *tv) {
	#ifdef PROFILE
	current_inference++;
	#endif
	switch(g) {
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
		case G_FN: {
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
		case G_TP: {
			tv->tykind = TYTUPLE;
			tv->tydat.tytuple.size = size;
			tv->tydat.tytuple.tys = (ty**)GC_MALLOC(sizeof(ty*) * size);
			for (int i = 0; i < size; i++) {
				tv->tydat.tytuple.tys[i] = newty();
			}
			return;
		}
		case G_RF: {
			// printf("DTI : ref was inferred\n");
			// printf("%p <- X ref\n", tv);
			tv->tykind = TYREF;
			tv->tydat.tyref = newty();
			return;
		}
		default: {
			printf("got G_NONE");
			exit(1);
		}
	}
}

#ifndef CAST
inline ty *ty_find(ty *t) {
    ty *root = t;
    while (root->tykind == SUBSTITUTED) {
        #ifdef PROFILE
        find_ty_num++;
        #endif
        root = root->tydat.tv;
    }

    ty *curr = t;
    while (curr->tykind == SUBSTITUTED) {
        ty *next = curr->tydat.tv;
        curr->tydat.tv = root;
        curr = next;
    }

    return root;
}
#endif //CAST

#if defined(CAST) || defined(MONOTONIC)
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
			case TYTUPLE: {
				if (t1->tydat.tytuple.size != t2->tydat.tytuple.size) return 0;
				for (int i = 0; i < t1->tydat.tytuple.size; i++) {
					if (!ty_equal(t1->tydat.tytuple.tys[i], t2->tydat.tytuple.tys[i])) return 0;
				}
				return 1;
			}
			case TYREF: {
				return ty_equal(t1->tydat.tyref, t2->tydat.tyref);
			}
			case TYVAR:
				return t1 == t2;
            default: return 0;
		} 
	} else {
		return 0;
	}
}

ty *get_dyn_tuple_ty(uint16_t size) {
	ty *retty = (ty*)GC_MALLOC(sizeof(ty));
	retty->tykind = TYTUPLE;
	retty->tydat.tytuple.size = size;
	retty->tydat.tytuple.tys = (ty**)GC_MALLOC(sizeof(ty*) * size);
	for (int i = 0; i < size; i++) {
		retty->tydat.tytuple.tys[i] = &tydyn;
	}
	return retty;
}
#endif

#ifdef MONOTONIC
ty *unify_meet(ty* u1, ty* u2) {
    switch (u1->tykind) {
        case DYN: return u2;
        case BASE_INT: {
            switch (u2->tykind) {
                case DYN:
                case BASE_INT:
                    return u1;
                case TYVAR:
                    dti(G_INT, 0, u2);
                    return u1;
                case SUBSTITUTED: return unify_meet(u1, ty_find(u2));
                default: break;
            }
        }
        case BASE_BOOL: {
            switch (u2->tykind) {
                case DYN:
                case BASE_BOOL:
                    return u1;
                case TYVAR:
                    dti(G_BOOL, 0, u2);
                    return u1;
                case SUBSTITUTED: return unify_meet(u1, ty_find(u2));
                default: break;
            }
        }
        case BASE_UNIT: {
            switch (u2->tykind) {
                case DYN:
                case BASE_UNIT:
                    return u1;
                case TYVAR:
                    dti(G_UNIT, 0, u2);
                    return u1;
                case SUBSTITUTED: return unify_meet(u1, ty_find(u2));
                default: break;
            }
        }
        case TYFUN: {
            switch (u2->tykind) {
                case DYN: return u1;
                case TYFUN: {
                    ty *retu = (ty*)GC_MALLOC(sizeof(ty));
                    retu->tykind = TYFUN;
                    retu->tydat.tyfun.left = unify_meet(u1->tydat.tyfun.left, u2->tydat.tyfun.left);
                    retu->tydat.tyfun.right = unify_meet(u1->tydat.tyfun.right, u2->tydat.tyfun.right);
                    return retu;
                }
                case TYVAR:
                    dti(G_FN, 0, u2);
                    return unify_meet(u1, u2);
                case SUBSTITUTED: return unify_meet(u1, ty_find(u2));
                default: break;
            }
        }
        case TYLIST: {
            switch (u2->tykind) {
                case DYN: return u1;
                case TYLIST: {
                    ty *retu = (ty*)GC_MALLOC(sizeof(ty));
                    retu->tykind = TYLIST;
                    retu->tydat.tylist = unify_meet(u1->tydat.tylist, u2->tydat.tylist);
                    return retu;
                }
                case TYVAR:
                    dti(G_LI, 0, u2);
                    return unify_meet(u1, u2);
                case SUBSTITUTED: return unify_meet(u1, ty_find(u2));
                default: break;
            }
        }
        case TYTUPLE: {
            uint16_t size = u1->tydat.tytuple.size;
            switch (u2->tykind) {
                case DYN: return u1;
                case TYTUPLE: {
                    if (size != u2->tydat.tytuple.size) break;
                    ty *retu = (ty*)GC_MALLOC(sizeof(ty));
                    retu->tykind = TYTUPLE;
                    retu->tydat.tytuple.size = size;
                    retu->tydat.tytuple.tys = (ty**)GC_MALLOC(sizeof(ty) * size);
                    for (int i = 0; i < size; i++) {
                        retu->tydat.tytuple.tys[i] = unify_meet(u1->tydat.tytuple.tys[i], u2->tydat.tytuple.tys[i]);
                    }
                    return retu;
                }
                case TYVAR:
                    dti(G_TP, size, u2);
                    return unify_meet(u1, u2);
                case SUBSTITUTED: return unify_meet(u1, ty_find(u2));
                default: break;
            }
        }
        case TYREF: {
            switch (u2->tykind) {
                case DYN: return u1;
                case TYREF: {
                    ty *retu = (ty*)GC_MALLOC(sizeof(ty));
                    retu->tykind = TYREF;
                    retu->tydat.tyref = unify_meet(u1->tydat.tyref, u2->tydat.tyref);
                    return retu;
                }
                case TYVAR:
                    dti(G_RF, 0, u2);
                    return unify_meet(u1, u2);
                case SUBSTITUTED: return unify_meet(u1, ty_find(u2));
                default: break;
            }
        }
        case TYVAR: {
            switch (u2->tykind) {
                case DYN: return u1;
                case BASE_INT: dti(G_INT, 0, u1); return u2;
                case BASE_BOOL: dti(G_BOOL, 0, u1); return u2;
                case BASE_UNIT: dti(G_UNIT, 0, u1); return u2;
                case TYFUN: dti(G_FN, 0, u1); return unify_meet(u1, u2);
                case TYLIST: dti(G_LI, 0, u1); return unify_meet(u1, u2);
                case TYTUPLE: dti(G_TP, u2->tydat.tytuple.size, u1); return unify_meet(u1, u2);
                case TYREF: dti(G_RF, 0, u1); return unify_meet(u1, u2);
                case TYVAR:
                    u1->tykind = SUBSTITUTED;
                    u1->tydat.tv = u2;
                    return u2;
                case SUBSTITUTED: return unify_meet(u1, ty_find(u2));
            }
        }
        case SUBSTITUTED: return unify_meet(ty_find(u1), u2);
        default: printf("cannot_unify; %d ~ %d", u1->tykind, u2->tykind); blame(0, 0); //dummy, yet, TODO
    }
}
#endif

#endif //STATIC