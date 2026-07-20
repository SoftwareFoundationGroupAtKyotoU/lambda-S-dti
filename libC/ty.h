#ifndef TY_H
#define TY_H

#ifndef STATIC
#include "types.h"

typedef struct ty {
	enum tykind : uint8_t {
		DYN, //0
		BASE_INT, //1
		BASE_BOOL, //2
		BASE_UNIT, //3
		TYFUN, //4
		TYLIST, //5
		TYTUPLE, //6
		TYREF, //7
		TYVAR, //8
		#ifndef CAST
		SUBSTITUTED, //9
		#endif
	} tykind;
	union tydat {
		ty *tv;
		struct tyfun {
			ty *left;
			ty *right;
		} tyfun;
		ty *tylist;
		struct tytuple {
			uint16_t size;
			ty **tys;
		} tytuple;
		ty *tyref;
	} tydat;
} ty;

extern ty tydyn;
extern ty tyint;
extern ty tybool;
extern ty tyunit;
extern ty tyfn;
extern ty tyli;
extern ty tyrf;

ty *(newty)();

void dti(const ground_ty g, const uint16_t arity, ty *tv);

#ifndef CAST
ty *(ty_find)(ty*);
#endif //CAST

#if defined(CAST) || defined(MONOTONIC)
int ty_equal(ty*, ty*);
ty *get_dyn_tuple_ty(uint16_t);
#endif

#ifdef MONOTONIC
ty *unify_meet(ty*, ty*);
#endif

#endif //STATIC

#endif //TY_H