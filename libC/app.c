#ifndef STATIC

#include <stdio.h>
#include <stdlib.h> //for abort
#include <gc.h>

#include "crc.h"
#include "fun.h"
#include "dyn.h"
#include "lst.h"
#include "capp.h"
#include "value.h"
#include "app.h"
#include "ty.h"

#if defined(CAST) || defined(ALT)
value fun_wrapped_call_funcM(value cls, value arg) {
	// closureから関数と、wrapしている情報を取り出す
    fun *inner_f = (fun*)cls.f->env[0];
	#ifdef CAST
	ty *t1 = (ty*)cls.f->env[1];
	ty *t2 = (ty*)cls.f->env[2];
	uint32_t rid = (uint32_t)(uintptr_t)cls.f->env[3];
	uint8_t polarity = (uint8_t)(uintptr_t)cls.f->env[4];
	#else // CAST
    crc *c = (crc*)cls.f->env[1];
	#endif // CAST

	value inner_f_val = (value){ .f = inner_f };

	// Coercion / Cast 適用し、return
	#ifdef CAST
	ty *t11 = t1->tydat.tyfun.left;
	ty *t12 = t1->tydat.tyfun.right;
	ty *t21 = t2->tydat.tyfun.left;
	ty *t22 = t2->tydat.tyfun.right;
	uint8_t neg_polarity = polarity ^ 1;
	value _arg = cast(arg, t21, t11, rid, neg_polarity);
	value ret = inner_f->funcM(inner_f_val, _arg);
	return cast(ret, t12, t22, rid, polarity);
	#else // CAST
    crc *c1 = c->crcdat.two_crc.c1;
    crc *c2 = c->crcdat.two_crc.c2;
    value _arg = coerce(arg, c1);
    value c2_val = (value){ .s = c2 };
    return inner_f->funcD(inner_f_val, _arg, c2_val);
	#endif // CAST
}
#endif // CAST || ALT

#ifndef CAST
value fun_wrapped_call_funcD(value cls, value arg1, value arg2) {
	// closureから関数と、wrapしている情報を取り出す
    fun *inner_f = (fun*)cls.f->env[0];
    crc *c = (crc*)cls.f->env[1];

    value inner_f_val = (value){ .f = inner_f };

	// Coercion 適用し、return
    crc *c1 = c->crcdat.two_crc.c1;
    crc *c2 = c->crcdat.two_crc.c2;
    crc *_arg2_crc = compose(c2, arg2.s);
    value _arg2 = (value){ .s = _arg2_crc };
    value _arg1 = coerce(arg1, c1);
	return inner_f->funcD(inner_f_val, _arg1, _arg2);
}
#endif // not CAST

#endif // not STATIC