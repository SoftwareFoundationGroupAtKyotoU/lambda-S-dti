#include "runtime.h"
#include "stdlib_list.h"

/* ---- local list traversal/construction helpers ---- */

static inline int _list_is_null(value l) {
#if defined(EAGER) || defined(STATIC)
	return (lst*)l == NULL;
#else
	return is_NULL((lst*)l);
#endif
}

static inline value _list_hd(value l) {
#if defined(EAGER) || defined(STATIC)
	return ((lst*)l)->h;
#else
	return hd((lst*)l);
#endif
}

static inline value _list_tl(value l) {
#if defined(EAGER) || defined(STATIC)
	return ((lst*)l)->t;
#else
	return tl((lst*)l);
#endif
}

/* A freshly built cons cell is never wrapped (the wrap bit is only ever set
 * when a coercion is deferred onto an existing cell), so it is always safe
 * to build one by directly setting .h/.t, matching Cls.Cons's own codegen
 * (toC.ml) regardless of EAGER/lazy or CAST/plain mode. */
static inline value _list_cons(value h, value t) {
	lst *cell = (lst*)GC_MALLOC(sizeof(lst));
	cell->h = h;
	cell->t = t;
	return (value)cell;
}

/* ---- core implementations ---- */

static inline value _core_list_length(value cls, value l) {
	(void)cls;
	int64_t n = 0;
	while (!_list_is_null(l)) {
		n++;
		l = _list_tl(l);
	}
	return (value)n;
}
DEF_UNARY(list_length, _core_list_length)

static value _core_list_map_go(value f, value l) {
	if (_list_is_null(l)) return 0;
	value new_h = CALL1(f, _list_hd(l));
	value new_t = _core_list_map_go(f, _list_tl(l));
	return _list_cons(new_h, new_t);
}
static inline value _core_list_map_x(value cls, value l) {
	value f = (value)((fun*)cls)->env[0];
	return _core_list_map_go(f, l);
}
DEF_UNARY(list_map_x, _core_list_map_x)
DEF_BINARY(list_map)

static value _core_list_init_go(value f, value i, value n) {
	if (i >= n) return 0;
	value h = CALL1(f, i);
	value t = _core_list_init_go(f, i + 1, n);
	return _list_cons(h, t);
}
static inline value _core_list_init_x(value cls, value f) {
	value n = (value)((fun*)cls)->env[0];
	return _core_list_init_go(f, 0, n);
}
DEF_UNARY(list_init_x, _core_list_init_x)
DEF_BINARY(list_init)

static value _core_list_mapi_go(value f, value i, value l) {
	if (_list_is_null(l)) return 0;
	value new_h = CALL1(CALL1(f, i), _list_hd(l));
	value new_t = _core_list_mapi_go(f, i + 1, _list_tl(l));
	return _list_cons(new_h, new_t);
}
static inline value _core_list_mapi_x(value cls, value l) {
	value f = (value)((fun*)cls)->env[0];
	return _core_list_mapi_go(f, 0, l);
}
DEF_UNARY(list_mapi_x, _core_list_mapi_x)
DEF_BINARY(list_mapi)

static void _core_list_iteri_go(value f, value i, value l) {
	if (_list_is_null(l)) return;
	CALL1(CALL1(f, i), _list_hd(l));
	_core_list_iteri_go(f, i + 1, _list_tl(l));
}
static inline value _core_list_iteri_x(value cls, value l) {
	value f = (value)((fun*)cls)->env[0];
	_core_list_iteri_go(f, 0, l);
	return 0;
}
DEF_UNARY(list_iteri_x, _core_list_iteri_x)
DEF_BINARY(list_iteri)

static inline value _core_list_fold_left(value f, value acc, value l) {
	while (!_list_is_null(l)) {
		acc = CALL1(CALL1(f, acc), _list_hd(l));
		l = _list_tl(l);
	}
	return acc;
}

/* list_fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a is ternary (one
 * curry stage deeper than DEF_BINARY). Stage 0 (capture f) and stage 2
 * (real computation, given f/acc already captured) are still plain one-arg
 * fun_* stages, so DEF_BINARY(list_fold_left) / DEF_UNARY(list_fold_left_x_x,
 * ...) cover them directly; only the middle stage (capture f *and* acc into
 * one new closure) doesn't fit an existing macro shape and is written by
 * hand below, per mode. */
static inline value _core_list_fold_left_final(value cls, value l) {
	value f = (value)((fun*)cls)->env[0];
	value acc = (value)((fun*)cls)->env[1];
	return _core_list_fold_left(f, acc, l);
}
DEF_UNARY(list_fold_left_x_x, _core_list_fold_left_final)

#ifdef ALT
value fun_alt_list_fold_left_x(value cls, value acc) {
	value f = (value)((fun*)cls)->env[0];
	value retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 2);
	((fun*)retv)->funcM = fun_alt_list_fold_left_x_x;
	((fun*)retv)->funcD = fun_list_fold_left_x_x;
	((fun*)retv)->env[0] = (void*)f;
	((fun*)retv)->env[1] = (void*)acc;
	return retv;
}
value fun_list_fold_left_x(value cls, value acc, value w) {
	return apply_coerce(fun_alt_list_fold_left_x(cls, acc), (crc*)w);
}
#elif defined(CAST) || defined(STATIC)
value fun_list_fold_left_x(value cls, value acc) {
	value f = (value)((fun*)cls)->env[0];
	value retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 2);
	((fun*)retv)->funcM = fun_list_fold_left_x_x;
	((fun*)retv)->env[0] = (void*)f;
	((fun*)retv)->env[1] = (void*)acc;
	return retv;
}
#else
value fun_list_fold_left_x(value cls, value acc, value w) {
	value f = (value)((fun*)cls)->env[0];
	value retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 2);
	((fun*)retv)->funcD = fun_list_fold_left_x_x;
	((fun*)retv)->env[0] = (void*)f;
	((fun*)retv)->env[1] = (void*)acc;
	return apply_coerce(retv, (crc*)w);
}
#endif
DEF_BINARY(list_fold_left)

STDLIB_LIST_UNARY_LIST(STDLIB_TABLE)
STDLIB_LIST_BINARY_LIST(STDLIB_TABLE)
STDLIB_LIST_TRINARY_LIST(STDLIB_TABLE)

STDLIB_LIST_UNARY_LIST(STDLIB_EXPORT)
STDLIB_LIST_BINARY_LIST(STDLIB_EXPORT)
STDLIB_LIST_TRINARY_LIST(STDLIB_EXPORT)
