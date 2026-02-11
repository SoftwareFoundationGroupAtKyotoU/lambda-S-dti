#include <stdlib.h>
#include <stdio.h>
#include <gc.h>
#include "unity.h"
#include "test_common.h"
#include "../libC/crc.h"

// --- 作成 ---
crc* new_id() { 
	crc* c = (crc*)GC_MALLOC(sizeof(crc));
	c->crckind = ID;
    return c;
}
crc* new_fun(crc* c1, crc* c2) {
    crc* c = (crc*)GC_MALLOC(sizeof(crc));
	c->crckind = FUN;
    c->crcdat.two_crc.c1 = c1; 
	c->crcdat.two_crc.c2 = c2;
    return c;
}
crc* new_list(crc* child) {
	crc* c = (crc*)GC_MALLOC(sizeof(crc));
	c->crckind = LIST;
    c->crcdat.one_crc = child;
    return c;
}
crc *new_bot(const uint8_t p, const uint32_t rid, const uint8_t is_occur) {
	crc *retc = (crc*)GC_MALLOC(sizeof(crc));
	retc->crckind = BOT;
	retc->botkind = is_occur;
	retc->p_proj = p;
	retc->crcdat.seq_tv.rid_proj = rid;
	return retc;
}
crc* new_seq_proj(const crc *base_proj, crc *s_new) {
    crc *c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = SEQ_PROJ;
    c->g_proj = base_proj->g_proj;
    c->p_proj = base_proj->p_proj;
    c->crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    c->crcdat.seq_tv.ptr.s = s_new;
    return c;
}
crc* new_seq_inj(crc *s_new, const crc *base_inj) {
    crc *c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = SEQ_INJ;
    c->g_inj = base_inj->g_inj;
    c->crcdat.seq_tv.ptr.s = s_new;
    return c;
}
crc* new_seq_proj_inj(const crc *base_proj, crc *s_new, const crc *base_inj) {
    crc *c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = SEQ_PROJ_INJ;
    c->g_proj = base_proj->g_proj;
    c->p_proj = base_proj->p_proj;
    c->g_inj = base_inj->g_inj;
    c->crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    c->crcdat.seq_tv.ptr.s = s_new;
    return c;
}
crc *new_seq_proj_bot(const crc *base_proj, crc *bot) {
	crc *retc = (crc*)GC_MALLOC(sizeof(crc));
	retc->crckind = SEQ_PROJ_BOT;
	retc->g_proj = base_proj->g_proj;
	retc->p_proj = base_proj->p_proj;
	retc->crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
	retc->crcdat.seq_tv.ptr.s = bot;
	return retc;
}
crc* new_tv_proj(const crc *base_proj, ty *tv) {
    crc *c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = TV_PROJ;
    c->p_proj = base_proj->p_proj;
    c->crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    c->crcdat.seq_tv.ptr.tv = tv;
    return c;
}
crc* new_tv_inj(ty *tv, const crc *base_inj) {
    crc *c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = TV_INJ;
	c->p_inj = base_inj->p_inj;
    c->crcdat.seq_tv.rid_inj = base_inj->crcdat.seq_tv.rid_inj;
	c->crcdat.seq_tv.ptr.tv = tv;
    return c;
}
crc* new_tv_proj_inj(const crc *base_proj, ty *tv, const crc *base_inj) {
    crc *c = (crc*)GC_MALLOC(sizeof(crc));
    c->crckind = TV_PROJ_INJ;
    c->p_proj = base_proj->p_proj;
    c->crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
	c->p_inj = base_inj->p_inj;
    c->crcdat.seq_tv.rid_inj = base_inj->crcdat.seq_tv.rid_inj;
    c->crcdat.seq_tv.ptr.tv = tv;
    return c;
}
crc* new_tv_proj_occur(const crc* base_proj, const uint8_t bot_p, const uint32_t bot_rid) {
	crc *c = (crc*)GC_MALLOC(sizeof(crc));
	c->crckind = TV_PROJ_OCCUR;
	c->p_proj = base_proj->p_proj;
	c->p_inj = bot_p;
    c->crcdat.seq_tv.rid_proj = base_proj->crcdat.seq_tv.rid_proj;
    c->crcdat.seq_tv.rid_inj = bot_rid;
	c->crcdat.seq_tv.ptr.tv = base_proj->crcdat.seq_tv.ptr.tv;
	return c;
}

// --- 比較 ---
void assert_crc_recursive(crc* act, crc* exp, const char* path) {
    if (!exp) { TEST_ASSERT_NULL_MESSAGE(act, path); return; }
    TEST_ASSERT_NOT_NULL_MESSAGE(act, path);

	switch(act->crckind) {
		case TV_INJ:
		case TV_PROJ:
		case TV_PROJ_INJ:
		case TV_PROJ_OCCUR:
			normalize_crc(act);
	}

    char msg[256];
    #define CHK_8(field) \
        snprintf(msg, sizeof(msg), "%s | Field: %s", path, #field); \
        TEST_ASSERT_EQUAL_UINT8_MESSAGE(exp->field, act->field, msg);
	#define CHK_32(field) \
        snprintf(msg, sizeof(msg), "%s | Field: %s", path, #field); \
        TEST_ASSERT_EQUAL_UINT32_MESSAGE(exp->crcdat.seq_tv.field, act->crcdat.seq_tv.field, msg);

    CHK_8(crckind); 
	CHK_8(g_proj); 
	CHK_8(g_inj); 
	CHK_8(p_proj); 
	CHK_8(p_inj); 
	CHK_8(botkind);
    #undef CHK

    char next_path[512];
	switch(act->crckind) {
		case ID: return;
		case BOT:
		case TV_PROJ:
		case TV_INJ:
		case TV_PROJ_INJ:
		case TV_PROJ_OCCUR: {
			CHK_32(rid_proj);
			CHK_32(rid_inj);
			return;
		}
		case SEQ_PROJ:
		case SEQ_INJ:
		case SEQ_PROJ_INJ:
		case SEQ_PROJ_BOT: {
			CHK_32(rid_proj);
			CHK_32(rid_inj);
			snprintf(next_path, sizeof(next_path), "%s -> SEQ.s", path);
        	assert_crc_recursive(act->crcdat.seq_tv.ptr.s, exp->crcdat.seq_tv.ptr.s, next_path);
			return;
		}
		case FUN: {
			snprintf(next_path, sizeof(next_path), "%s -> FUN.c1", path);
        	assert_crc_recursive(act->crcdat.two_crc.c1, exp->crcdat.two_crc.c1, next_path);
        	snprintf(next_path, sizeof(next_path), "%s -> FUN.c2", path);
        	assert_crc_recursive(act->crcdat.two_crc.c2, exp->crcdat.two_crc.c2, next_path);
			return;
		}
		case LIST: {
			snprintf(next_path, sizeof(next_path), "%s -> LIST.child", path);
        	assert_crc_recursive(act->crcdat.one_crc, exp->crcdat.one_crc, next_path);
			return;
		}
	}
}