#include "test_common.h"
#include "unity.h"
#include "../libC/ty.h"

// test_main.c にある現在のケース保持用変数
static range local_range_list[] = {
	{ .filename = "p" , .startline = 0, .startchr = 0, .endline = 0, .endchr = 0 },
	{ .filename = "q" , .startline = 1, .startchr = 1, .endline = 1, .endchr = 1 },
	{ .filename = "r" , .startline = 2, .startchr = 2, .endline = 2, .endchr = 2 },
	{ .filename = "s" , .startline = 3, .startchr = 3, .endline = 3, .endchr = 3 },
};
range *range_list;
extern ComposeTestCase* current_case;
extern void test_executor_bridge(); 

void run_manual_test_suite() {
	range_list = local_range_list;

	crc *int_p = new_seq_proj_inj(new_id(), new_id(), new_id());
	int_p->g_inj = G_INT;
	int_p->p_inj = 1;
	int_p->crcdat.seq_tv.rid_inj = 0;
	int_p->g_proj = G_INT;
	int_p->p_proj = 1;
	int_p->crcdat.seq_tv.rid_proj = 0;
	int_p->crcdat.seq_tv.ptr.s = new_id();

	crc *bool_q = new_seq_proj_inj(new_id(), new_id(), new_id());
	bool_q->g_inj = G_BOOL;
	bool_q->p_inj = 1;
	bool_q->crcdat.seq_tv.rid_inj = 1;
	bool_q->g_proj = G_BOOL;
	bool_q->p_proj = 1;
	bool_q->crcdat.seq_tv.rid_proj = 1;
	int_p->crcdat.seq_tv.ptr.s = new_id();

	crc *int_r = new_seq_proj_inj(new_id(), new_id(), new_id());
	int_r->g_inj = G_INT;
	int_r->p_inj = 1;
	int_r->crcdat.seq_tv.rid_inj = 2;
	int_r->g_proj = G_INT;
	int_r->p_proj = 1;
	int_r->crcdat.seq_tv.rid_proj = 2;
	int_p->crcdat.seq_tv.ptr.s = new_id();

	crc *unit_s = new_seq_proj_inj(new_id(), new_id(), new_id());
	unit_s->g_inj = G_UNIT;
	unit_s->p_inj = 1;
	unit_s->crcdat.seq_tv.rid_inj = 3;
	unit_s->g_proj = G_UNIT;
	unit_s->p_proj = 1;
	unit_s->crcdat.seq_tv.rid_proj = 3;
	int_p->crcdat.seq_tv.ptr.s = new_id();

	crc *comp = new_fun(int_p, unit_s);
	
	ty *x1 = newty();

    // ここに人間が期待値を書き込む
    ComposeTestCase cases[] = {
		// second is id
		{   "s ;; id = s", 
			comp, 
			new_id(), 
			comp,
		},
        // id
		{   "id ;; s = s", 
			new_id(), 
			comp, 
			comp,
		},
		// bot
		{   "⊥p ;; s = ⊥p", 
			new_bot(1, 0, 0), 
			comp, 
			new_bot(1, 0, 0), 
		},
		// proj_bot
		{   "int?p;⊥q ;; s = int?p;⊥q", 
			new_seq_proj_bot(int_p, new_bot(1, 1, 0)),
			comp,
			new_seq_proj_bot(int_p, new_bot(1, 1, 0)),
		},
		// proj_occur
		{   "?p⊥Xq ;; s = ?p⊥Xq", 
			new_tv_proj_occur(new_tv_proj(int_p, newty()), 1, 1), 
			comp,
			new_tv_proj_occur(new_tv_proj(int_p, newty()), 1, 1), 
		},
		// proj
		{   "int?p;id ;; id;int! = int?p;id;int!", 
			new_seq_proj(int_p, new_id()), 
			new_seq_inj(new_id(), int_p), 
			new_seq_proj_inj(int_p, new_id(), int_p),
		},
		{   "int?p;id ;; ⊥q     = int?p;⊥q", 
			new_seq_proj(int_p, new_id()), 
			new_bot(1, 1, 0),
			new_seq_proj_bot(int_p, new_bot(1, 1, 0)),
		},
			// TODO ★→★?p;g1 ;; g2 = ...
		// inj
		{   "id;int! ;; int?p;id      = id", 
			new_seq_inj(new_id(), int_p), 
			new_seq_proj(int_p, new_id()), 
			new_id(),
		},
			// TODO int!;;bool?
		{   "id;int! ;; int?p;id;int! = id;int!", 
			new_seq_inj(new_id(), int_p), 
			new_seq_proj_inj(int_p, new_id(), int_p),
			new_seq_inj(new_id(), int_p), 
		},
			// TODO int!;;bool?
		{   "id;int! ;; int?p;⊥q     = ⊥q", 
			new_seq_inj(new_id(), int_p),
			new_seq_proj_bot(int_p, new_bot(1, 1, 0)),
			new_bot(1, 1, 0),
		},
		{   "id;int! ;; bool?q;⊥r    = ⊥q", 
			new_seq_inj(new_id(), int_p),
			new_seq_proj_bot(bool_q, new_bot(1, 2, 0)),
			new_bot(1, 1, 0),
		},
		{   "id;int! ;; X?p           = id", 
			new_seq_inj(new_id(), int_p), 
			new_tv_proj(int_p, newty()), 
			new_id(),
		},
		{   "id;int! ;; ?pX!q         = id;int!", 
			new_seq_inj(new_id(), int_p), 
			new_tv_proj_inj(int_p, newty(), bool_q), 
			new_seq_inj(new_id(), int_p), 
		},
		{   "id;int! ;; ?p⊥Xq        = ⊥q", 
			new_seq_inj(new_id(), int_p), 
			new_tv_proj_occur(new_tv_proj(int_p, newty()), 1, 1), 
			new_bot(1, 1, 1),
		},
		// proj_inj
		{   "int?p;id;int!   ;; int?r;id      = int?p;id", 
			new_seq_proj_inj(int_p, new_id(), int_p),
			new_seq_proj(int_r, new_id()), 
			new_seq_proj(int_p, new_id()), 
		},
			// TODO int!;;bool?
		{   "int?p;id;int!   ;; int?r;id;int! = int?p;id;int!", 
			new_seq_proj_inj(int_p, new_id(), int_p),
			new_seq_proj_inj(int_r, new_id(), int_p),
			new_seq_proj_inj(int_p, new_id(), int_p),
		},
			// TODO int!;;bool?
		{   "int?p;id;int!   ;; int?r;⊥s     = int?p;⊥s", 
			new_seq_proj_inj(int_p, new_id(), int_p),
			new_seq_proj_bot(int_r, new_bot(1, 3, 0)),
			new_seq_proj_bot(int_p, new_bot(1, 3, 0)),
		},
		{   "int?p;id;int!   ;; bool?q;⊥r    = int?p;⊥q", 
			new_seq_proj_inj(int_p, new_id(), int_p),
			new_seq_proj_bot(bool_q, new_bot(1, 2, 0)),
			new_seq_proj_bot(int_p, new_bot(1, 1, 0)),
		},
		{   "bool?q;id;bool! ;; X?p           = bool?p;id", 
			new_seq_proj_inj(bool_q, new_id(), bool_q), 
			new_tv_proj(int_p, newty()), 
			new_seq_proj(bool_q, new_id()),
		},		
		{   "bool?q;id;bool! ;; ?pX!r         = bool?p;id;bool!", 
			new_seq_proj_inj(bool_q, new_id(), bool_q), 
			new_tv_proj_inj(int_p, newty(), int_r), 
			new_seq_proj_inj(bool_q, new_id(), bool_q), 
		},
		{   "bool?q;id;bool! ;; ?p⊥Xr        = bool?q;⊥r", 
			new_seq_proj_inj(bool_q, new_id(), bool_q), 
			new_tv_proj_occur(new_tv_proj(int_p, newty()), 1, 2), 
			new_seq_proj_bot(bool_q, new_bot(1, 2, 1)), 
		},
		// proj for tv
		{   "X?p             ;; X!q             = ?pX!q", 
			new_tv_proj(int_p, x1), 
			new_tv_inj(x1, bool_q), 
			new_tv_proj_inj(int_p, x1, bool_q),
		},
		{   "X?p             ;; ⊥q             = ?p⊥Xq", 
			new_tv_proj(int_p, newty()), 
			new_bot(1, 1, 1), 
			new_tv_proj_occur(int_p, 1, 1),
		},
		// inj for tv
		{   "X!p             ;; int?r;id        = id", 
			new_tv_inj(newty(), int_p), 
			new_seq_proj(int_r, new_id()), 
			new_id(),
		},
		{   "X!p             ;; bool?q;id;bool! = id;bool!", 
			new_tv_inj(newty(), int_p), 
			new_seq_proj_inj(bool_q, new_id(), bool_q), 
			new_seq_inj(new_id(), bool_q),
		},
		{   "X!p             ;; unit?s;⊥q      = ⊥q", 
			new_tv_inj(newty(), int_p), 
			new_seq_proj_bot(unit_s, new_bot(1, 1, 0)), 
			new_bot(1, 1, 0),
		},		
		{   "X!p             ;; Y?q             = id", 
			new_tv_inj(newty(), int_p), 
			new_tv_proj(bool_q, newty()), 
			new_id(),
		},
		{   "X!p             ;; ?qY!r           = Y!r", 
			new_tv_inj(newty(), int_p), 
			new_tv_proj_inj(bool_q, newty(), int_r), 
			new_tv_inj(newty(), int_r),
		},
		{   "X!p             ;; ?q⊥Yr          = ⊥r", 
			new_tv_inj(newty(), int_p), 
			new_tv_proj_occur(new_tv_proj(bool_q, newty()), 1, 2), 
			new_bot(1, 2, 1),
		},		
		// proj_inj for tv
		{   "?pX!q           ;; int?r;id        = int?p;id", 
			new_tv_proj_inj(int_p, newty(), bool_q), 
			new_seq_proj(int_r, new_id()), 
			new_seq_proj(int_p, new_id()), 
		},
		{   "?pX!s           ;; int?r;id;int!   = int?p;id;int!", 
			new_tv_proj_inj(int_p, newty(), bool_q), 
			new_seq_proj_inj(int_r, new_id(), int_r), 
			new_seq_proj_inj(int_p, new_id(), int_p), 
		},
		{   "?pX!q           ;; int?r;⊥s       = int?p;⊥q", 
			new_tv_proj_inj(int_p, newty(), bool_q), 
			new_seq_proj_bot(int_r, new_bot(1, 3, 0)), 
			new_seq_proj_bot(int_p, new_bot(1, 3, 0)), 
		},
		{   "?pX!q           ;; Y?r             = Y?p", 
			new_tv_proj_inj(int_p, newty(), bool_q), 
			new_tv_proj(int_r, newty()), 
			new_tv_proj(int_p, newty()), 
		},
		{   "?pX!q           ;; ?rY!s           = ?pY!s", 
			new_tv_proj_inj(int_p, newty(), bool_q), 
			new_tv_proj_inj(int_r, newty(), unit_s), 
			new_tv_proj_inj(int_p, newty(), unit_s),
		},
		{   "?pX!q           ;; ?r⊥Ys          = ?p⊥Ys", 
			new_tv_proj_inj(int_p, newty(), bool_q), 
			new_tv_proj_occur(new_tv_proj(int_r, newty()), 1, 3), 
			new_tv_proj_occur(new_tv_proj(int_p, newty()), 1, 3), 
		},
		// occur check
		// constructors
		{   "g             ;; ⊥q           = ⊥q", 
			comp, 
			new_bot(1, 1, 0),
			new_bot(1, 1, 0), 
		},
	};

    int num_cases = sizeof(cases) / sizeof(cases[0]);
    for (int i = 0; i < num_cases; i++) {
        current_case = &cases[i];
        RUN_TEST(test_executor_bridge);
    }
}