#ifndef FUN_H
#define FUN_H

#include "types.h"

typedef struct fun {
    // 第一引数に 自分自身のクロージャ cls を受け取る
	// クロージャを生成しないDirの適用であれば、envにはdummyのvalueを入れて対処
    #if defined(CAST) || defined(STATIC)
    value (*funcM)(value, value);
    #elif defined(ALT)
    value (*funcM)(value, value);
    value (*funcD)(value, value, value);
    #else 
    value (*funcD)(value, value, value);
    #endif
	
	// 自由変数や型引数、Wrapであればcoercionや型情報など
    void* env[];
} fun;

/* 
 * メモリレイアウトの例 (すべて void* にキャストして格納)
 * (A) 普通のクロージャ (自由変数がx, yの2つ)
 * [ funcM / funcD ]
 * [ env[0] = (void*)x  ] <-- value x = *(value*)&env[0] として取り出す
 * [ env[1] = (void*)y  ]
 *
 * (B) 多相クロージャ (自由変数がx、型引数がty1)
 * [ funcM / funcD ]
 * [ env[0] = (void*)x   ]
 * [ env[1] = (void*)ty1 ] <-- ty* ty1 = (ty*)env[1] として取り出す
 *
 * (C) WRAPされたクロージャ
 * [ funcM / funcD = fun_wrapped_call_funcM / fun_wrapped_call_funcD ]
 * [ env[0] = (void*)元の関数(fun*)  ]
 * [ env[1] = (void*)コアーション(crc*) ]
 * 
 * (D) WRAPされたクロージャ (CASTオン時)
 * [ funcM = fun_wrapped_call_funcM ]
 * [ env[0] = (void*)元の関数(fun*)  ]
 * [ env[1] = (void*)t1(ty*) ]         <-- ポインタなのでそのまま入る
 * [ env[2] = (void*)t2(ty*) ]         <-- ポインタなのでそのまま入る
 * [ env[3] = (void*)(uintptr_t)rid ]  <-- 整数は uintptr_t を経由してポインタ幅に合わせる
 * [ env[4] = (void*)(uintptr_t)polarity ]
 */

/*
 * wrap関数であるかどうかの判定は
 * 関数ポインタのアドレスがトランポリン関数のアドレスと一致するかで行う。
 */

#endif