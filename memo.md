### 関数
- `BLC-`
  - make_crcの負荷が大きそう
  - 例：fib2
  - loopの傾向が田邊さんのやつと違いそう...？
- `SLC-ALC`
  - 逆転しているもの（95%CIがすべて1倍を超えているもの）
    - evenodd: 2
    - fib: 3
    - loop: 10, 16, 17, 18, 20, 22, 24, 25, 26, 27
    - tak: 11, 15
    - ~~GC_MALLOCを二回しているので遅い...？~~
      - していない
    - 1.1倍以内なので誤差の範囲？？
- その他
  - fib1は何が起こってる？
    - SLCはcoerceが635621回呼ばれていて，その分遅くなっていそう
      - 嬉しい
  - evenodd1は計測時間が短くて参考にならなそう
    - fully staticだけ引数の数を増やして計測する？

AC/SC でACが遅くなることがある(map, church)のは謎
BCがかなり遅い


### List
- `SLC-ALC`
  - 逆転しているもの
    - mklist: なし
    - ほか: ようわからんが，ある
- eager vs lazy
  - eagerはS向きではない...？
    - 
  - coerceの回数は，lstの要素数がn個のとき，
    - リストにコアーションが付くと，
      - eager: $n$回
      - lazy: $1$回
    - matchでheadとtailに分解するとき，
      - eager: $0$回
      - lazy: $2$回
  - lazyではeagerで分配されるcomposeを先に行うことができる

- change the tyvar structure (tyvar + blame label) 
  - this change may be applied after LS1
- compiler
  - ldti-compiler does not support some polymorphic function declarations.
    - If you declare `let f x :'a = x` and want to calculate `f (); f 3`, then the compile process fails because of `Type_error: cannot solve a constraint: unit ~.~ int`.
    - This is why `closure_tyvars_let_decl` needs (but ldti implementation has bug with this)