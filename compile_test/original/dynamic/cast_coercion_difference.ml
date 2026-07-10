((((fun (x:bool) :int -> 3) (1:?)):?):bool);;

(* DTI : tyvar was inferred
0x7eff30f5cec0 <- 0x7eff30f5cf40
DTI : arrow was inferred
0x7eff30f5cfe0 <- (0x7eff30f5cea0=>0x7eff30f5ce80)
DTI : tyvar was inferred
0x7eff30f5cf60 <- 0x7eff30f5cea0
tyfind: 0x7eff30f5cec0
tyfind: 0x7eff30f5cf40
DTI : tyvar was inferred
0x7eff30f5ce80 <- 0x7eff30f5cf40
DTI : arrow was inferred
0x7eff30f5cea0 <- (0x7eff30f5ce60=>0x7eff30f5ce40)
DTI : tyvar was inferred
0x7eff30f5cee0 <- 0x7eff30f5ce60
DTI : tyvar was inferred
0x7eff30f5ce40 <- 0x7eff30f5cf00
tyfind: 0x7eff30f5ce80
tyfind: 0x7eff30f5cf40
DTI : tyvar was inferred
0x7eff30f5cf20 <- 0x7eff30f5cf40
tyfind: 0x7eff30f5cf60
tyfind: 0x7eff30f5cea0
DTI : arrow was inferred
0x7eff30f5cf80 <- (0x7eff30f5ce20=>0x7eff30f5ce00)
DTI : tyvar was inferred
0x7eff30f5ce60 <- 0x7eff30f5ce20
tyfind: 0x7eff30f5ce40
tyfind: 0x7eff30f5cf00
DTI : tyvar was inferred
0x7eff30f5ce00 <- 0x7eff30f5cf00
DTI : arrow was inferred
0x7eff30f5cfa0 <- (0x7eff30f5cde0=>0x7eff30f5cdc0)
DTI : tyvar was inferred
0x7eff30f5ce20 <- 0x7eff30f5cde0
tyfind: 0x7eff30f5ce00
tyfind: 0x7eff30f5cf00
DTI : tyvar was inferred
0x7eff30f5cdc0 <- 0x7eff30f5cf00
DTI : tyvar was inferred
0x7eff30f5cde0 <- 0x7eff30f5cfc0
tyfind: 0x7eff30f5cdc0
tyfind: 0x7eff30f5cf00
DTI : tyvar was inferred
0x7eff30f5cfc0 <- 0x7eff30f5cf00
tyfind: 0x7eff30f5cf20
tyfind: 0x7eff30f5cf40
tyfind: 0x7eff30f5cec0
tyfind: 0x7eff30f5cf40
DTI : unit was inferred
0x7eff30f5cf40 <- unit
DTI : int was inferred
0x7eff30f5cf00 <- int
tyfind: 0x7eff30f5cee0
tyfind: 0x7eff30f5ce60
tyfind: 0x7eff30f5ce20
tyfind: 0x7eff30f5cde0
tyfind: 0x7eff30f5cfc0
tyfind: 0x7eff30f5cf00
4 *)