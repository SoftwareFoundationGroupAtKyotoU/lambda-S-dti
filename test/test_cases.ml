let tests = [
  (* Constants *)
  ["1", "int", "1", "1"];
  ["true", "bool", "true", "1"];
  ["()", "unit", "()", "()"];
  (* Unary operators *)
  ["-1", "int", "-1", "-1"];
  ["--2", "int", "2", "2"];
  ["let x = 1 in x-1", "int", "0", "0"];
  (* Binary operators *)
  ["1 + 2 + 3", "int", "6", "6"];
  ["3 * 2 + 3", "int", "9", "9"];
  ["3 * (2 + 3)", "int", "15", "15"];
  ["3 = 3", "bool", "true", "1"];
  (* Type ascription *)
  ["(2 : ?)", "?", "2<<id{int};int!>>", "2<<id{int};int!>>"];
  ["((2: ?): int)", "int", "2", "2"];
  (* if-then-else *)
  ["if 2 < 3 then 4 else 5", "int", "4", "4"];
  ["if 3 < 3 then 4 else 5", "int", "5", "5"];
  (* let *)
  ["let x = 3 + 4 in x", "int", "7", "7"];
  ["let x = 3 + 4 in let y = 1 in let x = 2 in y + x", "int", "3", "3"];
  ["let x = 10 in let x = 100 in x * x", "int", "10000", "10000"];
  (* abstraction *)
  ["fun x -> x + 1", "int -> int", "<fun>", "<fun>"];
  ["fun (x:?) -> x + 1", "? -> int", "<fun>", "<fun>"];
  ["fun x -> x", "'a -> 'a", "<fun>", "<fun>"];
  ["fun (x: unit) -> ()", "unit -> unit", "<fun>", "<fun>"];
  ["fun (x: int -> bool) -> ()", "(int -> bool) -> unit", "<fun>", "<fun>"];
  ["fun (x: int -> bool -> int) -> ()", "(int -> bool -> int) -> unit", "<fun>", "<fun>"];
  ["fun (x: (int -> bool) -> int) -> ()", "((int -> bool) -> int) -> unit", "<fun>", "<fun>"];
  ["fun (x:'a) (y:'b) -> x y", "('a -> 'b) -> 'a -> 'b", "<fun>", "<fun>"];
  (* application *)
  ["(fun x -> x + 1) 3", "int", "4", "4"];
  ["(fun (x:?) -> x + 1) 3", "int", "4", "4"];
  (* ["(fun (x:?) -> x + 1) false", "int", "blame+", "blame+"]; *)
  ["(fun x y -> x + y) 3 4", "int", "7", "7"];
  ["(fun (x:?) -> x 2) (fun y -> y)", "?", "2<<id{int};int!>>", "2<<id{int};int!>>"];
  ["(fun (x:?) -> x 2) (fun (y: int) -> y)", "?", "2<<id{int};int!>>", "2<<id{int};int!>>"];
  ["(fun (x:?) -> x 2) (fun y -> true)", "?", "true<<id{bool};bool!>>", "1<<id{bool};bool!>>"];
  (* ["(fun (x:?) -> x) (fun y -> true)", "?", "<fun><<id{? -> ?};(? -> ?)!>>", "<fun><<id{? -> ?};(? -> ?)!>>"]; *)
  ["(fun x -> 1 + ((fun (y:?) -> y) x)) 2", "int", "3", "3"];
  (* sequence *)
  ["(); 1 + 2", "int", "3", "3"];
  ["(():?); 1 + 2", "int", "3", "3"];
  (* dynamic type inference *)
  ["(fun (f:?) -> f 2) (fun y -> y)", "?", "2<<id{int};int!>>", "2<<id{int};int!>>"];
  (* *) ["(fun (f:?) -> f 2) ((fun x -> x) ((fun (y:?) -> y) (fun z -> z + 1)))", "?", "3<<id{int};int!>>", "3<<id{int};int!>>"];
  ["(fun (x:?) -> (fun y -> y) x) (fun (z:?) -> z + 1) 3", "int", "4", "4"];
  ["(fun x -> x) ((fun (y:?) -> y) (fun x -> x + 1)) 1", "int", "2", "2"];
  ["(fun (f:?) -> f (); f true) (fun (x:?) -> x)", "?", "true<<id{bool};bool!>>", "1<<id{bool};bool!>>"];
  (* ["(fun (f:?) -> f (); f true) (fun x -> x)", "?", "blame-", "blame-"]; *)
  ["(fun (f:?) -> let d = f 2 in f true) (fun (x:?) -> x)", "?", "true<<id{bool};bool!>>", "1<<id{bool};bool!>>"];
  (* ["(fun (f:?) -> let d = f 2 in f true) (fun x -> x)", "?", "blame-", "blame-"]; *)
  (* let-poly *)
  ["let s = fun x y z -> x z (y z) in s", "('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c", "<fun>", "<fun>"];
  ["let k = fun x y -> x in k", "'a -> 'b -> 'a", "<fun>", "<fun>"];
  ["let s = fun x y z -> x z (y z) in let k = fun x y -> x in s k k", "'a -> 'a", "<fun>", "<fun>"];
  ["let s = fun x y z -> x z (y z) in let k = fun x y -> x in s k k 1", "int", "1", "1"];
  ["let s = fun (x:?) (y:?) (z:?) -> x z (y z) in let k = fun x y -> x in s k k 1", "?", "1<<id{int};int!>>", "1<<id{int};int!>>"];
  (* ["let succ x = x + 1 in let twice f x = f (f x) in twice succ 1", "int", "3", "3"]; *)
  (* ["let id x = x in let did (x:?) = x in let succ x = x + 1 in (fun (x:?) -> x 1) (id (did succ))", "?", "2: int => ?", "2: int => ?"]; *)
  ["let id x = x in id (); id true", "bool", "true", "1"];
  ["let g = fun x -> ((fun y -> y) : ?->?) x in g (); g 3", "?", "3<<id{int};int!>>", "3<<id{int};int!>>"];
  ["let f = fun x -> 1 + ((fun (y:?) -> y) x) in 2", "int", "2", "2"];
  (* toplevel let-poly *)
  [
    "let g = fun x -> ((fun y -> y) : ?->?) x", "'a -> ?", "<fun>", "<fun>";
    "g (); g true", "?", "true<<id{bool};bool!>>", "1<<id{bool};bool!>>";
  ];
  [
    "let f = (fun x -> x) (fun y -> y)", "'a -> 'a", "<fun>", "<fun>";
    "f", "'a -> 'a", "<fun>", "<fun>";
    "f 3", "int", "3", "3";
    "f", "int -> int", "<fun>", "<fun>";
  ];
  [
    "let twice f x = f (f x)", "('a -> 'a) -> 'a -> 'a", "<fun>", "<fun>";
    (* "twice succ 3", "int", "5", "5";
    "twice not true", "bool", "true", "1"; *)
  ];
  [
    "let dtwice (f:?) (x:?) = f (f x)", "? -> ? -> ?", "<fun>", "<fun>";
    (* "dtwice succ 3", "?", "5: int => ?", "5: int => ?";
    "dtwice not true", "?", "true: bool => ?", "1: bool => ?"; *)
  ];
  [
    "let f x: 'a = x", "'a -> 'a", "<fun>", "<fun>";
    "f 3", "int", "3", "3";
    "f true", "bool", "true", "1";
    "f", "'a -> 'a", "<fun>", "<fun>";
  ];
  [
    "let did (x:?) = x", "? -> ?", "<fun>", "<fun>";
    "let f x: 'a = did x", "'a -> 'b", "<fun>", "<fun>";
    "f 3", "int", "3", "3";
    "f true", "bool", "true", "1";
    "f", "'a -> 'b", "<fun>", "<fun>";
  ];
  [
    "let f: 'a -> 'a = fun x -> x", "'a -> 'a", "<fun>", "<fun>";
    "f 3", "int", "3", "3";
    "f true", "bool", "true", "1";
    "f", "'a -> 'a", "<fun>", "<fun>";
    "let g = f", "'a -> 'a", "<fun>", "<fun>";
    "g 3", "int", "3", "3";
    "g true", "bool", "true", "1";
    "g", "'a -> 'a", "<fun>", "<fun>";
    "let g: 'b = f", "'a -> 'a", "<fun>", "<fun>";
    "g 3", "int", "3", "3";
    "g true", "bool", "true", "1";
    "g", "'a -> 'a", "<fun>", "<fun>";
  ];
  [
    "let f: 'a = fun x -> x", "'a -> 'a", "<fun>", "<fun>";
    "f 3", "int", "3", "3";
    "f true", "bool", "true", "1";
    "f", "'a -> 'a", "<fun>", "<fun>";
    "let g = f", "'a -> 'a", "<fun>", "<fun>";
    "g 3", "int", "3", "3";
    "g true", "bool", "true", "1";
    "g", "'a -> 'a", "<fun>", "<fun>";
  ];
  [
    "let f = ((fun x -> x: 'a -> 'a): 'a -> 'a)", "'a -> 'a", "<fun>", "<fun>";
    "f 3", "int", "3", "3";
    "f true", "bool", "true", "1";
    "f", "'a -> 'a", "<fun>", "<fun>";
    "let g = f", "'a -> 'a", "<fun>", "<fun>";
    "g 3", "int", "3", "3";
    "g true", "bool", "true", "1";
    "g", "'a -> 'a", "<fun>", "<fun>";
  ];
  (* [
    "let f: 'a -> 'a -> ? = fun x y -> 0", "'a -> 'a -> ?", "<fun>", "<fun>";
    "let g1 x = ((fun y -> y) : ? -> ?) x", "'a -> ?", "<fun>", "<fun>";
    "fun x y -> f (g1 x) (g1 y)", "'a -> 'b -> ?", "<fun>", "<fun>";
    "let g2 (x: 'a) = ((fun y -> y) : ? -> ?) x", "'a -> ?", "<fun>", "<fun>";
    "fun x y -> f (g2 x) (g2 y)", "'a -> 'b -> ?", "<fun>", "<fun>";
  ]; *)
  [
    "let f = ((((fun x -> x): 'a ->'a): ?): 'a->'a)", "'a -> 'a", "<fun>", "<fun>";
    "f 3", "int", "3", "3";
    "f", "int -> int", "<fun>", "<fun>";
  ];
  [
    "let f (x: int) (y: bool) = 0", "int -> bool -> int", "<fun>", "<fun>";
    "let dyn x = ((fun (y: 'b) -> y): ? -> ?) x", "'a -> ?", "<fun>", "<fun>";
    "f (dyn 2) (dyn true)", "int", "0", "0";
  ];
  [
    "let f = fun x -> x", "'a -> 'a", "<fun>", "<fun>";
    "let f = fun x -> x f", "(('a -> 'a) -> 'b) -> 'b", "<fun>", "<fun>";
    "f (fun x -> x) 4", "int", "4", "4";
  ];
  (* let-poly & recursion *)
  ["let rec fact n = if n <= 1 then 1 else n * fact (n - 1) in fact 5", "int", "120", "120"];
  ["let rec fact (n:?) = if n <= 1 then 1 else n * fact (n - 1) in fact 5", "int", "120", "120"];
  ["let rec f (x:?) = x in f 2", "int", "2", "2"];
  ["let rec f n x = if n < 0 then x else f (n - 1) x in f 100 true", "bool", "true", "1"];
  ["let rec f (n:?) (x:?) = if n < 0 then x else f (n - 1) x in f 100 true", "bool", "true", "1"];
  ["let rec f n (x:?) = if n <= 0 then x else f 0 x in f 0 true", "bool", "true", "1"];
  ["let rec f n (x:?) = if n <= 0 then x else f 0 x in f 10 true", "bool", "true", "1"];
  ["let rec id x = x in id (); id true", "bool", "true", "1"];
  (* stdlib *)
  (* ["succ 2", "int", "3", "3"];
  ["prec 0", "int", "-1", "-1"]; *)
  (* alpha, beta *)
  ["let x = 2 in let x = 4 in x + x", "int", "8", "8"];
  ["let x = 2 in let y = x in (fun y -> y) y", "int", "2", "2"];
  ["let x = 2 in let a = x in let b = a in let c = x in let d = a in let e = x in e", "int", "2", "2"];
]

(* let g = fun x -> ((fun y -> y):? -> ?) x in if g true then g 2 else g 3  *)

(* let minus_one x = x - 1 in let rec repeat n f x = if n = 0 then x else repeat (n-1) f (f x) in repeat 100000 minus_one 1000000;; *)