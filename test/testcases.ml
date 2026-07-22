open Lambda_S_dti.Config

module Static = struct
  let constants = [
    ["1", "int", "1"];
    ["true", "bool", "true"];
    ["()", "unit", "()"];
  ]

  let unary_ops = [
    ["-1", "int", "-1"];
    ["--2", "int", "2"];
    ["let x = 1 in x-1", "int", "0"];
  ]

  let binary_ops = [
    ["1 + 2 + 3", "int", "6"];
    ["3 * 2 + 3", "int", "9"];
    ["3 * (2 + 3)", "int", "15"];
    ["3 = 3", "bool", "true"];
    ["10 / 2", "int", "5"];
    ["10 mod 3", "int", "1"];
    ["2 <> 3", "bool", "true"];
    ["3 <= 3", "bool", "true"];
    ["4 >= 5", "bool", "false"];
    ["true && false", "bool", "false"];
    ["false || true", "bool", "true"];
    ["(1 < 2) && (3 > 4)", "bool", "false"];
  ]

  let if_then_else = [
    ["if 2 < 3 then 4 else 5", "int", "4"];
    ["if 3 < 3 then 4 else 5", "int", "5"];
    ["if true then 1, 2 else 3, 4", "int * int", "(1, 2)"];
  ]

  let let_definition = [
    ["let x = 3 + 4 in x", "int", "7"];
    ["let x = 3 + 4 in let y = 1 in let x = 2 in y + x", "int", "3"];
    ["let x = 10 in let x = 100 in x * x", "int", "10000"];
  ]

  let abstraction = [
    ["fun x -> x + 1", "int -> int", "<fun>"];
    ["fun x -> x", "'a -> 'a", "<fun>"];
    ["fun (x: unit) -> ()", "unit -> unit", "<fun>"];
    ["fun (x: int -> bool) -> ()", "(int -> bool) -> unit", "<fun>"];
    ["fun (x: int -> bool -> int) -> ()", "(int -> bool -> int) -> unit", "<fun>"];
    ["fun (x: (int -> bool) -> int) -> ()", "((int -> bool) -> int) -> unit", "<fun>"];
    ["fun (x:'a) (y:'b) -> x y", "('a -> 'b) -> 'a -> 'b", "<fun>"];
    ["fun (x: int * bool -> int) -> 0", "(int * bool -> int) -> int", "<fun>"];
  ]

  let application = [
    ["(fun x -> x + 1) 3", "int", "4"];
    ["(fun x y -> x + y) 3 4", "int", "7"];
    ["let add x y z = x + y + z in add 1 2 3", "int", "6"];
    ["let add x y = x + y in let add5 = add 5 in add5 10", "int", "15"];
    ["(fun x -> fun y -> x + y) 1 2", "int", "3"];
    ["let compose f g x = f (g x) in compose (fun x -> x + 1) (fun x -> x * 2) 3", "int", "7"];
  ]

  let sequence = [
    ["(); 1 + 2", "int", "3"];
  ]

  let let_poly = [
    ["let s = fun x y z -> x z (y z) in s", "('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c", "<fun>"];
    ["let k = fun x y -> x in k", "'a -> 'b -> 'a", "<fun>"];
    ["let s = fun x y z -> x z (y z) in let k = fun x y -> x in s k k", "'a -> 'a", "<fun>"];
    ["let s = fun x y z -> x z (y z) in let k = fun x y -> x in s k k 1", "int", "1"];
    ["let succ x = x + 1 in let twice f x = f (f x) in twice succ 1", "int", "3"];
    ["let id x = x in id (); id true", "bool", "true"];
  ]

  let let_poly_toplevel = [
    [
      "let f = (fun x -> x) (fun y -> y)", "'a -> 'a", "<fun>";
      "f", "'a -> 'a", "<fun>";
      "f 3", "int", "3";
      "f", "int -> int", "<fun>";
    ];
    [
      "let twice f x = f (f x)", "('a -> 'a) -> 'a -> 'a", "<fun>";
      "twice succ 3", "int", "5";
      "twice not true", "bool", "true";
    ];
    [
      "let f x: 'a = x", "'a -> 'a", "<fun>";
      "f 3", "int", "3";
      "f true", "bool", "true";
      "f", "'a -> 'a", "<fun>";
    ];
    [
      "let f: 'a -> 'a = fun x -> x", "'a -> 'a", "<fun>";
      "f 3", "int", "3";
      "f true", "bool", "true";
      "f", "'a -> 'a", "<fun>";
      "let g = f", "'a -> 'a", "<fun>";
      "g 3", "int", "3";
      "g true", "bool", "true";
      "g", "'a -> 'a", "<fun>";
      "let g: 'b = f", "'a -> 'a", "<fun>";
      "g 3", "int", "3";
      "g true", "bool", "true";
      "g", "'a -> 'a", "<fun>";
    ];
    [
      "let f: 'a = fun x -> x", "'a -> 'a", "<fun>";
      "f 3", "int", "3";
      "f true", "bool", "true";
      "f", "'a -> 'a", "<fun>";
      "let g = f", "'a -> 'a", "<fun>";
      "g 3", "int", "3";
      "g true", "bool", "true";
      "g", "'a -> 'a", "<fun>";
    ];
    [
      "let f = ((fun x -> x: 'a -> 'a): 'a -> 'a)", "'a -> 'a", "<fun>";
      "f 3", "int", "3";
      "f true", "bool", "true";
      "f", "'a -> 'a", "<fun>";
      "let g = f", "'a -> 'a", "<fun>";
      "g 3", "int", "3";
      "g true", "bool", "true";
      "g", "'a -> 'a", "<fun>";
    ];
    [
      "let f = fun x -> x", "'a -> 'a", "<fun>";
      "let f = fun x -> x f", "(('a -> 'a) -> 'b) -> 'b", "<fun>";
      "f (fun x -> x) 4", "int", "4";
    ];
  ]

  let let_poly_recursion = [
    ["let rec fact n = if n <= 1 then 1 else n * fact (n - 1) in fact 5", "int", "120"];
    ["let rec f n x = if n < 0 then x else f (n - 1) x in f 100 true", "bool", "true"];
    ["let rec id x = x in id (); id true", "bool", "true"];
  ]

  let lists = [
    ["[]", "'a list", "[]"];
    ["[[]]", "'a list list", "[] :: []"];
    ["1 :: 2 :: []", "int list", "1 :: 2 :: []"];
    ["[1; 2; 3]", "int list", "1 :: 2 :: 3 :: []"];
    ["let x = [true; false] in x", "bool list", "true :: false :: []"];
    ["let x = [] in let y = 3 :: x in let z = true :: x in y", "int list", "3 :: []"];
  ]

  let matches = [
    ["match 1 with | 1 -> 10 | _ -> 20", "int", "10"];
    ["match true with true -> 1 | false -> 0", "int", "1"];
    ["let f x = match x with | [] -> 0 | h :: t -> h in f [3; 4]", "int", "3"];
    ["let rec sum l = match l with [] -> 0 | h :: t -> h + sum t in sum [1; 2; 3; 4]", "int", "10"];
    ["match 1, true with (x, y) -> x", "int", "1"];
    ["match 1, (2, 3) with (x, (y, z)) -> y", "int", "2"];
    ["let f l = match l with h :: h2 :: t -> h + h2 | _ -> 0 in f [1; 2; 3]", "int", "3"];
    ["match ([] : int list) with [] -> 0 | h :: t -> h", "int", "0"];
    ["match (1, 2, 3) with (x, y, z) -> x + y + z", "int", "6"];
    ["match 1 with _ -> 99", "int", "99"];
  ]

  let tuples = [
    ["1, true", "int * bool", "(1, true)"];
    ["1 + 2, 3 * 4", "int * int", "(3, 12)"];
    ["1, 2, 3", "int * int * int", "(1, 2, 3)"];
    ["(1, true), 2", "(int * bool) * int", "((1, true), 2)"];
    ["let f x y = x, y in f 1 true", "int * bool", "(1, true)"];
  ]

  let refs = [
    ["ref 1", "int ref", "{ contents = 1, int }"];
    ["!(ref 1)", "int", "1"];
    ["!(ref true)", "bool", "true"];
    ["let x = ref 1 in x := 2", "unit", "()"];
    ["let x = ref 1 in x := 2; !x", "int", "2"];
    ["let x = ref 0 in let y = x in y := 5; !x", "int", "5"];
    ["let x = ref 1 in x := !x + 1; !x", "int", "2"];
    ["fun x -> x := !x + 1", "int ref -> unit", "<fun>"];
  ]
  
  let stdlibs = [
    ["succ 2", "int", "3"];
    ["prec 0", "int", "-1"];
    ["not true", "bool", "false"];
    ["not false", "bool", "true"];
    ["min 3 5", "int", "3"];
    ["max 3 5", "int", "5"];
    ["abs (-5)", "int", "5"];
    ["ignore 5", "unit", "()"];
    ["ignore true", "unit", "()"];
    ["succ (succ 1)", "int", "3"];
    ["prec (prec 10)", "int", "8"];
  ]
end

module Gradual = struct
  let ext ~config ts = List.map (fun t -> List.map (fun (p, u, v_B, v_S) -> if config.intoB then p, u, v_B else p, u, v_S) t) ts

  let binary_ops ~config = ext ~config [
    ["false && (((true:?):int):?)", "bool", "false", "false"];
  ]

  let type_ascription ~config = ext ~config [
    ["(2 : ?)", "?", "2: int => ?", "2<<id{int};int!>>"];
    ["((2: ?): int)", "int", "2", "2"];
  ]

  let abstraction ~config = ext ~config [
    ["fun (x:?) -> x + 1", "? -> int", "<fun>", "<fun>"];
  ]

  let application ~config = ext ~config [
    ["(fun (x:?) -> x + 1) 3", "int", "4", "4"];
    ["(fun (x:?) -> x + 1) false", "int", "blame+", "blame+"];
    ["(fun (x:?) -> x 2) (fun y -> y)", "?", "2: int => ?", "2<<id{int};int!>>"];
    ["(fun (x:?) -> x 2) (fun (y: int) -> y)", "?", "2: int => ?", "2<<id{int};int!>>"];
    ["(fun (x:?) -> x 2) (fun y -> true)", "?", "true: bool => ?", "true<<id{bool};bool!>>"];
    ["(fun (x:?) -> x) (fun y -> true)", "?", "<fun>: 'a -> bool => ? -> ? => ?", "<fun><<'a?p->(id{bool};bool!);(? -> ?)!>>"];
    ["(fun x -> 1 + ((fun (y:?) -> y) x)) 2", "int", "3", "3"];
  ]

  let sequence ~config = ext ~config [
    ["(():?); 1 + 2", "int", "3", "3"];
  ]

  let dti ~config = ext ~config [
    ["(fun (f:?) -> f 2) (fun y -> y)", "?", "2: int => ?", "2<<id{int};int!>>"];
    ["(fun (f:?) -> f 2) ((fun x -> x) ((fun (y:?) -> y) (fun z -> z + 1)))", "?", "3: int => ?", "3<<id{int};int!>>"];
    ["(fun (x:?) -> (fun y -> y) x) (fun (z:?) -> z + 1) 3", "int", "4", "4"];
    ["(fun x -> x) ((fun (y:?) -> y) (fun x -> x + 1)) 1", "int", "2", "2"];
    ["(fun (f:?) -> f (); f true) (fun (x:?) -> x)", "?", "true: bool => ?", "true<<id{bool};bool!>>"];
    ["(fun (f:?) -> f (); f true) (fun x -> x)", "?", "blame-", "blame-"];
    ["(fun (f:?) -> let d = f 2 in f true) (fun (x:?) -> x)", "?", "true: bool => ?", "true<<id{bool};bool!>>"];
    ["(fun (f:?) -> let d = f 2 in f true) (fun x -> x)", "?", "blame-", "blame-"];
  ]

  let let_poly ~config = ext ~config [
    ["let s = fun (x:?) (y:?) (z:?) -> x z (y z) in let k = fun x y -> x in s k k 1", "?", "1: int => ?", "1<<id{int};int!>>"];
    ["let id x = x in let did (x:?) = x in let succ x = x + 1 in (fun (x:?) -> x 1) (id (did succ))", "?", "2: int => ?", "2<<id{int};int!>>"];
    ["let g = fun x -> ((fun y -> y) : ?->?) x in g (); g 3", "?", "3: int => ?", "3<<id{int};int!>>"];
    ["let f = fun x -> 1 + ((fun (y:?) -> y) x) in 2", "int", "2", "2"];
  ]

  let let_poly_toplevel ~config = ext ~config [
    [
      "let g = fun x -> ((fun y -> y) : ?->?) x", "'a -> ?", "<fun>", "<fun>";
      "g (); g true", "?", "true: bool => ?", "true<<id{bool};bool!>>";
    ];
    [
      "let dtwice (f:?) (x:?) = f (f x)", "? -> ? -> ?", "<fun>", "<fun>";
      "dtwice succ 3", "?", "5: int => ?",  "5<<id{int};int!>>";
      "dtwice not true", "?", "true: bool => ?", "true<<id{bool};bool!>>";
    ];
    [
      "let did (x:?) = x", "? -> ?", "<fun>", "<fun>";
      "let f x: 'a = did x", "'a -> 'b", "<fun>", "<fun>";
      "f 3", "int", "3", "3";
      "f true", "bool", "true", "true";
      "f", "'a -> 'b", "<fun>", "<fun>";
    ];
    [
      "let f: 'a -> 'a -> ? = fun x y -> 0", "'a -> 'a -> ?", "<fun>", "<fun>";
      "let g1 x = ((fun y -> y) : ? -> ?) x", "'a -> ?", "<fun>", "<fun>";
      "fun x y -> f (g1 x) (g1 y)", "'a -> 'b -> ?", "<fun>", "<fun>";
      "let g2 (x: 'a) = ((fun y -> y) : ? -> ?) x", "'a -> ?", "<fun>", "<fun>";
      "fun x y -> f (g2 x) (g2 y)", "'a -> 'b -> ?", "<fun>", "<fun>";
    ];
    [
      "let f = ((((fun x -> x): 'a ->'a): ?): 'a->'a)", "'a -> 'a", "<fun>: 'a -> 'a => ? -> ? => 'a -> 'a", "<fun>";
      "f 3", "int", "3", "3";
      "f", "int -> int", "<fun>: int -> int => ? -> ? => int -> int", "<fun>";
    ];
    [
      "let f (x: int) (y: bool) = 0", "int -> bool -> int", "<fun>", "<fun>";
      "let dyn x = ((fun (y: 'b) -> y): ? -> ?) x", "'a -> ?", "<fun>", "<fun>";
      "f (dyn 2) (dyn true)", "int", "0", "0";
    ];
  ]

  let let_poly_recursion ~config = ext ~config [
    ["let rec fact (n:?) = if n <= 1 then 1 else n * fact (n - 1) in fact 5", "int", "120", "120"];
    ["let rec f (x:?) = x in f 2", "int", "2", "2"];
    ["let rec f (n:?) (x:?) = if n < 0 then x else f (n - 1) x in f 100 true", "bool", "true", "true"];
    ["let rec f n (x:?) = if n <= 0 then x else f 0 x in f 0 true", "bool", "true", "true"];
    ["let rec f n (x:?) = if n <= 0 then x else f 0 x in f 10 true", "bool", "true", "true"];
  ]

  let lists ~config = ext ~config [
    ["(1:?) :: []", "int list", "1 :: []", "1 :: []"];
    ["match ([(1, true); (2, false)] : ?) with | [] -> 0 | (x, y) :: t -> x", "int", "1", "1"];
  ]

  let matches ~config = ext ~config [
    ["let rec sum (l:?) = match l with [] -> 0 | h :: t -> h + sum t in sum [1; 2; 3; 4]", "int", "10", "10"];
    ["let rec sum l :? = match l with [] -> 0 | h :: t -> h + sum t in sum [1; 2; 3; 4]", "?", "10: int => ?", "10<<id{int};int!>>"];
    ["let rec sum (l:?) :? = match l with [] -> 0 | h :: t -> h + sum t in sum [1; 2; 3; 4]", "?", "10: int => ?", "10<<id{int};int!>>"];
    ["match (1, true : ?) with (x, y) -> x", "?", "1: int => ?", "1<<id{int};int!>>"];
    ["match (1, (2, 3) : ?) with (x, (y, z)) -> z", "?", "3: int => ?", "3<<id{int};int!>>"];
    ["let t = (((fun x -> x + 1), 2) : (? -> ?) * ?) in match t with (f, x) -> f x", "?", "3: int => ?", "3<<id{int};int!>>"];
  ]

  let tuples ~config = ext ~config [
    ["match ((1, 2, 3): ?) with (x, y, z) -> x + y + z", "int", "6", "6"];
    ["((1, 2, 3 : ?) : int * int)", "int * int", "blame+", "blame+"];
  ]

  let refs ~config = ext ~config [
    ["ref (1 : ?)", "? ref", "{ contents = 1: int => ?, ? }", "{ contents = 1<<id{int};int!>>, ? }"];
    ["!(ref (1 : ?))", "?", "1: int => ?", "1<<id{int};int!>>"];
    ["let r : ? ref = ref 1 in !r", "?", "1: int => ?", "1<<id{int};int!>>"];
    ["let r : ? ref = ref 1 in r := (2:?); !r", "?", "2: int => ?", "2<<id{int};int!>>"];
    ["let r = ref 1 in let s : ? ref = r in s := 2; !r", "int", "2", "2"];
    ["let r : ? ref = ref 1 in let s = r in s := 2; !s", "?", "2: int => ?", "2<<id{int};int!>>"];
    ["let r : ? ref = ref 1 in let s = r in s := 2; !r", "?", "2: int => ?", "2<<id{int};int!>>"];
  ]
end

module EagerLazy = struct
  let ext ~config ts = List.map (fun t -> List.map (fun (p, u, v_B_e, v_B_l, v_S_e, v_S_l) -> match config.intoB, config.eager with
    | true, true -> p, u, v_B_e
    | true, false -> p, u, v_B_l
    | false, true -> p, u, v_S_e
    | false, false -> p, u, v_S_l
    ) t) ts

  let application ~config = ext ~config [
    ["(fun (x: int * ?) -> x) (1, true)", "int * ?", "(1, true: bool => ?)", "(1, true): int * bool => int * ?", "(1, true<<id{bool};bool!>>)", "(1, true)<<id{int}*(id{bool};bool!)>>"];
    ["(fun (x: ?) -> x) (1, true)", "?", "(1: int => ?, true: bool => ?): (? * ?) => ?", "(1, true): int * bool => ? * ? => ?", "(1, true)<<(id{int};int!)*(id{bool};bool!);(? * ?)!>>", "(1, true)<<(id{int};int!)*(id{bool};bool!);(? * ?)!>>"];
    ["(fun (x: ?) -> (x : int * int)) (1, 2)", "int * int", "(1, 2)", "(1, 2): int * int => ? * ? => int * int", "(1, 2)", "(1, 2)"];
    ["(fun (x: ?) -> (x : int * int)) (1, true)", "int * int", "blame+", "(1, true): int * bool => ? * ? => int * int", "blame+", "(1, true)<<id{int}*⊥{bool,p,int}>>"];
  ]

  let lists ~config = ext ~config [
    ["([]:?)", "?", "[]: [?] => ?", "[]: 'a list => ? list => ?", "[]<<['a!p];[?]!>>", "[]<<['a!p];[?]!>>"];
    ["1 :: ([]:?)", "int list", "1 :: []", "1 :: []: 'a list => ? list => int list", "1 :: []", "1 :: []"];
    ["1 :: (2:?) :: ([]:?)", "int list", "1 :: 2 :: []", "1 :: (2: int => ? :: []: 'a list => ? list): ? list => int list", "1 :: 2 :: []", "1 :: (2<<id{int};int!>> :: []<<['a!p]>>)<<[int?p;id{int}]>>"];
    ["(([1; 2], true : ?) : int list * bool)", "int list * bool", "(1 :: 2 :: [], true)", "(1 :: 2 :: [], true): int list * bool => ? * ? => int list * bool", "(1 :: 2 :: [], true)", "(1 :: 2 :: [], true)"];
    ["let x = ([]:?) in let y = 3 :: x in let z = true :: x in y", "int list", "3 :: []", "3 :: []: 'a list => ? list => int list", "3 :: []", "3 :: []"];
  ]

  let tuples ~config = ext ~config [
    ["(1, true : int * ?)", "int * ?", "(1, true: bool => ?)", "(1, true): int * bool => int * ?", "(1, true<<id{bool};bool!>>)", "(1, true)<<id{int}*(id{bool};bool!)>>"];
    ["(1, true : ? * ?)", "? * ?", "(1: int => ?, true: bool => ?)", "(1, true): int * bool => ? * ?", "(1<<id{int};int!>>, true<<id{bool};bool!>>)", "(1, true)<<(id{int};int!)*(id{bool};bool!)>>"];
    ["(1, true : ?)", "?", "(1: int => ?, true: bool => ?): (? * ?) => ?", "(1, true): int * bool => ? * ? => ?", "(1, true)<<(id{int};int!)*(id{bool};bool!);(? * ?)!>>", "(1, true)<<(id{int};int!)*(id{bool};bool!);(? * ?)!>>"];
    ["((1, true : ?) : int * bool)", "int * bool", "(1, true)", "(1, true): int * bool => ? * ? => int * bool", "(1, true)", "(1, true)"];
    ["((1, true : ?) : ? * ?)", "? * ?", "(1: int => ?, true: bool => ?)", "(1, true): int * bool => ? * ?", "(1<<id{int};int!>>, true<<id{bool};bool!>>)", "(1, true)<<(id{int};int!)*(id{bool};bool!)>>"];
    ["((1, true : ?) : bool * int)", "bool * int", "blame+", "(1, true): int * bool => ? * ? => bool * int", "blame+", "(1, true)<<⊥{int,p,bool}*⊥{bool,p,int}>>"];
    ["(((1, true), 3 : ?) : (int * int) * int)", "(int * int) * int", "blame+", "((1, true), 3): (int * bool) * int => ? * ? => (int * int) * int", "blame+", "((1, true), 3)<<(id{int}*⊥{bool,p,int})*id{int}>>"];
    ["((1, (2, 3) : ?) : int * int)", "int * int", "blame+", "(1, (2, 3)): int * (int * int) => ? * ? => int * int", "blame+", "(1, (2, 3))<<id{int}*⊥{(? * ?),p,int}>>"];
  ]
end

module Monotonic = struct
  let ext ~config ts = List.map (fun t -> List.map (fun (p, u, v_B, v_S_m, v_S_n) -> match config.intoB, config.monotonic with
    | true, _ -> p, u, v_B
    | false, true -> p, u, v_S_m
    | false, false -> p, u, v_S_n
    ) t) ts

  let refs ~config = ext ~config [
    [
      "let f : ? = fun (x:?) -> x", "?", "<fun>: (? -> ?) => ?", "<fun><<id{? -> ?};(? -> ?)!>>", "<fun><<id{? -> ?};(? -> ?)!>>";
      "let r : ? = ref (f, (():?))", "?", "{ contents = (<fun>: (? -> ?) => ?, (): unit => ?), ? * ? }: (? * ?) ref => ? ref => ?", "{ contents = (<fun><<id{? -> ?};(? -> ?)!>>, ()<<id{unit};unit!>>), ? * ? }<<mref(?);:?:!>>", "{ contents = (<fun><<id{? -> ?};(? -> ?)!>>, ()<<id{unit};unit!>>), ? * ? }<<ref(id{? * ?};(? * ?)!,(? * ?)?p;id{? * ?});:?:!>>";
      "r := (f, r)", "unit", "()", "()", "()";
      "let g (x : ((? -> int) * ((int -> ?) * ?) ref) ref) = match !x with (y, z) -> (y:?) 42", "((? -> int) * ((int -> ?) * ?) ref) ref -> ?", "<fun>", "<fun>", "<fun>";
      "g r", "?", "42: int => ?", "42<<id{int};int!>>", "42<<id{int};int!>>";
    ]
  ]
end

(* ["match (1, true) : ? with ((x:int), (y:bool)) -> x", "int", "1", "1", "1", "1"]; *)
(* ["match (1, true) : ? with ((x:bool), (y:bool)) -> x", "bool", "blame+", "blame+", "blame+", "blame+"]; *)
(* ["let x, y = 1, true in x", "int", "1", "1", "1", "1"]; *)
(* ["let x, y = (1, true : ?) in x", "?", "1: int => ?", "...", "1: int => ?", "..."]; *)

(* let g = fun x -> ((fun y -> y):? -> ?) x in if g true then g 2 else g 3  *)

(* let minus_one x = x - 1 in let rec repeat n f x = if n = 0 then x else repeat (n-1) f (f x) in repeat 100000 minus_one 1000000;; *)

let suites ~config = 
  ignore config;
  [
    "Constants", Static.constants;
    "Unary Operations", Static.unary_ops;
    "Binary Operations", Static.binary_ops;
    "Binary Operations (Gradual)", Gradual.binary_ops ~config;
    "Type Ascription", Gradual.type_ascription ~config;
    "If Expression", Static.if_then_else;
    "Let Definition", Static.let_definition;
    "Abstraction", Static.abstraction;
    "Abstraction (Gradual)", Gradual.abstraction ~config;
    "Application", Static.application;
    "Application (Gradual)", Gradual.application ~config;
    "Application (EagerLazy)", EagerLazy.application ~config;
    "Sequence", Static.sequence;
    "Sequence (Gradual)", Gradual.sequence ~config;
    "Dinamic Type Inference", Gradual.dti ~config;
    "Let Polymorphism", Static.let_poly;
    "Let Polymorphism (Gradual)", Gradual.let_poly ~config;
    "Let Polymorphism in Toplevel", Static.let_poly_toplevel;
    "Let Polymorphism in Toplevel (Gradual)", Gradual.let_poly_toplevel ~config;
    "Let Polymorphism & Recursion", Static.let_poly_recursion;
    "Let Polymorphism & Recursion (Gradual)", Gradual.let_poly_recursion ~config;
    "List", Static.lists;
    "List (Gradual)", Gradual.lists ~config;
    "List (EagerLazy)", EagerLazy.lists ~config;
    "Match Expression", Static.matches;
    "Match Expression (Gradual)", Gradual.matches ~config; 
    "Tuple", Static.tuples;
    "Tuple (Gradual)", Gradual.tuples ~config;
    "Tuple (EagerLazy)", EagerLazy.tuples ~config;
    "Reference", Static.refs;
    "Reference (Gradual)", Gradual.refs ~config;
    "Reference (Monotonic)", Monotonic.refs ~config;
    "Functions in Standard Library", Static.stdlibs;
  ]