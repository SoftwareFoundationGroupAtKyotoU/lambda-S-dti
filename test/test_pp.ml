open Format

open OUnit2

open Lambda_S_dti
open Syntax
open Pp

let id x = x

let parse str =
  Parser.toplevel Lexer.main @@ Lexing.from_string str

let tv n = TyVar (n, ref None)

let test_pp_ty =
  let test (expected, u) =
    expected >:: fun ctxt ->
      assert_equal ~ctxt:ctxt ~printer:id expected @@ asprintf "%a" pp_ty u
  in
  List.map test [
    (* type variables *)
    "'x1", tv 1;
    "'x999", tv 999;
    "'x1 -> 'x2", TyFun (tv 1, tv 2);
    "'x2 -> 'x1", TyFun (tv 2, tv 1);
    "'x1 -> 'x1", TyFun (tv 1, tv 1);
    "('x1 -> 'x2) -> 'x1", TyFun (TyFun (tv 1, tv 2), tv 1);
    (* functions *)
    "int -> bool", TyFun (TyInt, TyBool);
    "int -> bool -> ?", TyFun (TyInt, TyFun (TyBool, TyDyn));
    "(int -> bool) -> ?", TyFun (TyFun (TyInt, TyBool), TyDyn);
    "(int -> bool) -> ? -> int", TyFun (TyFun (TyInt, TyBool), TyFun (TyDyn, TyInt));
    (* lists *)
    "int list", TyList TyInt;
    "? list list", TyList (TyList TyDyn);
    "int -> ? list", TyFun (TyInt, TyList TyDyn); 
    "(int -> ?) list", TyList (TyFun (TyInt, TyDyn)); 
    (* tuples *)
    "int * bool", TyTuple [TyInt; TyBool];
    "int * bool * unit", TyTuple [TyInt; TyBool; TyUnit];
    "int * bool -> ?", TyFun (TyTuple [TyInt; TyBool], TyDyn); 
    "int * (bool -> ?)", TyTuple [TyInt; TyFun (TyBool, TyDyn)]; 
    "(int -> ?) * bool", TyTuple [TyFun (TyInt, TyDyn); TyBool];
    (* references *)
    "int ref", TyRef TyInt;
    "bool ref ref", TyRef (TyRef TyBool);
    "int -> ? ref", TyFun (TyInt, TyRef TyDyn); 
    "(int -> ?) ref", TyRef (TyFun (TyInt, TyDyn)); 
    (* complex *)
    "int list ref", TyRef (TyList TyInt);
    "int ref list", TyList (TyRef TyInt);
    "int ref * bool list", TyTuple [TyRef TyInt; TyList TyBool];
  ]

let test_pp_ty2 =
  let test (expected, u) =
    expected >:: fun ctxt ->
      assert_equal ~ctxt:ctxt ~printer:id expected @@ asprintf "%a" pp_ty2 u
  in
  List.map test [
    "int -> bool", TyFun (TyInt, TyBool);
    "(int -> bool) -> ?", TyFun (TyFun (TyInt, TyBool), TyDyn);
    "int ref list", TyList (TyRef TyInt);
    "'a", tv 1;
    "'a -> 'b", TyFun (tv 1, tv 2);
    "'a -> 'b", TyFun (tv 2, tv 1); 
    "'a -> 'a", TyFun (tv 1, tv 1); 
    "('a -> 'b) -> 'a", TyFun (TyFun (tv 1, tv 2), tv 1);
    "'a * 'b * 'a", TyTuple [tv 1; tv 2; tv 1];
    "'a list -> 'a ref", TyFun (TyList (tv 1), TyRef (tv 1));
  ]

module ITGL = struct
  open Pp.ITGL

  let test_exact =
    let test e =
      e >:: fun ctxt ->
        assert_equal ~ctxt:ctxt ~printer:id e @@ asprintf "%a" pp_program @@ parse (e ^ ";;")
    in
    List.map test [
      "42";
      "true";
      "false";
      "()";

      "1 + 2 + 3";
      "1 - 2 - 3";
      "1 * 2 * 3";
      "1 / 2 / 3";
      "1 + 2 * 3";
      "1 * 2 + 3";
      "(1 + 2) * 3";
      "1 = 2";
      "1 <> 2";
      "1 < 2 + 3";
      "1 + 2 >= 3 * 4";

      "fun (x: ?) -> fun (y: ?) -> fun (z: ?) -> z";
      "x y z";
      "x (y z)";
      "f x + 1";
      "f (x + 1)";

      "1 + (2 : ?)";
      "(1 + 2 : int)";
      "(f (x : int) : bool)";

      "[]";
      "1 :: []";
      "1 :: 2 :: []";
      "(1 :: 2) :: []";
      "1 + 2 :: 3 * 4 :: []";
      "f x :: y";

      "(1, 2)";
      "(1, 2, 3)";
      "((1, 2), 3)";
      "(1, (2, 3))";
      "(1 + 2, 3 * 4)";

      "ref 1";
      "!x";
      "x := 1";
      "!x + 1";
      "!(x + 1)";
      "ref (x y)";
      "!f x";
      "!(f x)";
      "x := y := 1";
      "(x := y) := 1";
      "x := !x + 1";

      "if true then 1 else 2";
      "if 1 = 2 then x else y";
      "if a then b else if c then d else e";
      "let x = 1 in x + 1";
      "let x = 1 in let y = 2 in x + y";
      "match x with | y -> 1";
      
      "let x = 1 + 2";
      (* TODO: "let rec f (x: int) : int = f x"; *)
    ]

  let test_desugar =
    let test (input, expected) =
      input >:: fun ctxt ->
        assert_equal ~ctxt:ctxt ~printer:id expected @@ asprintf "%a" pp_program @@ parse (input ^ ";;")
    in
    List.map test [
      "true || false", "if true then true else if false then true else false";
      "true && false", "if true then if false then true else false else false";

      "-1", "0 - 1";
      "-x", "0 - x";
      "+1", "1";
      "+x", "x";

      "() ; 2", "let _ = (() : unit) in 2";
      "1 ; 2 ; 3", "let _ = (1 : unit) in let _ = (2 : unit) in 3";

      "[1]", "1 :: []";
      "[1; 2; 3]", "1 :: 2 :: 3 :: []";

      (* TODO: "fun x y -> x", "fun (x: 'x265) -> fun (y: 'x264) -> x"; *)
      "fun (x: int) (y: bool) -> x", "fun (x: int) -> fun (y: bool) -> x";

      (* TODO: "let f x y = x", "let f = fun (x: 'x308) -> fun (y: 'x307) -> x"; *)
      "let f (x: int) (y: bool) : int = x", "let f = fun (x: int) -> fun (y: bool) -> (x : int)";
      
      (* TODO: "let rec f x y = x", "let f = fix f (x: 'x312): 'x313 -> 'x311 = fun (y: 'x313) -> x"; *)
      (* TODO: "let rec f (x: int) (y: bool) : int = x", "let f = fix f (x: int): bool -> int = fun (y: bool) -> x"; *)
    ]

  let suite = [
    "test_pp_program_exact">::: test_exact;
    "test_pp_program_desugar">::: test_desugar;
  ]
end

module CC = struct
  open Pp.CC
  open Syntax.CC

  let r = Utils.Error.dummy_range

  let test_pp_exp =
    let test (expected, f) =
      expected >:: fun ctxt ->
        assert_equal ~ctxt:ctxt ~printer:id expected @@ asprintf "%a" pp_exp f
    in
    let x, y, z = Var ("x", []), Var ("y", []), Var ("z", []) in
    List.map test [
      "x y z", AppMExp (AppMExp (x, y), z);
      "x (y z)", AppMExp (x, AppMExp (y, z));
      "x * y + z * x", BinOp (Plus, BinOp (Mult, x, y), BinOp (Mult, z, x));
      "(x + y) * (z + x)", BinOp (Mult, BinOp (Plus, x, y), BinOp (Plus, z, x));
      "(fun (x: ?) -> x)<(? -> ?)!>",
      CAppExp (FunBExp ([], ("x", TyDyn), x), CoercionExp (CInj Ar));
      "x<int!>", CAppExp (x, CoercionExp (CInj I));
      "x<int!><bool?p>", CAppExp (CAppExp (x, CoercionExp (CInj I)), CoercionExp (CProj (B, (r, Pos))));
      "(fun (x: ?) -> x) (fun (y: ?) -> y)",
      AppMExp (FunBExp ([], ("x", TyDyn), x), FunBExp ([], ("y", TyDyn), y));
      "x y<int!>", CAppExp (AppMExp (x, y), CoercionExp (CInj I));
      "x (y<int!>)", AppMExp (x, CAppExp (y, CoercionExp (CInj I)));
    ]

  let suite = [
    "test_pp_exp">::: test_pp_exp;
  ]
end

let suite = [
  "test_pp_ty">::: test_pp_ty;
  "test_pp_ty2">::: test_pp_ty2;
  "test_ITGL">::: ITGL.suite;
  "test_CC">::: CC.suite;
]
