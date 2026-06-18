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

  let test_pp_program =
    let test (e) =
      e >:: fun ctxt ->
        assert_equal ~ctxt:ctxt ~printer:id e @@ asprintf "%a" pp_program @@ parse (e ^ ";;")
    in
    List.map test [
      "fun (x: ?) -> fun (y: ?) -> fun (z: ?) -> z";
      "x (y z)";
      "x y z";
      "1 * 2 + 3 * 4";
      "(1 + 2) * (3 + 4)";
      "(fun (x: ?) -> x) (fun (y: ?) -> y)";
      "1 + (2 : ?)";
    ]

  let suite = [
    "test_pp_program">::: test_pp_program;
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
      CAppExp (FunBExp (("x", TyDyn), x), CoercionExp (CInj Ar));
      "x<int!>", CAppExp (x, CoercionExp (CInj I));
      "x<int!><bool?p>", CAppExp (CAppExp (x, CoercionExp (CInj I)), CoercionExp (CProj (B, (r, Pos))));
      "(fun (x: ?) -> x) (fun (y: ?) -> y)",
      AppMExp (FunBExp (("x", TyDyn), x), FunBExp (("y", TyDyn), y));
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
