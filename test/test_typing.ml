open Format

open OUnit2

open Lambda_S_dti
open Syntax
open Typing

let id x = x

module ITGL = struct
  open Typing.ITGL

  let parse str =
    Parser.toplevel Lexer.main @@ Lexing.from_string str

  let test_type_of_program =
    let tyenv = Environment.empty in
    let test (program, expected) =
      program >:: fun ctxt ->
        let e = parse @@ program ^ ";;" in
        let e, u = Typing.ITGL.type_of_program tyenv e in
        let tyenv, e, u = Typing.ITGL.normalize tyenv e u in
        let _, f_b, u_b = Translate.ITGL.translate ~intoB:true tyenv e in
        let _, f_s, u_s = Translate.ITGL.translate ~intoB:false tyenv e in
        let u_b' = Typing.CC.type_of_program tyenv f_b in
        let u_s' = Typing.CC.type_of_program tyenv f_s in
        let assert_ty_equal msg expected_ty actual_ty =
          assert_equal ~ctxt
            ~printer:(fun t -> asprintf "%a" Pp.pp_ty2 t)
            expected_ty
            actual_ty
            ~msg
        in
        assert_ty_equal "ITGL u_b" u u_b;
        assert_ty_equal "ITGL u_s" u u_s;
        assert_ty_equal "CC u_b'" u u_b';
        assert_ty_equal "CC u_s'" u u_s';
        assert_equal ~ctxt:ctxt ~printer:id expected @@ asprintf "%a" Pp.pp_ty2 u
    in
    List.map test [
      "1", "int";
      "true", "bool";
      "1 + 2 + 3", "int";
      "(true : ?)", "?";
      "((true : ?) : int)", "int";
      "fun x -> x + 1", "int -> int";
      "fun x -> x", "'a -> 'a";
      "fun (x:?) -> x + 2", "? -> int";
      "(fun (x:?) -> x + 2) 3", "int";
      "(fun (x:?) -> x + 2) true", "int";
      "(fun (x:?) -> x 2) (fun y -> true)", "?";
      "(fun (x:?) -> x) (fun y -> y)", "?";
      "(fun (x:?) -> x 2) (fun y -> y)", "?";
      "fun x y -> x y", "('a -> 'b) -> 'a -> 'b";
      "fun y z -> z (z y)", "'a -> ('a -> 'a) -> 'a";
      "fun x y z -> x z (y z)", "('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c";
      "fun x y -> x", "'a -> 'b -> 'a";
      "let id x = x", "'a -> 'a";
      "let dynid (x:?) = x", "? -> ?";
      "let succ x = x + 1", "int -> int";
      "let id x = x in let did (x:?) = x in let succ x = x + 1 in (fun (x:?) -> x 1) (id (did succ))", "?";
      "let id x = x in let did (x:?) = x in let succ x = x + 1 in (fun (x:?) -> x true) (id (did succ))", "?";
      "let rec f x (y:bool) z: int = 1 in f", "'a -> bool -> 'b -> int";
      (* list *)
      "[]", "'a list";
      "1 :: []", "int list";
      "true :: false :: []", "bool list";
      "[1; 2; 3]", "int list";
      "fun x -> x :: []", "'a -> 'a list";
      "fun x y -> x :: y", "'a -> 'a list -> 'a list";
      "let id x = x in [id 1; 2]", "int list";
      "(1 : ?) :: []", "'a list";
      "1 :: (([] : ?) : int list)", "int list";
      (* tuple *)
      "(1, true)", "int * bool";
      "((1, 2), 3)", "(int * int) * int";
      "fun x y -> (x, y)", "'a -> 'b -> 'a * 'b";
      "((1 : ?), false)", "? * bool";
      (* ref *)
      "ref 1", "int ref";
      "!(ref true)", "bool";
      "let x = ref 1 in x := 2", "unit";
      "let x = ref 1 in x := 2; !x", "int";
      "fun x -> x := !x + 1", "int ref -> unit";
      "ref (1 : ?)", "? ref";
      "!(ref (1 : ?))", "?";
      (* value restrection *)
      "let id = fun x -> x in (id 1, id true)", "int * bool";
      "let empty = [] in (1 :: empty, true :: empty)", "int list * bool list";
      "let r = ref [] in r := [1]; !r", "int list";
      (* complex *)
      "ref []", "'a list ref";
      "[(1, true); (2, false)]", "(int * bool) list";
      "let x = ref [1; 2] in !x", "int list";
    ]

  let test_type_of_program_errors =
    let tyenv = Environment.empty in
    let test program =
      program >:: fun _ ->
        let e = parse @@ program ^ ";;" in
        (* NOTE: Currently we do not care about contents of the exception *)
        let message = begin
          try
            ignore @@ type_of_program tyenv e;
            Some (asprintf "Type_error is not raised: '%s'" program)
          with
          | Type_error _ ->
            (* OK *)
            None
          | _ ->
            Some (asprintf "Unexpected exception is raised: '%s'" program)
        end in
        match message with
        | None -> ()
        | Some m -> assert_failure m
    in
    List.map test [
      "1 + true";
      "true * false";
      "1 < false";
      "if 0 then true else false";
      "if true then 1 else false";
      "x";
      "let f (x:'a) = x in f (); f true";
      "let rec f (x:'a) = x in f (); f true";
      (* list *)
      "1 :: true";
      "1 :: [true]";
      "[1; true]";
      "let f (x: int list) = x in f [true]";
      (* tuple *)
      "let f (x: int * int) = x in f (1, true)";
      "let f (x: int * int) = x in f 1";
      (* ref *)
      "!1";
      "1 := 2";
      "let x = ref 1 in x := true";
      "let x = ref 1 in x := !x + true";
      (* value restriction *)
      "let f = (fun x -> x) (fun y -> y) in (f 1, f true)";
      (* TODO: "let r = ref [] in let _ = (r := [1]) in (r := [true])"; *)
      "let r = ref [] in let x = (r := [1]) in (r := [true])";
      "let r = ref [] in (1 :: !r, true :: !r)";
      "let r = ref (fun x -> x) in r := (fun x -> x + 1); !r true";
    ]

  let suite = [
    "test_type_of_program">::: test_type_of_program;
    "test_type_of_program_errors">::: test_type_of_program_errors;
  ]
end

let suite = [
  "test_ITGL">::: ITGL.suite;
]
