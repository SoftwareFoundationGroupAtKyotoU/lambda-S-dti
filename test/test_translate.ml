open Format
open OUnit2
open Lambda_S_dti
open Syntax

let id x = x

module CC_Translation = struct
  let parse str =
    Parser.toplevel Lexer.main @@ Lexing.from_string str

  let test_translation =
    let tyenv = Environment.empty in
    let test (program, expected_cc_b, expected_cc_s) =
      program >:: fun ctxt ->
        let e = parse @@ program ^ ";;" in
        let _, f_b, _ = Translate.ITGL.translate ~intoB:true tyenv e in
        let _, f_s, _ = Translate.ITGL.translate ~intoB:false tyenv e in
        (* CCのASTを文字列化（※ pp_cc_program はご自身の関数名に合わせてください） *)
        let actual_cc_b = asprintf "%a" Pp.CC.pp_program f_b in
        let actual_cc_s = asprintf "%a" Pp.CC.pp_program f_s in
        assert_equal ~ctxt:ctxt ~printer:id expected_cc_b actual_cc_b;
        assert_equal ~ctxt:ctxt ~printer:id expected_cc_s actual_cc_s;
    in
    List.map test [
      "1", "1", "1";
      "true", "true", "true";
      (* TODO: "fun x -> x", "fun (x : 'a) -> x"; *)

      "(1 : ?)", "1: int => ?", "1<id{int};int!>";
      "(true : ?)", "true: bool => ?", "true<id{bool};bool!>";
      "((1 : ?) : bool)", "1: int => ? => bool", "1<id{int};int!><bool?p;id{bool}>";

      "(1 : ?) + 2", "(1: int => ? => int) + 2", "1<id{int};int!><int?p;id{int}> + 2";
      "1 + (2 : ?)", "1 + (2: int => ? => int)", "1 + 2<id{int};int!><int?p;id{int}>";
      "if (true : ?) then 1 else 2", "if true: bool => ? => bool then 1 else 2", "if true<id{bool};bool!><bool?p;id{bool}> then 1 else 2";
      "let x : ? = 1 in x", "let x = 1: int => ? in x", "let x = 1<id{int};int!> in x";
      "let f (x: int) = x in f (1 : ?)", "let f = fun (x: int) -> x in f (1: int => ? => int)", "let f = fun (x: int) -> x in f (1<id{int};int!><int?p;id{int}>)";
      
      "((1, true) : ?)", "(1, true): int * bool => ?", "(1, true)<(id{int};int!)*(id{bool};bool!);(? * ?)!>";
      (* TODO: "(1 : ?) :: []", "((1 : int => ?) : ? => int) :: []"; *)

      "ref (1 : ?)", "ref (1: int => ?)@?", "ref (1<id{int};int!>)@?";
      "let r = ref (1 : ?) in !r + 1", "let r = ref (1: int => ?)@? in (!r@?: ? => int) + 1", "let r = ref (1<id{int};int!>)@? in !r@?<int?p;id{int}> + 1";

      "((fun (x: int) -> x + 1) : ? -> ?)", "(fun (x: int) -> x + 1): int -> int => ? -> ?", "(fun (x: int) -> x + 1)<(int?p;id{int})->(id{int};int!)>";
    ]

  let suite = [
    "test_translation">::: test_translation;
  ]
end

let suite = [
  "CC_Translation" >::: CC_Translation.suite;
]
