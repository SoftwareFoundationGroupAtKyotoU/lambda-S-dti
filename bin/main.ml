open Format
open Lambda_S1_dti

exception Compile_bad of string
exception Invalid_option of string

let debug = ref false
let ls1 = ref false
let alt = ref false
let compile = ref false

let programs = ref [] (*Stdlibのために、要変更*)

let opt_file = ref None

let rec read_eval_print lexbuf env tyenv alphaenv kfunenvs kenv =
  (* Used in all modes *)
  let print f = fprintf std_formatter f in
  (* Used in debug mode *)
  let print_debug f = Utils.Format.make_print_debug !debug f in
  flush stderr;
  flush stdout;
  if lexbuf.Lexing.lex_curr_p.pos_fname = "" then print "# @?";
  begin try
      (* Parsing *)
      print_debug "***** Parser *****\n";
      let e = Parser.toplevel Lexer.main lexbuf in
      print_debug "e: %a\n" Pp.ITGL.pp_program e;
      (* programs := e :: !programs; *)

      (* Type inference *)
      print_debug "***** Typing *****\n";
      let e, u = Typing.ITGL.type_of_program tyenv e in
      print_debug "e: %a\n" Pp.ITGL.pp_program e;
      print_debug "U: %a\n" Pp.pp_ty u;

      (* NOTE: Typing.ITGL.translate and Typing.LS.type_of_program expect
       * normalized input *)
      let tyenv, e, u = Typing.ITGL.normalize tyenv e u in
      
      (* Translation *)
      print_debug "***** Coercion-insertion *****\n";
      let new_tyenv, f, u' = Translate.ITGL.translate tyenv e in 
      print_debug "f: %a\n" Pp.LS.pp_program f;
      print_debug "U: %a\n" Pp.pp_ty u';
      assert (Typing.is_equal u u');
      let u'' = Typing.LS.type_of_program tyenv f in
      assert (Typing.is_equal u u'');
      print_debug "f: %a\n" Pp.LS.pp_program f;
      let f, alphaenv = KNormal.LS.alpha_program alphaenv f in 
      let f = 
        if !alt then Translate.LS.translate_alt tyenv f
        else Translate.LS.translate tyenv f 
      in
      print_debug "f: %a\n" Pp.LS1.pp_program f;

      let (env, alphaenv, kfunenvs, kenv) = 
      if !ls1 then begin
      (* Evaluation *)
      print_debug "***** Eval *****\n";
      (* let f, u''' = 
        if !alt then Translate.LS.translate_alt tyenv f
        else Translate.LS.translate tyenv f 
      in *)
      let env, x, v = Eval.LS1.eval_program env f ~debug:!debug
      in print "%a : %a = %a\n"
        pp_print_string x
        Pp.pp_ty2 u
        Pp.LS1.pp_value v;
      (env, alphaenv, kfunenvs, kenv)
      end
      else begin
      (* k-Normalization *)
      print_debug "***** kNormal *****\n";
      (* let kf, _ = KNormal.kNorm_funs kfunenvs f ~debug:!debug in *)
      (* let kf = 
        if !alt then Translate.KNorm.translate_alt kf
        else Translate.KNorm.translate kf 
      in *)
      (* let kf = KNormal.LS1.k_normalize_program f in *)
      let kf, kfunenvs = KNormal.kNorm1_funs kfunenvs f ~debug:!debug in
      print_debug "kf: %a\n" Pp.KNorm1.pp_program kf;
      (* Evaluation on kNormalized term *)
      print_debug "***** Eval *****\n";
      let kenv, kx, kv = Eval.KNorm1.eval_program kenv kf ~debug:!debug in
      print_debug "k-Normal :: ";
      print_debug "%a : %a = %a\n"
        pp_print_string kx
        Pp.pp_ty2 u
        Pp.KNorm1.pp_value kv;
      (env, alphaenv, kfunenvs, kenv)
      end in
      read_eval_print lexbuf env new_tyenv alphaenv kfunenvs kenv 
      (* TODO: new_tyenv need? *)
    with
    | Failure message ->
      print "Failure: %s\n" message;
      Utils.Lexing.flush_input lexbuf
    | Parser.Error -> (* Menhir *)
      let token = Lexing.lexeme lexbuf in
      print "Parser.Error: unexpected token %s\n" token;
      Utils.Lexing.flush_input lexbuf
    | Typing.Type_error message ->
      print "Type_error: %s\n" message
    | Eval.Blame (r, p) -> begin
        match p with
        | Pos -> print "Blame on the expression side:\n%a\n" Utils.Error.pp_range r
        | Neg -> print "Blame on the environment side:\n%a\n" Utils.Error.pp_range r
      end
    | Eval.KBlame (r, p) -> begin
        match p with
        | Pos -> print "Blame on the expression side:\n%a\n" Utils.Error.pp_range r
        | Neg -> print "Blame on the environment side:\n%a\n" Utils.Error.pp_range r
      end
  end;
  (match !opt_file with
    | None -> (*programs := [];*) read_eval_print lexbuf env tyenv alphaenv kfunenvs kenv
    | Some _ ->())

let compile_process progs _ tyenv alphaenv kfunenvs _ = 
  (* Used in all modes *)
  (*let print f = fprintf std_formatter f in*)
  (* Used in debug mode *)
  let print_debug f = Utils.Format.make_print_debug !debug f in
  let rec to_exp ps = match ps with
    | Syntax.ITGL.Exp e :: [] -> e
    | Syntax.ITGL.LetDecl (x, e) :: t -> Syntax.ITGL.LetExp (Utils.Error.dummy_range, x, e, to_exp t)
    | _ -> raise @@ Compile_bad "exp appear in not only last"
  in let e = Syntax.ITGL.Exp (to_exp (List.rev progs)) in
  begin try
    print_debug "\n========== Compilation ==========\n";

    (* Type inference *)
    print_debug "***** Typing *****\n";
    let e, u = Typing.ITGL.type_of_program tyenv e in
    print_debug "e: %a\n" Pp.ITGL.pp_program e;
    print_debug "U: %a\n" Pp.pp_ty u;

    (* NOTE: Typing.ITGL.translate and Typing.LS.type_of_program expect
     * normalized input *)
    let tyenv, e, u = Typing.ITGL.normalize tyenv e u in

    (* Translation *)
    print_debug "***** Cast-insertion *****\n";
    let _, f, u' = Translate.ITGL.translate tyenv e in
    print_debug "f: %a\n" Pp.LS.pp_program f;
    print_debug "U: %a\n" Pp.pp_ty u';
    assert (Typing.is_equal u u');
    let u'' = Typing.LS.type_of_program tyenv f in
    assert (Typing.is_equal u u'');
    let f, _ = KNormal.LS.alpha_program alphaenv f in
    print_debug "f: %a\n" Pp.LS.pp_program f;
      (* let f, u''' = 
        if !alt then Translate.LS.translate_alt tyenv f
        else Translate.LS.translate tyenv f 
      in
      (* assert (Typing.is_equal u u'''); *)
      print_debug "f: %a\n" Pp.LS1.pp_program f; *)

    (* k-Normalization *)
    print_debug "***** kNormal *****\n";
    let kf, _ = KNormal.kNorm_funs kfunenvs f ~debug:!debug in
    let kf = 
      if !alt then Translate.KNorm.translate_alt kf
      else Translate.KNorm.translate kf 
    in
    let kf, _ = KNormal.kNorm1_funs_simpl kfunenvs kf ~debug:!debug in 
    (* print_debug "f: %a\n" Pp.LS1.pp_program f;  *)
    print_debug "kf: %a\n" Pp.KNorm1.pp_program kf;

    let p = match kf with Syntax.KNorm1.Exp e -> e | _ -> raise @@ Compile_bad "kf is not exp" in

    print_debug "***** Closure *****\n";
    let p = Closure.KNorm1.toCls_program p in
    print_debug "%a\n" Pp.Cls.pp_program p;

    print_debug "***** toC *****\n";
    let toC_program = ToC.toC_program !alt in
    let c_code = asprintf "%a" toC_program p in
    print_debug "%s\n" c_code;
    c_code
    
  with
  | Failure message -> raise @@ Failure message
  | Typing.Type_error message -> raise @@ Typing.Type_error message
  end

let rec read_compile lexbuf env tyenv alphaenv kfunenvs kenv = 
  (* Used in all modes *)
  let print f = fprintf std_formatter f in
  (* Used in debug mode *)
  let print_debug f = Utils.Format.make_print_debug !debug f in
  flush stderr;
  flush stdout;
  if lexbuf.Lexing.lex_curr_p.pos_fname = "" then print "# @?";
  try
    print_debug "***** Parser *****\n";
    let e = Parser.toplevel Lexer.main lexbuf in
    print_debug "e: %a\n" Pp.ITGL.pp_program e;
    programs := e :: !programs;

    match e, !opt_file with
    | Syntax.ITGL.Exp _, None -> 
        let c_code = compile_process !programs env tyenv alphaenv kfunenvs kenv in
        (* Printf.printf "%s\n" c_code; *)
        programs := [];
        let oc = open_out "result_C/stdout.c" in
        Printf.fprintf oc "%s" c_code;
        close_out oc;
        let _ = Sys.command "gcc result_C/stdout.c lib/cast.c -I/mnt/c/gc/include /mnt/c/gc/lib/libgc.so -o result/stdout.out -O2 -g3" in
        let _ = Sys.command "result/stdout.out" in
        print "\n";
        read_compile lexbuf env (*new_*)tyenv alphaenv kfunenvs kenv
    | Syntax.ITGL.Exp _, Some f -> 
        let c_code = compile_process !programs env tyenv alphaenv kfunenvs kenv in
        programs := [];
        let oc = open_out ("../result_C/"^f^"_out.c") in
        Printf.fprintf oc "%s" c_code;
        close_out oc;
        let _ = Sys.command ("gcc ../result_C/"^f^"_out.c ../lib/cast.c -I/mnt/c/gc/include /mnt/c/gc/lib/libgc.so -o ../result/"^f^".out -O2") in
        let _ = Sys.command ("../result/"^f^".out") in
        print "\n"
    | _, None -> read_compile lexbuf env (*new_*)tyenv alphaenv kfunenvs kenv
    | _, Some f ->
        if lexbuf.lex_eof_reached then
          let c_code = compile_process !programs env tyenv alphaenv kfunenvs kenv in
          let oc = open_out ("../result/"^f^"_out.c") in
          Printf.fprintf oc "%s" c_code;
          close_out oc
        else 
          read_compile lexbuf env (*new_*)tyenv alphaenv kfunenvs kenv
  with
    | Failure message ->
      print "Failure: %s\n" message;
      Utils.Lexing.flush_input lexbuf
    | Parser.Error -> (* Menhir *)
      let token = Lexing.lexeme lexbuf in
      print "Parser.Error: unexpected token %s\n" token;
      Utils.Lexing.flush_input lexbuf
    | Typing.Type_error message ->
      print "Type_error: %s\n" message
    | ToC.ToC_error message ->
      print "%s\n" message

let start file =
  let print_debug f = Utils.Format.make_print_debug !debug f in
  opt_file := file;
  print_debug "***** Lexer *****\n";
  let channel, lexbuf = match file with
    | None ->
        print_debug "Reading from stdin\n%!";
        stdin, Lexing.from_channel stdin
    | Some f ->
        print_debug "Reading from file \"%s\"\n%!" f;
        let channel = open_in f in
        let lexbuf = Lexing.from_channel channel in
        lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = f};
        channel, lexbuf
  in
  let env, tyenv, alphaenv, kfunenvs, kenv = Stdlib.pervasives in
  try
    if !compile && !ls1 then raise @@ Invalid_option "-c and -LS1 are imcompatible"
    else if !compile then read_compile lexbuf env tyenv alphaenv kfunenvs kenv
    else read_eval_print lexbuf env tyenv alphaenv kfunenvs kenv
  with
    | Lexer.Eof ->
      (* Exiting normally *)
      close_in channel
    | Stdlib.Stdlib_exit i ->
      (* Exiting with the status code *)
      close_in channel;
      exit i
    | e ->
      (* Unexpected error occurs, close the opened channel *)
      close_in_noerr channel;
      raise e

let () =
  let program = Sys.argv.(0) in
  let usage =
    "Interpreter of the ITGL with dynamic type inference\n" ^
    asprintf "Usage: %s <options> [file]\n" program ^
    "Options: "
  in
  let file = ref None in
  let options = Arg.align [
      ("-d", Arg.Set debug, " Enable debug mode");
      ("-LS1", Arg.Set ls1, " Evaluate on LS1");
      ("-alt", Arg.Set alt, " Use alternative translation");
      ("-c", Arg.Set compile, " Compile the program to C code and run it");
    ]
  in
  let parse_argv arg = match !file with
    | None -> file := Some arg
    | Some _ -> raise @@ Arg.Bad "error: only one file can be specified"
  in
  Arg.parse options parse_argv usage;
  start !file


(* let rec id x y = id x y in 0;;

let id_30 = fun 'x10,'x11,'x12 -> fix id_30 ((x_31: 'x11), k1): 'x12 -> 'x10 = 
  (fun ((y_32: 'x12), k3) -> 
   (id_30 x_31 (y_32) 
  | id_30 x_31 (y_32, k3)) 
| (fun ((y_32: 'x12), k2) -> 
   (id_30 x_31 (y_32) 
  | id_30 x_31 (y_32, k2)))<k1>) 
in 0

let id_30 = fun 'x10,'x11,'x12 -> fun (x_31, k1) -> 
  (let _var_33 = fun (y_32, k3) -> 
    (let _var_34 = id_30 x_31 in _var_34 y_32 
   | let _var_35 = id_30 x_31 in _var_35 (y_32, k3)) 
  in _var_33 | 
  let _var_36 = fun (y_32, k2) -> 
   (let _var_37 = id_30 x_31 in _var_37 y_32 
  | let _var_38 = id_30 x_31 in _var_38 (y_32, k2)) 
  in _var_36<k1>) 
in 0

let id_30 = fun 'x10,'x11,'x12 -> fun (x_31, k25) -> 
  (let _var_33 = fun (y_32, k29) -> 
   (let _var_34 = id_30 x_31 in _var_34 y_32 
  | let _var_34 = id_30 x_31 in _var_34 (y_32, k29)) 
  in _var_33 
| let _var_33 = fun (y_32, k26) -> 
   (let _var_34 = id_30 x_31 in _var_34 y_32 
  | let _var_34 = id_30 x_31 in _var_34 (y_32, k26)) 
  in _var_33<k25>) 
in 0 *)