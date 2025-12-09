open Format
open Lambda_S1_dti

exception Compile_bad of string
exception Invalid_option of string

let debug = ref false
let k = ref false
let alt = ref false
let compile = ref false

let programs = ref []

let opt_file = ref None

let rec read_eval_print lexbuf env tyenv kfunenvs kenv =
  (* Used in all modes *)
  let print f = fprintf std_formatter f in
  (* Used in debug mode *)
  (* for ref debug, print_debug is defined in each function *)
  let print_debug f = Utils.Format.make_print_debug !debug f in
  flush stderr;
  flush stdout;
  if lexbuf.Lexing.lex_curr_p.pos_fname = "" then print "# @?";
  begin try
    (* Parsing *)
    let e = Parser.toplevel Lexer.main lexbuf in
    print_debug "***** Parser *****\n";
    print_debug "e: %a\n" Pp.ITGL.pp_program e;

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
    (* new_tyenv include current LetDecl type, so type check and translation must be executed in old tyenv *)
    print_debug "f: %a\n" Pp.LS.pp_program f;
    print_debug "U: %a\n" Pp.pp_ty u';
    assert (Typing.is_equal u u');
    let u'' = Typing.LS.type_of_program tyenv f in
    assert (Typing.is_equal u u'');

    print_debug "***** CPS-translation *****\n";
    let f(*, u'''*) =                                  (* TODO: tlanslation into LS1 should return type u'''? *)
      if !alt then Translate.LS.translate_alt tyenv f
      else Translate.LS.translate tyenv f 
    in
    (* assert (Typing.is_equal u u'''); *)
    print_debug "f: %a\n" Pp.LS1.pp_program f;

    let (env, kfunenvs, kenv) = 
    if not !k then begin
      (* Evaluation *)
      print_debug "***** Eval *****\n";
      let env, x, v = Eval.LS1.eval_program env f ~debug:!debug
      in print "%a : %a = %a\n"
        pp_print_string x
        Pp.pp_ty2 u
        Pp.LS1.pp_value2 v;
      (env, kfunenvs, kenv)
    end
    else begin
      (* k-Normalization *)
      print_debug "***** k-Normalization *****\n";
      let kf, kfunenvs = KNormal.kNorm_funs kfunenvs f ~debug:!debug in
      print_debug "kf: %a\n" Pp.KNorm.pp_program kf;
      (* Evaluation on kNormalized term *)
      print_debug "***** Eval *****\n";
      let kenv, kx, kv = Eval.KNorm.eval_program kenv kf ~debug:!debug in
      print_debug "k-Normal :: ";
      print_debug "%a : %a = %a\n"
        pp_print_string kx
        Pp.pp_ty2 u
        Pp.KNorm.pp_value2 kv;
      (env, kfunenvs, kenv)
    end in
    read_eval_print lexbuf env new_tyenv kfunenvs kenv 
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
  | Syntax.LS1.Blame (r, p) | Syntax.KNorm.KBlame (r, p) -> 
    begin match p with
    | Pos -> print "Blame on the expression side:\n%a\n" Utils.Error.pp_range r
    | Neg -> print "Blame on the environment side:\n%a\n" Utils.Error.pp_range r
    end
  end;
  read_eval_print lexbuf env tyenv kfunenvs kenv

let compile_process progs tyenv kfunenvs = 
  (* Used in debug mode *)
  let print_debug f = Utils.Format.make_print_debug !debug f in
  let rec to_exp ps = match ps with
    | Syntax.ITGL.Exp e :: [] -> e
    | Syntax.ITGL.LetDecl (x, e) :: [] -> Syntax.ITGL.LetExp (Syntax.ITGL.range_of_exp e, x, e, UConst Utils.Error.dummy_range)
    | Syntax.ITGL.LetDecl (x, e) :: t -> Syntax.ITGL.LetExp (Syntax.ITGL.range_of_exp e, x, e, to_exp t)
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
    print_debug "***** Coercion-insertion *****\n";
    let _, f, u' = Translate.ITGL.translate tyenv e in
    print_debug "f: %a\n" Pp.LS.pp_program f;
    print_debug "U: %a\n" Pp.pp_ty u';
    assert (Typing.is_equal u u');
    let u'' = Typing.LS.type_of_program tyenv f in
    assert (Typing.is_equal u u'');

    print_debug "***** CPS-translation *****\n";
    let f = Translate.LS.translate tyenv f in
    print_debug "f: %a\n" Pp.LS1.pp_program f;

    (* k-Normalization *)
    print_debug "***** kNormalization *****\n";
    let kf, _ = KNormal.kNorm_funs kfunenvs f ~debug:!debug in
    print_debug "kf: %a\n" Pp.KNorm.pp_program kf;

    let p = match kf with Syntax.KNorm.Exp e -> e | _ -> raise @@ Compile_bad "kf is not exp" in

    print_debug "***** Closure *****\n";
    let p = Closure.toCls_program p !alt in
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

let rec read_compile lexbuf tyenv kfunenvs =
  (* Used in all modes *)
  let print f = fprintf std_formatter f in
  (* Used in debug mode *)
  let print_debug f = Utils.Format.make_print_debug !debug f in
  flush stderr;
  flush stdout;
  if lexbuf.Lexing.lex_curr_p.pos_fname = "" then print "# @?";
  begin try
    let e = Parser.toplevel Lexer.main lexbuf in
    print_debug "***** Parser *****\n";
    print_debug "e: %a\n" Pp.ITGL.pp_program e;
    programs := e :: !programs;

    match e, !opt_file with
    | Syntax.ITGL.Exp _, None -> 
      let c_code = compile_process !programs tyenv kfunenvs in
      programs := [];
      flush stderr;
      let oc = open_out "result_C/stdout.c" in
      Printf.fprintf oc "%s" c_code;
      close_out oc;
      let _ = Sys.command "gcc result_C/stdout.c lib/cast.c lib/stdlib.c -I/mnt/c/gc/include /mnt/c/gc/lib/libgc.so -o result/stdout.out -O2 -g3" in
      let _ = Sys.command "result/stdout.out" in
      print_debug "\n";
      read_compile lexbuf tyenv kfunenvs
    | Syntax.ITGL.Exp _, Some f -> 
      let c_code = compile_process !programs tyenv kfunenvs in
      programs := [];
      flush stderr;
      let oc = open_out ("../result_C/"^f^"_out.c") in
      Printf.fprintf oc "%s" c_code;
      close_out oc;
      let _ = Sys.command ("gcc ../result_C/"^f^"_out.c ../lib/cast.c lib/stdlib.c -I/mnt/c/gc/include /mnt/c/gc/lib/libgc.so -o ../result/"^f^".out -O2") in
      let _ = Sys.command ("../result/"^f^".out") in
      ()
    | _, None -> read_compile lexbuf tyenv kfunenvs
    | _, Some f ->
      begin try 
        read_compile lexbuf tyenv kfunenvs
      with
      | Lexer.Eof ->
        if !programs <> [] then
          let c_code = compile_process !programs tyenv kfunenvs in
          flush stderr;
          programs := [];
          let oc = open_out ("../result/"^f^"_out.c") in
          Printf.fprintf oc "%s" c_code;
          close_out oc;
        else 
          raise Lexer.Eof
      end
  with
  | Failure message ->
    fprintf err_formatter "Failure: %s\n" message;
    flush stderr;
    Utils.Lexing.flush_input lexbuf;
  | Parser.Error -> (* Menhir *)
    let token = Lexing.lexeme lexbuf in
    fprintf err_formatter "Parser.Error: unexpected token %s\n" token;
    flush stderr;
    Utils.Lexing.flush_input lexbuf;
  | Typing.Type_error message ->
    fprintf err_formatter "Type_error: %s\n" message;
    flush stderr;
  | ToC.ToC_error message ->
    fprintf err_formatter "%s\n" message;
    flush stderr;
  end;
  read_compile lexbuf tyenv kfunenvs

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
  let env, tyenv, kfunenvs, kenv = Stdlib.pervasives !alt !debug !compile in
  try
    if !compile then
      read_compile lexbuf tyenv kfunenvs
    else 
      read_eval_print lexbuf env tyenv kfunenvs kenv
  with
    | Lexer.Eof ->
      (* Exiting normally *)
      (* print_debug "end of file!\n"; *)
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
      ("-k", Arg.Set k, " Evaluate on k-Normal form");
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
