open Format
open Lambda_S1_dti

exception Compile_bad of string
exception Invalid_option of string

let intoB = ref false
let debug = ref false
let k = ref false
let alt = ref false
let compile = ref false

let programs = ref []

let opt_file = ref None

let print f = fprintf std_formatter f
let print_debug f = Utils.Format.make_print_debug !debug f

let parse_print lexbuf = 
  let e = Parser.toplevel Lexer.main lexbuf in
  (* NOTE: Lexer.Eof arises here, and text below will not shown *)
  print_debug "***** Parser *****\n";
  print_debug "e: %a\n" Pp.ITGL.pp_program e;
  e

let typing_ITGL_print tyenv e =
  print_debug "***** Typing *****\n";
  let e, u = Typing.ITGL.type_of_program tyenv e in
  print_debug "e: %a\n" Pp.ITGL.pp_program e;
  print_debug "U: %a\n" Pp.pp_ty u;
  e, u

let translation_LB_print tyenv e = 
  print_debug "***** Cast-insertion *****\n";
  let new_tyenv, f, u' = Translate.ITGL.translate ~intoB:true tyenv e in 
  (* NOTE: new_tyenv include current LetDecl type, so type check and translation must be executed in old tyenv *)
  print_debug "f: %a\n" Pp.CC.pp_program f;
  print_debug "U: %a\n" Pp.pp_ty u';
  new_tyenv, f, u'

let translation_LS_print tyenv e =
  print_debug "***** Coercion-insertion *****\n";
  let new_tyenv, f, u' = Translate.ITGL.translate ~intoB:false tyenv e in 
  (* NOTE: new_tyenv include current LetDecl type, so type check and translation must be executed in old tyenv *)
  print_debug "f: %a\n" Pp.CC.pp_program f;
  print_debug "U: %a\n" Pp.pp_ty u';
  new_tyenv, f, u'

let translation_LS1_print ~alt tyenv f =
  print_debug "***** CPS-translation *****\n";
  let f(*, u'''*) =                                  (* TODO: tlanslation into LS1 should return type u'''? *)
    if alt then Translate.CC.translate_alt tyenv f
    else Translate.CC.translate tyenv f 
  in print_debug "f: %a\n" Pp.LS1.pp_program f;
  f(*, u'''*) 

let kNormal_LB_print (tvsenv, alphaenv, betaenv) f = 
  print_debug "***** k-Normalization *****\n";
  let f, alphaenv = KNormal.CC.alpha_program alphaenv f in
  print_debug "alpha: %a\n" Pp.CC.pp_program f;
  let f, tvsenv = KNormal.CC.k_normalize_program tvsenv f in
  print_debug "k_normalize: %a\n" Pp.KNorm.pp_program f;
  let rec iter betaenv f =
    let fbeta, betaenv = KNormal.KNorm.beta_program betaenv f in
    let fassoc = KNormal.KNorm.assoc_program fbeta in
    if f = fassoc then f, (tvsenv, alphaenv, betaenv)
    else 
      (print_debug "beta: %a\n" Pp.KNorm.pp_program fbeta;
      print_debug "assoc: %a\n" Pp.KNorm.pp_program fassoc;
      iter betaenv fassoc)
  in let kf, kfunenvs = iter betaenv f in
  print_debug "kf: %a\n" Pp.KNorm.pp_program kf;
  kf, kfunenvs
  
let kNormal_LS_print (tvsenv, alphaenv, betaenv) f = 
  print_debug "***** k-Normalization *****\n";
  let f, alphaenv = KNormal.LS1.alpha_program alphaenv f in
  print_debug "alpha: %a\n" Pp.LS1.pp_program f;
  let f, tvsenv = KNormal.LS1.k_normalize_program tvsenv f in
  print_debug "k_normalize: %a\n" Pp.KNorm.pp_program f;
  let rec iter betaenv f =
    let fbeta, betaenv = KNormal.KNorm.beta_program betaenv f in
    let fassoc = KNormal.KNorm.assoc_program fbeta in
    if f = fassoc then f, (tvsenv, alphaenv, betaenv)
    else 
      (print_debug "beta: %a\n" Pp.KNorm.pp_program fbeta;
      print_debug "assoc: %a\n" Pp.KNorm.pp_program fassoc;
      iter betaenv fassoc)
  in let kf, kfunenvs = iter betaenv f in
  print_debug "kf: %a\n" Pp.KNorm.pp_program kf;
  kf, kfunenvs

let eval_LB_print env f u =
  print_debug "***** Eval *****\n";
  let env, x, v = Eval.CC.eval_program env f ~debug:!debug in 
  print "%a : %a = %a\n"
    pp_print_string x
    Pp.pp_ty2 u
    Pp.CC.pp_value2 v;
  env 

let eval_LS_print env f u =
  print_debug "***** Eval *****\n";
  let env, x, v = Eval.LS1.eval_program env f ~debug:!debug in 
  print "%a : %a = %a\n"
    pp_print_string x
    Pp.pp_ty2 u
    Pp.LS1.pp_value2 v;
  env 

let keval_print kenv kf u =
  print_debug "***** k-Eval *****\n";
  let kenv, kx, kv = Eval.KNorm.eval_program kenv kf ~debug:!debug in
  print_debug "k-Normal :: ";
  print "%a : %a = %a\n"
    pp_print_string kx
    Pp.pp_ty2 u
    Pp.KNorm.pp_value2 kv;
  kenv

let closure_print ~alt kf venv = 
  print_debug "***** Closure *****\n";
  let p = Closure.toCls_program kf venv ~alt:alt in
  print_debug "%a\n" Pp.Cls.pp_program p;
  p

let toC_print ~alt ~intoB p = 
  print_debug "***** toC *****\n";
  let toC_program = ToC.toC_program ~alt:alt ~intoB:intoB ~bench:0 in
  let c_code = asprintf "%a" toC_program p in
  print_debug "%s\n" c_code;
  c_code

let rec read_eval_print_LB lexbuf env tyenv kfunenvs kenv =
  flush stderr;
  flush stdout;
  if lexbuf.Lexing.lex_curr_p.pos_fname = "" then print "# @?";
  begin try
    (* Parsing *)
    let e = parse_print lexbuf in
    (* Type inference *)
    let e, u = typing_ITGL_print tyenv e in
    (* NOTE: Typing.ITGL.translate and Typing.CC.type_of_program expect normalized input *)
    let tyenv, e, u = Typing.ITGL.normalize tyenv e u in
    (* Coercion-insertion *)
    let new_tyenv, f, u' = translation_LB_print tyenv e in
    assert (Typing.is_equal u u');
    let u'' = Typing.CC.type_of_program tyenv f in
    assert (Typing.is_equal u u'');
    let env, kfunenvs, kenv = 
    if not !k then
      (* Evaluation *)
      let env = eval_LB_print env f u in
      env, kfunenvs, kenv
    else
      (* k-Normalization *)
      let kf, kfunenvs = kNormal_LB_print kfunenvs f in
      (* Evaluation on kNormalized term *)
      let kenv = keval_print kenv kf u in
      env, kfunenvs, kenv
    in
    read_eval_print_LB lexbuf env new_tyenv kfunenvs kenv 
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
  | Syntax.Blame (r, p) -> 
    begin match p with
    | Pos -> print "Blame on the expression side:\n%a\n" Utils.Error.pp_range r
    | Neg -> print "Blame on the environment side:\n%a\n" Utils.Error.pp_range r
    end
  end;
  read_eval_print_LB lexbuf env tyenv kfunenvs kenv

let rec read_eval_print_LS lexbuf env tyenv kfunenvs kenv =
  flush stderr;
  flush stdout;
  if lexbuf.Lexing.lex_curr_p.pos_fname = "" then print "# @?";
  begin try
    (* Parsing *)
    let e = parse_print lexbuf in
    (* Type inference *)
    let e, u = typing_ITGL_print tyenv e in
    (* NOTE: Typing.ITGL.translate and Typing.CC.type_of_program expect normalized input *)
    let tyenv, e, u = Typing.ITGL.normalize tyenv e u in
    (* Coercion-insertion *)
    let new_tyenv, f, u' = translation_LS_print tyenv e in
    assert (Typing.is_equal u u');
    let u'' = Typing.CC.type_of_program tyenv f in
    assert (Typing.is_equal u u'');
    (* CPS-Translation *)
    let f(*, u'''*) = translation_LS1_print ~alt:!alt tyenv f in
    (* assert (Typing.is_equal u u'''); *)
    let env, kfunenvs, kenv = 
    if not !k then
      (* Evaluation *)
      let env = eval_LS_print env f u in
      env, kfunenvs, kenv
    else
      (* k-Normalization *)
      let kf, kfunenvs = kNormal_LS_print kfunenvs f in
      (* Evaluation on kNormalized term *)
      let kenv = keval_print kenv kf u in
      env, kfunenvs, kenv
    in
    read_eval_print_LS lexbuf env new_tyenv kfunenvs kenv 
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
  | Syntax.Blame (r, p) -> 
    begin match p with
    | Pos -> print "Blame on the expression side:\n%a\n" Utils.Error.pp_range r
    | Neg -> print "Blame on the environment side:\n%a\n" Utils.Error.pp_range r
    end
  end;
  read_eval_print_LS lexbuf env tyenv kfunenvs kenv

let compile_process progs tyenv kfunenvs = 
  let rec to_exp ps = match ps with
    | Syntax.ITGL.Exp e :: [] -> e
    | Syntax.ITGL.LetDecl (x, e) :: [] -> Syntax.ITGL.LetExp (Syntax.ITGL.range_of_exp e, x, e, UConst Utils.Error.dummy_range)
    | Syntax.ITGL.LetDecl (x, e) :: t -> Syntax.ITGL.LetExp (Syntax.ITGL.range_of_exp e, x, e, to_exp t)
    | _ -> raise @@ Compile_bad "exp appear in not only last"
  in let e = Syntax.ITGL.Exp (to_exp (List.rev progs)) in
  programs := [];
  begin try
    print_debug "========== Compilation ==========\n";
    (* Type inference *)
    let e, u = typing_ITGL_print tyenv e in
    (* NOTE: Typing.ITGL.translate and Typing.CC.type_of_program expect
     * normalized input *)
    let tyenv, e, u = Typing.ITGL.normalize tyenv e u in
    let kf, _ = 
      if !intoB then 
        (* Cast-insertion *)
        let _, f, u' = translation_LB_print tyenv e in
        assert (Typing.is_equal u u');
        let u'' = Typing.CC.type_of_program tyenv f in
        assert (Typing.is_equal u u'');
        (* k-Normalization *)
        kNormal_LB_print kfunenvs f
      else 
        (* Coercion-insertion *)
        let _, f, u' = translation_LS_print tyenv e in
        assert (Typing.is_equal u u');
        let u'' = Typing.CC.type_of_program tyenv f in
        assert (Typing.is_equal u u'');
        (* CPS-translation *)
        (* NOTE: when generating C, alternative translation is done in closure conversion *)
        let f = translation_LS1_print ~alt:false tyenv f in
        (* k-Normalization *)
        kNormal_LS_print kfunenvs f
    in
    (* Closure-conversion *)
    let p = closure_print ~alt:!alt kf Stdlib.venv in
    let c_code = toC_print ~alt:!alt ~intoB:!intoB p in
    c_code
  with
  | Failure message -> raise @@ Failure message
  | Typing.Type_error message -> raise @@ Typing.Type_error message
  end

let rec read_compile lexbuf tyenv kfunenvs =
  flush stderr;
  flush stdout;
  if lexbuf.Lexing.lex_curr_p.pos_fname = "" then print "# @?";
  begin try
    let e = parse_print lexbuf in
    programs := e :: !programs;
    match e, !opt_file with
    | Syntax.ITGL.Exp _, None -> 
      let c_code = compile_process !programs tyenv kfunenvs in
      flush stderr;
      let oc = open_out "result_C/stdout.c" in
      Printf.fprintf oc "%s" c_code;
      close_out oc;
      let _ = 
        Sys.command @@ 
        Format.asprintf "gcc result_C/stdout.c libC/%s.c %slibC/stdlib%s.c -I/mnt/c/gc/include /mnt/c/gc/lib/libgc.so -o result/stdout.out -g3" (* TODO: -O2 *) 
          (if !intoB then "cast" else "coerce")
          (if !intoB then "" else if !alt then "libC/coerceA.c " else "libC/coerceS.c ")
          (if !intoB then "B" else if !alt then "A" else "S")
      in
      let _ = Sys.command "result/stdout.out" in
      print_debug "\n";
      read_compile lexbuf tyenv kfunenvs
    | Syntax.ITGL.Exp _, Some f -> 
      let c_code = compile_process !programs tyenv kfunenvs in
      flush stderr;
      let oc = open_out ("../result_C/"^f^"_out.c") in
      Printf.fprintf oc "%s" c_code;
      close_out oc;
      let _ = 
        Sys.command @@
        Format.asprintf "gcc ../result_C/%s_out.c ../libC/%s.c %s../libC/stdlib%s.c -I/mnt/c/gc/include /mnt/c/gc/lib/libgc.so -o ../result/%s.out -O2" 
          f
          (if !intoB then "cast" else "coerce")
          (if !intoB then "" else if !alt then "../libC/coerceA.c " else "../libC/coerceS.c ")
          (if !intoB then "B" else if !alt then "A" else "S")
          f
      in
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
  try
    if !intoB then 
      let env, tyenv, kfunenvs, kenv = Stdlib.pervasives_LB ~debug:!debug ~compile:!compile in
      if !compile then read_compile lexbuf tyenv kfunenvs
      else read_eval_print_LB lexbuf env tyenv kfunenvs kenv
    else 
      let env, tyenv, kfunenvs, kenv = Stdlib.pervasives_LS ~alt:!alt ~debug:!debug ~compile:!compile in
      if !compile then read_compile lexbuf tyenv kfunenvs
      else read_eval_print_LS lexbuf env tyenv kfunenvs kenv
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
      ("-b", Arg.Set intoB, " tramslate into LB");
    ]
  in
  let parse_argv arg = match !file with
  | None -> file := Some arg
  | Some _ -> raise @@ Arg.Bad "error: only one file can be specified"
  in
  Arg.parse options parse_argv usage;
  start !file