open Format
open Lambda_S1_dti

(* Configuration *)
type config_t = {
  mutable debug : bool;
  mutable k_norm : bool;
  mutable alt : bool;
  mutable compile : bool;
  mutable into_b : bool;
  (* mutable eager: bool; TODO *)
  mutable opt_file : string option;
}

let config = {
  debug = false;
  k_norm = false;
  alt = false;
  compile = false;
  into_b = false;
  (* eager = false; TODO *)
  opt_file = None;
}

(* exception Invalid_option of string *)

(* Logging & Parsing Helpers *)
let print f = fprintf std_formatter f
let print_debug f = Utils.Format.make_print_debug config.debug f
let print_err f = fprintf err_formatter f

(* Compilation Logic *)
module Compiler = struct
  exception Compile_bad of string

  let bundle_programs progs =
    let rec to_exp ps = match ps with
      | Syntax.ITGL.Exp e :: [] -> e
      | Syntax.ITGL.LetDecl (x, e) :: [] -> 
          Syntax.ITGL.LetExp (Syntax.ITGL.range_of_exp e, x, e, UConst Utils.Error.dummy_range)
      | Syntax.ITGL.LetDecl (x, e) :: t -> 
          Syntax.ITGL.LetExp (Syntax.ITGL.range_of_exp e, x, e, to_exp t)
      | _ -> raise @@ Compile_bad "exp must appear only at the last position"
    in 
    Syntax.ITGL.Exp (to_exp (List.rev progs))

  (* GCCコマンド生成 *)
  let build_cmd_for_stdin () =
    let intoB = config.into_b in
    let alt = config.alt in
    match config.opt_file with
    | Some filename -> 
      asprintf "gcc ../result_C/%s_out.c %s%s../libC/*.c -o ../result/%s.out -lgc -g3 -O2"
        filename
        (if intoB then "-D CAST " else "")
        (if alt then "-D ALT " else "")
        filename
    | None -> 
      asprintf "gcc result_C/stdin.c %s%slibC/*.c -o result/stdin.out -lgc -g3" (* TODO: -O2 *)
        (if intoB then "-D CAST " else "")
        (if alt then "-D ALT " else "")
end

(* Pipeline Stages *)
module Pipeline = struct
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

  let translation_CC_print tyenv e = 
    print_debug "***** %s *****\n" (if config.into_b then "Cast-insertion" else "Coercion-insertion");
    let new_tyenv, f, u' = Translate.ITGL.translate ~intoB:config.into_b tyenv e in 
    (* NOTE: new_tyenv include current LetDecl type, so type check and translation must be executed in old tyenv *)
    print_debug "f: %a\n" Pp.CC.pp_program f;
    print_debug "U: %a\n" Pp.pp_ty u';
    new_tyenv, f, u'

  let translation_LS1_print ~alt tyenv f =
    print_debug "***** CPS-translation *****\n";
    let f(*, u'''*) = (* TODO: tlanslation into LS1 should return type u'''? *)
      if alt then Translate.CC.translate_alt tyenv f
      else Translate.CC.translate tyenv f 
    in print_debug "f: %a\n" Pp.LS1.pp_program f;
    f(*, u'''*) 

  let kNorm_funs_print (tvsenv, alphaenv, betaenv) f ~alpha_fn ~norm_fn ~pp = 
    print_debug "***** k-Normalization *****\n";
    let f, alphaenv = alpha_fn alphaenv f in
    print_debug "alpha: %a\n" pp f;
    let f, tvsenv = norm_fn tvsenv f in
    print_debug "k_normalize: %a\n" Pp.KNorm.pp_program f;
    let rec iter betaenv f =
      let fbeta, betaenv = KNormal.KNorm.beta_program betaenv f in
      let fassoc = KNormal.KNorm.assoc_program fbeta in
      if f = fassoc then f, (tvsenv, alphaenv, betaenv)
      else 
        (print_debug "beta: %a\n" Pp.KNorm.pp_program fbeta;
         print_debug "assoc: %a\n" Pp.KNorm.pp_program fassoc;
         iter betaenv fassoc)
    in
    let kf, kfunenvs = iter betaenv f in
    print_debug "kf: %a\n" Pp.KNorm.pp_program kf;
    kf, kfunenvs

  let kNormal_LB_print envs f = 
    kNorm_funs_print envs f
      ~alpha_fn:KNormal.CC.alpha_program
      ~norm_fn:KNormal.CC.k_normalize_program
      ~pp:Pp.CC.pp_program

  let kNormal_LS_print envs f = 
    kNorm_funs_print envs f
      ~alpha_fn:KNormal.LS1.alpha_program
      ~norm_fn:KNormal.LS1.k_normalize_program
      ~pp:Pp.LS1.pp_program

  let eval_print env f u ~eval_fn ~pp_val =
    print_debug "***** Eval *****\n";
    let env, x, v = eval_fn env f in 
    print "%a : %a = %a\n"
      pp_print_string x
      Pp.pp_ty2 u
      pp_val v;
    env 

  let eval_LB_print env f u =
    eval_print env f u
      ~eval_fn:(Eval.CC.eval_program ~debug:config.debug)
      ~pp_val:Pp.CC.pp_value2

  let eval_LS_print env f u =
    eval_print env f u
      ~eval_fn:(Eval.LS1.eval_program ~debug:config.debug)
      ~pp_val:Pp.LS1.pp_value2

  let keval_print kenv kf u =
    print_debug "***** k-Eval *****\n";
    let kenv, kx, kv = Eval.KNorm.eval_program kenv kf ~debug:config.debug in
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
end

(* Core Logic *)
let rec read_eval_print lexbuf env tyenv kfunenvs kenv 
  ~eval_fn ~translation_fn ~kNormal_fn =
  let read_eval_print = read_eval_print ~eval_fn:eval_fn ~translation_fn:translation_fn ~kNormal_fn:kNormal_fn in
  flush stderr;
  flush stdout;
  if lexbuf.Lexing.lex_curr_p.pos_fname = "" then print "# @?";
  begin try
    (* Parsing *)
    let e = Pipeline.parse_print lexbuf in
    (* Type inference *)
    let e, u = Pipeline.typing_ITGL_print tyenv e in
    (* NOTE: Typing.ITGL.translate and Typing.CC.type_of_program expect normalized input *)
    let tyenv, e, u = Typing.ITGL.normalize tyenv e u in
    (* Coercion- / Cast-insertion *)
    let new_tyenv, f, u' = Pipeline.translation_CC_print tyenv e in
    assert (Typing.is_equal u u');
    let u'' = Typing.CC.type_of_program tyenv f in
    assert (Typing.is_equal u u'');
    (* CPS-Translation when config.into_b is false *)
    let f(*, u'''*) = translation_fn tyenv f in
    (* assert (Typing.is_equal u u'''); *)
    let env, kfunenvs, kenv = 
    if not config.k_norm then
      (* Evaluation *)
      let env = eval_fn env f u in
      env, kfunenvs, kenv
    else
      (* k-Normalization *)
      let kf, kfunenvs = kNormal_fn kfunenvs f in
      (* Evaluation on kNormalized term *)
      let kenv = Pipeline.keval_print kenv kf u in
      env, kfunenvs, kenv
    in
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
  | Syntax.Blame (r, p) -> 
    begin match p with
    | Pos -> print "Blame on the expression side:\n%a\n" Utils.Error.pp_range r
    | Neg -> print "Blame on the environment side:\n%a\n" Utils.Error.pp_range r
    end
  end;
  read_eval_print lexbuf env tyenv kfunenvs kenv 

let read_eval_print_LB lexbuf env tyenv kfunenvs kenv =
  read_eval_print lexbuf env tyenv kfunenvs kenv 
    ~eval_fn: Pipeline.eval_LB_print
    ~translation_fn: (fun _ f -> f)
    ~kNormal_fn: Pipeline.kNormal_LB_print
  
let read_eval_print_LS lexbuf env tyenv kfunenvs kenv =
  read_eval_print lexbuf env tyenv kfunenvs kenv 
    ~eval_fn: Pipeline.eval_LS_print
    ~translation_fn: (Pipeline.translation_LS1_print ~alt:config.alt)
    ~kNormal_fn: Pipeline.kNormal_LS_print

let gen_c_code programs tyenv kfunenvs = 
  let e = Compiler.bundle_programs programs in
  print_debug "========== Compilation ==========\n";
  (* Type inference *)
  let e, u = Pipeline.typing_ITGL_print tyenv e in
  (* NOTE: Typing.ITGL.translate and Typing.CC.type_of_program expect normalized input *)
  let tyenv, e, u = Typing.ITGL.normalize tyenv e u in
  (* Coercion- / Cast-insertion *)
  let _, f, u' = Pipeline.translation_CC_print tyenv e in
  assert (Typing.is_equal u u');
  let u'' = Typing.CC.type_of_program tyenv f in
  assert (Typing.is_equal u u'');
  let kf, _ = 
    if config.into_b then 
      (* k-Normalization *)
      Pipeline.kNormal_LB_print kfunenvs f
    else 
      (* CPS-translation *)
      (* NOTE: when generating C, alternative translation is done in closure conversion *)
      let f = Pipeline.translation_LS1_print ~alt:false tyenv f in
      (* k-Normalization *)
      Pipeline.kNormal_LS_print kfunenvs f
  in
  (* Closure-conversion *)
  let p = Pipeline.closure_print ~alt:config.alt kf Stdlib.venv in
  let c_code = Pipeline.toC_print ~alt:config.alt ~intoB:config.into_b p in
  c_code

let handle_compile_output c_code = match config.opt_file with
| Some filename ->
  (* ファイル入力モード *)
  let out_path = "../result_C/" ^ filename ^ "_out.c" in
  let oc = open_out out_path in
  Printf.fprintf oc "%s" c_code;
  close_out oc;
  (* print_debug "Generated C file: %s (Execution delegated)\n" out_path *)
  let _ = Sys.command (Compiler.build_cmd_for_stdin ()) in
  let _ = Sys.command ("../result/" ^ filename ^ ".out") in
  ()
| None ->
  (* 標準入力モード *)
  flush stderr;
  let out_path = "result_C/stdin.c" in
  let oc = open_out out_path in
  Printf.fprintf oc "%s" c_code;
  close_out oc;
  (* print_debug "%s" (Compiler.build_cmd_for_stdin ()); *)
  let _ = Sys.command (Compiler.build_cmd_for_stdin ()) in
  let _ = Sys.command "result/stdin.out" in
  ()

let rec read_compile lexbuf tyenv kfunenvs programs =
  flush stderr;
  flush stdout;
  if lexbuf.Lexing.lex_curr_p.pos_fname = "" then print "# @?";
  begin try
    let e = Pipeline.parse_print lexbuf in
    let programs = e :: programs in
    match e with
    | Syntax.ITGL.Exp _ -> 
      let c_code = gen_c_code programs tyenv kfunenvs in
      handle_compile_output c_code;
      print_debug "\n";
      read_compile lexbuf tyenv kfunenvs []
      (* TODO: ファイルモードのとき，プログラムがきちんと書れていなくてもコンパイルが通ることがある ex.bad.ml *)
    | _ -> read_compile lexbuf tyenv kfunenvs programs
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
  read_compile lexbuf tyenv kfunenvs programs

let start file =
  config.opt_file <- file;
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
    if config.into_b then 
      let env, tyenv, kfunenvs, kenv = Stdlib.pervasives_LB ~debug:config.debug ~compile:config.compile in
      if config.compile then read_compile lexbuf tyenv kfunenvs []
      else read_eval_print_LB lexbuf env tyenv kfunenvs kenv
    else 
      let env, tyenv, kfunenvs, kenv = Stdlib.pervasives_LS ~alt:config.alt ~debug:config.debug ~compile:config.compile in
      if config.compile then read_compile lexbuf tyenv kfunenvs []
      else read_eval_print_LS lexbuf env tyenv kfunenvs kenv
  with
    | Lexer.Eof ->
      (* Exiting normally *)
      (* print_debug "end of file\n"; *)
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
      ("-d", Arg.Unit (fun () -> config.debug <- true), " Enable debug mode");
      ("-k", Arg.Unit (fun () -> config.k_norm <- true), " Evaluate on k-Normal form");
      ("-a", Arg.Unit (fun () -> config.alt <- true), " Use alternative translation");
      ("-c", Arg.Unit (fun () -> config.compile <- true), " Compile the program to C code");
      ("-b", Arg.Unit (fun () -> config.into_b <- true), " tramslate into LB");
    ]
  in
  let parse_argv arg = match !file with
  | None -> file := Some arg
  | Some _ -> raise @@ Arg.Bad "error: only one file can be specified"
  in
  Arg.parse options parse_argv usage;
  start !file

(* let safe_execute lexbuf fn =
  try
    fn ()
  with
  | Failure message ->
      print_err "Failure: %s\n" message;
      Utils.Lexing.flush_input lexbuf
  | Parser.Error ->
      let token = Lexing.lexeme lexbuf in
      print_err "Parser.Error: unexpected token %s\n" token;
      Utils.Lexing.flush_input lexbuf
  | Typing.Type_error message ->
      print_err "Type_error: %s\n" message
  | Syntax.Blame (r, p) ->
      begin match p with
      | Pos -> print "Blame on the expression side:\n%a\n" Utils.Error.pp_range r
      | Neg -> print "Blame on the environment side:\n%a\n" Utils.Error.pp_range r
      end
  | ToC.ToC_error message ->
      print_err "ToC Error: %s\n" message *)

(* REPL / Main Loop *)
(* let rec loop config lexbuf env tyenv kfunenvs kenv acc_progs =
  flush stderr; flush stdout;
  if lexbuf.Lexing.lex_curr_p.pos_fname = "" then print "# @?";
  
  try
    let e = parse_print config lexbuf in
    
    if config.compile then
      (* Compile Mode *)
      match e with
      | Syntax.ITGL.Exp _ ->
          (* プログラム単位の終わり: 蓄積した定義を含めてコンパイル処理へ *)
          safe_execute lexbuf (fun () ->
            let new_progs = e :: acc_progs in
            let c_code = gen_c_code config tyenv kfunenvs new_progs in
            handle_compile_output config c_code;
            print_debug config "\n"
          );
          (* コンパイル後はアキュムレータをリセット *)
          loop config lexbuf env tyenv kfunenvs kenv []
      | _ -> 
          (* 定義: 蓄積する *)
          loop config lexbuf env tyenv kfunenvs kenv (e :: acc_progs)
    else
      (* Interpret Mode *)
      safe_execute lexbuf (fun () ->
        let e, u = typing_ITGL_print config tyenv e in
        let tyenv, e, u = Typing.ITGL.normalize tyenv e u in
        
        if config.into_b then
          let new_tyenv, f, u' = Pipeline.translation_LB config tyenv e in
          assert (Typing.is_equal u u');
          let _ = Typing.CC.type_of_program tyenv f in 
          
          if not config.k_norm then
            let env = Pipeline.eval_LB config env f u in
            loop config lexbuf env new_tyenv kfunenvs kenv []
          else
            let kf, kfunenvs = Pipeline.kNormal_LB config kfunenvs f in
            let kenv = Pipeline.keval config kenv kf u in
            loop config lexbuf env new_tyenv kfunenvs kenv []
        else
          let new_tyenv, f, u' = Pipeline.translation_LS config tyenv e in
          assert (Typing.is_equal u u');
          let _ = Typing.CC.type_of_program tyenv f in
          let f = Pipeline.translation_LS1 config ~alt:config.alt tyenv f in
          
          if not config.k_norm then
            let env = Pipeline.eval_LS config env f u in
            loop config lexbuf env new_tyenv kfunenvs kenv []
          else
            let kf, kfunenvs = Pipeline.kNormal_LS config kfunenvs f in
            let kenv = Pipeline.keval config kenv kf u in
            loop config lexbuf env new_tyenv kfunenvs kenv []
      )
  with
  | Lexer.Eof ->
      (* EOF到達時の処理 *)
      (* ファイルモードで未コンパイルの蓄積がある場合は出力して終了 *)
      if config.compile && acc_progs <> [] then begin
         match config.opt_file with
         | Some filename ->
             safe_execute lexbuf (fun () ->
               let c_code = gen_c_code config tyenv kfunenvs acc_progs in
               handle_compile_output config c_code
             )
         | None -> 
             (* REPLでのEOFは通常無視または終了だが、未処理バッファがあれば処理可能 *)
             () 
      end;
      () (* Exit loop *)
  | Stdlib.Stdlib_exit i -> exit i
  | e -> raise e

(* --- Entry Point --- *)

let start file =
  default_config.opt_file <- file;
  print_debug default_config "***** Lexer *****\n";
  
  let channel, lexbuf = match file with
  | None ->
      print_debug default_config "Reading from stdin\n%!";
      stdin, Lexing.from_channel stdin
  | Some f ->
      print_debug default_config "Reading from file \"%s\"\n%!" f;
      let channel = open_in f in
      let lexbuf = Lexing.from_channel channel in
      lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = f};
      channel, lexbuf
  in

  try
    let env, tyenv, kfunenvs, kenv = 
      if default_config.into_b then 
        Stdlib.pervasives_LB ~debug:default_config.debug ~compile:default_config.compile 
      else 
        Stdlib.pervasives_LS ~alt:default_config.alt ~debug:default_config.debug ~compile:default_config.compile 
    in
    loop default_config lexbuf env tyenv kfunenvs kenv []
  with
  | e ->
      close_in_noerr channel;
      raise e *)