open Format
open Syntax
open Config

exception Compile_bad of string

(* helpers *)
let print_title ppf title = 
  fprintf ppf "***** %s *****@." title

let log_section ppf title =
  fprintf ppf "@.@[<v>--- %s ---@]@." title

let parse ppf lexbuf = 
  let e = Parser.toplevel Lexer.main lexbuf in
  (* NOTE: Lexer.Eof arises here, and text below will not shown *)
  print_title ppf "Parser";
  fprintf ppf "e: %a@." Pp.ITGL.pp_program e;
  e

let typing_ITGL ppf tyenv e =
  print_title ppf "Typing";
  let e, u = Typing.ITGL.type_of_program tyenv e in
  fprintf ppf "e: %a@." Pp.ITGL.pp_program e;
  fprintf ppf "U: %a@." Pp.pp_ty u;
  e, u

let translate_to_CC ppf tyenv e ~config ~bench_ppf = 
  let intoB = config.intoB in
  log_section bench_ppf "after Mutate";
  fprintf bench_ppf "%a@." Pp.ITGL.pp_program e;
  print_title ppf (if intoB then "Cast-insertion" else "Coercion-insertion");
  let new_tyenv, f, u' = Translate.ITGL.translate ~intoB tyenv e in 
  (* NOTE: new_tyenv include current LetDecl type, so type check and translation must be executed in old tyenv *)
  fprintf ppf "f: %a@." Pp.CC.pp_program f;
  fprintf ppf "U: %a@." Pp.pp_ty u';
  log_section bench_ppf "after Insertion";
  fprintf bench_ppf "%a@." Pp.CC.pp_program f;
  new_tyenv, f, u'

let translate_to_LS1 ppf tyenv f ~config =
  print_title ppf "CPS-translation";
  (* TODO: tlanslation into LS1 should return type u'''? *)
  let f(*, u'''*) = 
    (* NOTE: when generating C, alternative translation is done in closure conversion *)
    if config.alt && not config.compile then Translate.CC.translate_alt tyenv f
    else Translate.CC.translate tyenv f 
  in 
  fprintf ppf "f: %a@." Pp.LS1.pp_program f;
  f(*, u'''*) 

let eval ppf env f u ~eval_fn ~pp_val ~res_ppf =
  print_title ppf "Eval";
  let env, x, v = eval_fn env f in 
  fprintf res_ppf "%a : %a = %a@."
    pp_print_string x
    Pp.pp_ty2 u
    pp_val v;
  env 

let eval_LB ppf env f u ~config ~res_ppf =
  let debug = config.debug in
  eval ppf env f u
    ~eval_fn:(Eval.CC.eval_program ~debug)
    ~res_ppf
    ~pp_val:Pp.CC.pp_value2

let eval_LS ppf env f u ~config ~res_ppf =
  let debug = config.debug in
  eval ppf env f u
    ~eval_fn:(Eval.LS1.eval_program ~debug)
    ~res_ppf
    ~pp_val:Pp.LS1.pp_value2

let kNorm_funs ppf (tvsenv, alphaenv, betaenv) f ~alpha_fn ~norm_fn ~pp = 
  print_title ppf "k-Normalization";
  let f, alphaenv = alpha_fn alphaenv f in
  fprintf ppf "alpha: %a@." pp f;
  let f, tvsenv = norm_fn tvsenv f in
  fprintf ppf "k_normalize: %a@." Pp.KNorm.pp_program f;
  let rec iter betaenv f =
    let fbeta, betaenv = KNormal.KNorm.beta_program betaenv f in
    let fassoc = KNormal.KNorm.assoc_program fbeta in
    if f = fassoc then f, (tvsenv, alphaenv, betaenv)
    else 
      (fprintf ppf "beta: %a@." Pp.KNorm.pp_program fbeta;
       fprintf ppf "assoc: %a@." Pp.KNorm.pp_program fassoc;
       iter betaenv fassoc)
  in
  let kf, kfunenvs = iter betaenv f in
  fprintf ppf "kf: %a@." Pp.KNorm.pp_program kf;
  kf, kfunenvs

let kNormal_LB ppf envs f ~config = 
  let static = config.static in
  kNorm_funs ppf envs f
    ~alpha_fn:KNormal.CC.alpha_program
    ~norm_fn:(KNormal.CC.k_normalize_program ~static)
    ~pp:Pp.CC.pp_program

let kNormal_LS ppf envs f = 
  kNorm_funs ppf envs f
    ~alpha_fn:KNormal.LS1.alpha_program
    ~norm_fn:KNormal.LS1.k_normalize_program
    ~pp:Pp.LS1.pp_program

let keval ppf kenv kf u ~config ~res_ppf =
  let debug = config.debug in
  print_title ppf "k-Eval";
  let kenv, kx, kv = Eval.KNorm.eval_program kenv kf ~debug in
  (* print_debug "k-Normal :: "; *)
  fprintf res_ppf "%a : %a = %a@."
    pp_print_string kx
    Pp.pp_ty2 u
    Pp.KNorm.pp_value2 kv;
  kenv

let closure ppf kf venv ~config = 
  let alt = config.alt in
  print_title ppf "Closure";
  let p = Closure.toCls_program kf venv ~alt in
  fprintf ppf "%a@." Pp.Cls.pp_program p;
  p

let toC ppf p ~config ~bench = 
  print_title ppf "toC";
  let toC_program = ToC.toC_program ~config ~bench in
  let c_code = asprintf "%a" toC_program p in
  fprintf ppf "%s@." c_code;
  c_code

(* 公開API *)
let lex ppf file =
  print_title ppf "Lexer";
  match file with
  | None ->
    fprintf ppf "Reading from stdin@.";
    stdin, Lexing.from_channel stdin
  | Some f ->
    fprintf ppf "Reading from file \"%s\"@." f;
    let channel = open_in f in
    let lexbuf = Lexing.from_channel channel in
    lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = f};
    channel, lexbuf

let parse_cc ppf lexbuf tyenv ~config =
  (* Parsing *)
  let e = parse ppf lexbuf in
  (* Type inference *)
  let e, u = typing_ITGL ppf tyenv e in
  (* NOTE: Typing.ITGL.translate and Typing.CC.type_of_program expect normalized input *)
  let tyenv, e, u = Typing.ITGL.normalize tyenv e u in
  (* Coercion- / Cast-insertion *)
  let new_tyenv, f, u' = translate_to_CC ppf tyenv e ~config ~bench_ppf:Utils.Format.empty_formatter in
  assert (Typing.is_equal u u');
  let u'' = Typing.CC.type_of_program tyenv f in
  assert (Typing.is_equal u u'');
  new_tyenv, f, u 

let rec read_eval ppf lexbuf env tyenv kfunenvs kenv 
  ~config ~res_ppf
  ~translation_fn ~eval_fn ~kNormal_fn =  
  let read_eval = read_eval ~config ~res_ppf ~translation_fn ~eval_fn ~kNormal_fn in
  flush stderr;
  flush stdout;
  if lexbuf.Lexing.lex_curr_p.pos_fname = "" then fprintf std_formatter "# @?";
  begin try 
    let new_tyenv, f, u = parse_cc ppf lexbuf tyenv ~config in
    (* CPS-Translation when intoB is false *)
    let f(*, u'''*) = translation_fn ppf tyenv f in
    (* assert (Typing.is_equal u u'''); *)
    let env, kfunenvs, kenv = 
      if not config.kNorm then
        (* Evaluation *)
        let env = eval_fn ppf env f u in
        env, kfunenvs, kenv
      else
        (* k-Normalization *)
        let kf, kfunenvs = kNormal_fn ppf kfunenvs f in
        (* Evaluation on kNormalized term *)
        let kenv = keval ppf kenv kf u ~config ~res_ppf in
        env, kfunenvs, kenv
    in
    read_eval ppf lexbuf env new_tyenv kfunenvs kenv
  with
  | Parser.Error -> (* Menhir *)
    let token = Lexing.lexeme lexbuf in
    fprintf err_formatter "Parser.Error: unexpected token %s@." token;
    Utils.Lexing.flush_input lexbuf
  | Typing.Type_error message ->
    fprintf err_formatter "Type_error: %s@." message
  | Failure message ->
    fprintf err_formatter "Failure: %s@." message;
    Utils.Lexing.flush_input lexbuf
  | Syntax.Blame (r, p) -> 
    begin match p with
    | Pos -> fprintf err_formatter "Blame on the expression side:\n%a@." Utils.Error.pp_range r
    | Neg -> fprintf err_formatter "Blame on the environment side:\n%a@." Utils.Error.pp_range r
    end
  end;
  read_eval ppf lexbuf env tyenv kfunenvs kenv

let read_eval_LB ppf lexbuf env tyenv kfunenvs kenv ~config ~res_ppf =
  read_eval ppf lexbuf env tyenv kfunenvs kenv ~config ~res_ppf
    ~eval_fn: (eval_LB ~config ~res_ppf)
    ~translation_fn: (fun _ _ f -> f)
    ~kNormal_fn: (kNormal_LB ~config)
  
let read_eval_LS ppf lexbuf env tyenv kfunenvs kenv ~config ~res_ppf =
  read_eval ppf lexbuf env tyenv kfunenvs kenv ~config ~res_ppf
    ~eval_fn: (eval_LS ~config ~res_ppf)
    ~translation_fn: (translate_to_LS1 ~config)
    ~kNormal_fn: kNormal_LS

let cc_compile ppf programs tyenv kfunenvs ~config ~bench_ppf ~bench =
  let bundle_programs progs =
    let rec to_exp ps = match ps with
      | Syntax.CC.Exp e :: [] -> e
      | Syntax.CC.LetDecl (x, tvs, e) :: [] -> 
          Syntax.CC.LetExp (x, tvs, e, Syntax.CC.UConst)
      | Syntax.CC.LetDecl (x, tvs, e) :: t -> 
          Syntax.CC.LetExp (x, tvs, e, to_exp t)
      | _ -> raise @@ Compile_bad "exp must appear only at the last position"
    in 
    Syntax.CC.Exp (to_exp (List.rev progs))
  in
  let f = bundle_programs programs in
  log_section bench_ppf "after Translation";
  fprintf ppf "========== Compilation ==========@.";
  let kf, _ = 
    if config.intoB then 
      (* k-Normalization *)
      let _ = fprintf bench_ppf "%a@." Pp.CC.pp_program f in
      kNormal_LB ppf kfunenvs f ~config
    else 
      (* CPS-translation *)
      let f = translate_to_LS1 ppf tyenv f ~config in
      fprintf bench_ppf "%a@." Pp.LS1.pp_program f;
      (* k-Normalization *)
      kNormal_LS ppf kfunenvs f
  in
  (* Closure-conversion *)
  let p = closure ppf kf Stdlib.venv ~config in
  let c_code = toC ppf p ~config ~bench in
  c_code

let compile_for_bench ppf p ~config ~bench_idx ~bench_ppf =
  if config.intoB then 
    let _, tyenv, kfunenvs, _ = Stdlib.pervasives_LB ~config in
    let p, u = Typing.ITGL.type_of_program tyenv p in
    let tyenv, p, _ = Typing.ITGL.normalize tyenv p u in
    let _, decl, _ = translate_to_CC ppf tyenv p ~config ~bench_ppf in
    let c_code = cc_compile ppf [decl] tyenv kfunenvs ~config ~bench_ppf ~bench:bench_idx in
    c_code, decl, tyenv
  else
    let _, tyenv, kfunenvs, _ = Stdlib.pervasives_LS ~config in
    let p, u = Typing.ITGL.type_of_program tyenv p in
    let tyenv, p, _ = Typing.ITGL.normalize tyenv p u in
    let _, decl, _ = translate_to_CC ppf tyenv p ~config ~bench_ppf in
    let c_code = cc_compile ppf [decl] tyenv kfunenvs ~config ~bench_ppf ~bench:bench_idx in
    c_code, decl, tyenv

let rec read_compile ppf lexbuf tyenv kfunenvs opt_file ~config =
  let read_compile = read_compile ~config in
  let initial_tyenv = tyenv in
  let initial_kfunenvs = kfunenvs in 
  let rec loop ppf lexbuf tyenv kfunenvs programs ~config = 
    let loop = loop ~config in
    flush stderr;
    flush stdout;
    if lexbuf.Lexing.lex_curr_p.pos_fname = "" then fprintf std_formatter "# @?";
    begin try
      let new_tyenv, e, _ = parse_cc ppf lexbuf tyenv ~config in
      let programs = e :: programs in
      match e with
      | Syntax.CC.Exp _ -> 
        let c_code = cc_compile ppf programs new_tyenv kfunenvs ~config ~bench_ppf:Utils.Format.empty_formatter ~bench:0 in
        Builder.build_run c_code opt_file ~config;
        fprintf ppf "@.";
        read_compile ppf lexbuf initial_tyenv initial_kfunenvs opt_file
      (* TODO: ファイルモードのとき，プログラムがきちんと書れていなくてもコンパイルが通ることがある (ex: bad.ml) *)
      | _ -> loop ppf lexbuf new_tyenv kfunenvs programs
    with
    | Parser.Error -> (* Menhir *)
      let token = Lexing.lexeme lexbuf in
      fprintf err_formatter "Parser.Error: unexpected token %s@." token;
      Utils.Lexing.flush_input lexbuf
    | Typing.Type_error message ->
      fprintf err_formatter "Type_error: %s@." message
    end;
    loop ppf lexbuf tyenv kfunenvs programs
  in
  loop ppf lexbuf initial_tyenv initial_kfunenvs [] ~config