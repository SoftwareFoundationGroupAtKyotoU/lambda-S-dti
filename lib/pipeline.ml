open Format
open Syntax
open Config

exception Compile_bad of string

(* --- helpers --- *)
let print_title ppf title = 
  fprintf ppf "***** %s *****@." title

let log_section ppf title =
  fprintf ppf "@.@[<v>--- %s ---@]@." title

let bundle_programs progs =
  let rec to_exp ps = match ps with
    | Syntax.CC.Exp e :: [] -> e
    | Syntax.CC.LetDecl (x, e) :: [] -> 
        Syntax.CC.LetExp (x, e, Syntax.CC.UConst)
    | Syntax.CC.LetDecl (x, e) :: t -> 
        Syntax.CC.LetExp (x, e, to_exp t)
    | _ -> raise @@ Compile_bad "exp must appear only at the last position"
  in 
  Syntax.CC.Exp (to_exp (List.rev progs))

type 't state = {
  program : 't;
  ty : ty;
  tyenv : tysc Environment.t;
  env : CC.value Environment.t;
  kfunenvs : tyvar list Environment.t * id Environment.t * id Environment.t;
}

let init_state program ~config =
  let env, tyenv, kfunenvs = Stdlib.pervasives ~config in
  { program; ty = TyVar (-1, { contents = None }); tyenv; env; kfunenvs }

let change_state_program program state =
  {
    program;
    ty = state.ty;
    tyenv = state.tyenv;
    env = state.env;
    kfunenvs = state.kfunenvs;
  }

(* --- public API --- *)
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

let parse ppf lexbuf state = 
  let e = Parser.toplevel Lexer.main lexbuf in
  (* NOTE: Lexer.Eof arises here, and text below will not shown *)
  print_title ppf "Parser";
  fprintf ppf "e: %a@." Pp.ITGL.pp_program e;
  change_state_program e state

let typing_ITGL ppf state =
  print_title ppf "Typing";
  let e, u = Typing.ITGL.type_of_program state.tyenv state.program in
  (* NOTE: Typing.ITGL.translate and Typing.CC.type_of_program expect normalized input *)
  let tyenv, e, u = Normalize.ITGL.normalize state.tyenv e u in
  fprintf ppf "e: %a@.U: %a@." Pp.ITGL.pp_program e Pp.pp_ty u;
  { state with program = e; ty = u; tyenv = tyenv }

let translate_to_CC ppf state ~config ~bench_ppf ~bench = 
  log_section bench_ppf "after Mutate";
  fprintf bench_ppf "%a@." Pp.ITGL.pp_program state.program;
  print_title ppf (if config.intoB then "Cast-insertion" else "Coercion-insertion");
  let new_tyenv, f, u' = Translate.ITGL.translate ~config state.tyenv state.program in
  (* NOTE: new_tyenv include current LetDecl type, so type check and translation must be executed in old tyenv *)
  (* Pp.pp_ty2 Format.err_formatter u'; *)
  assert (Type_utils.is_equal state.ty u');
  let u'' = Typing.CC.type_of_program state.tyenv f in
  assert (Type_utils.is_equal state.ty u'');
  log_section bench_ppf "after Insertion";
  fprintf bench_ppf "%a@." Pp.CC.pp_program f;
  fprintf ppf "f: %a@." Pp.CC.pp_program f;
  let f = 
    if bench = 0 then f
    else Fresh_tv.CC.tv_renew f
  in
  print_title ppf "CPS-translation";
  let f, u''' = Translate.CC.translate ~config state.tyenv f in
  assert (Type_utils.is_equal state.ty u''');
  fprintf ppf "f: %a@." Pp.CC.pp_program f;
  let state = change_state_program f state in
  { state with tyenv = new_tyenv }

let eval ppf state ~config =
  print_title ppf "Eval";
  let env, x, v = Eval.CC.eval_program ~config state.env state.program in 
  { state with env }, x, v

let kNorm_funs ppf state ~config =
  let (tvsenv, alphaenv, betaenv) = state.kfunenvs in
  print_title ppf "k-Normalization";
  let f, alphaenv = KNormal.CC.alpha_program alphaenv state.program in
  fprintf ppf "alpha: %a@." Pp.CC.pp_program f;
  let f, tvsenv = KNormal.CC.k_normalize_program tvsenv f ~static:config.static in
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
  let state = change_state_program kf state in
  { state with kfunenvs = kfunenvs }

let closure ppf state ~config = 
  print_title ppf "Closure";
  let p = Closure.toCls_program state.program Stdlib.venv ~alt:config.alt in
  fprintf ppf "%a@." Pp.Cls.pp_program p;
  change_state_program p state

let toC ppf state ~config ~bench = 
  print_title ppf "toC";
  let c_code = ToC.toC_program ~config ~bench state.program in
  let str_c = asprintf "%a" Pp.C.pp_program c_code in
  fprintf ppf "%s@." str_c;
  str_c