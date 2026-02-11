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

let build_clang_cmd ?(log_dir="") ?(file="") ?(mode_str="") ?(src_files="") 
  opt_file ~config ~bench ~profile =
  let intoB = config.intoB in
  let static = config.static in
  let eager = config.eager in
  let alt = config.alt in
  let mode_var = (if intoB && not static then "-D CAST " else if alt && not static then "-D ALT " else "") in
  let lst_var = (if eager && not static then "-D EAGER " else "") in
  let static_var = (if static then "-D STATIC " else "") in
  let profile_var = (if profile then "-D PROFILE " else "") in
  if bench then 
    asprintf "clang %s/bench/%s%s%s.c %s%s%s%slibC/*.c benchC/bench_json.c %s -o %s/bench/%s%s%s.out -lgc -lcjson -O3" (* -falign-functions=32 -falign-loops=32 -falign-jumps=32 *)
      log_dir 
      file 
      mode_str
      (if profile then "_profile" else "")
      mode_var
      lst_var
      static_var
      profile_var
      src_files
      log_dir 
      file 
      mode_str
      (if profile then "_profile" else "")
  else match opt_file with
  | Some filename -> 
    asprintf "clang ../result_C/%s_out.c %s%s%s../libC/*.c -o ../result/%s.out -lgc -g3 -O3"
      filename
      mode_var
      lst_var
      static_var
      filename
  | None -> 
    (* clang result_C/stdin.c libC/*.c -o result/stdin.out -lgc -g3 -std=c2x -pg -O3 *)
    asprintf "clang result_C/stdin.c %s%s%slibC/*.c -o result/stdin.out -lgc -g3 -std=c2x -pg -O3" (* TODO: -O3 *)
      mode_var
      lst_var
      static_var

let build_run c_code opt_file ~config = match opt_file with
  | Some filename ->
    (* ファイル入力モード *)
    let out_path = "../result_C/" ^ filename ^ "_out.c" in
    let oc = open_out out_path in
    Printf.fprintf oc "%s" c_code;
    close_out oc;
    (* print_debug "Generated C file: %s (Execution delegated)@." out_path *)
    let i = Sys.command (build_clang_cmd opt_file ~config ~bench:false ~profile:false) in
    if i != 0 then raise @@ Compile_bad "clang fail";
    let i = Sys.command ("../result/" ^ filename ^ ".out") in
    if i != 0 then raise @@ Compile_bad ".out fail";
    ()
  | None ->
    (* 標準入力モード *)
    let out_path = "result_C/stdin.c" in
    let oc = open_out out_path in
    Printf.fprintf oc "%s" c_code;
    close_out oc;
    (* print_debug "%s" (Compiler.build_cmd_for_stdin ()); *)
    let i = Sys.command (build_clang_cmd opt_file ~config ~bench:false ~profile:false) in
    if i != 0 then raise @@ Compile_bad "clang fail";
    let i = Sys.command "result/stdin.out" in
    if i != 0 then raise @@ Compile_bad ".out fail";
    ()

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
        build_run c_code opt_file ~config;
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

let build_run_bench ~log_dir ~file ~mode_str ~itr ~mutants_length ~config =
  let src_files = asprintf "%s/%s/%s*.c" log_dir mode_str file in
  (* _mutants.h 生成 *)
  let oc = open_out (asprintf "%s/bench/%s%s_mutants.h" log_dir file mode_str) in
  Printf.fprintf oc "#ifndef MUTANTS_H\n#define MUTANTS_H\n\n";
  let rec print_itr n =
    if n = mutants_length + 1 then ()
    else (Printf.fprintf oc "int mutant%d(void);\nint set_tys%d(void);\n" n n; print_itr (n + 1))
  in print_itr 1;
  Printf.fprintf oc "#endif";
  close_out oc;
  (* .c 生成 *)
  let oc = open_out (asprintf "%s/bench/%s%s.c" log_dir file mode_str) in
  Printf.fprintf oc "%s\n%s\n%s\n%s"
    (asprintf "#include <stdio.h>\n#include <sys/time.h>\n#include <sys/resource.h>\n#include \"../../../libC/types.h\"\n#include \"../../../benchC/bench_json.h\"\n#include \"%s%s_mutants.h\"\n" file mode_str)
    (asprintf "#define MUTANTS_LENGTH %d\n#define ITR %d\n" mutants_length itr)
    "#ifndef STATIC\nrange *range_list;\n#endif\nstatic double times[MUTANTS_LENGTH][ITR];\nint i;\nstruct rusage start_usage, end_usage;\n"
    "int main(){\n";
  let rec print_itr n =
    if n = mutants_length + 1 then ()
    else begin 
      Printf.fprintf oc "for (i = 0; i<ITR; i++){\ngetrusage(RUSAGE_SELF, &start_usage);\nmutant%d();\ngetrusage(RUSAGE_SELF, &end_usage);\ntimes[%d][i] = (double)(end_usage.ru_utime.tv_sec - start_usage.ru_utime.tv_sec) + (double)(end_usage.ru_utime.tv_usec - start_usage.ru_utime.tv_usec) * 1e-6;\nrewind(stdin);\n}\nfprintf(stderr, \"mutant%d done. \");\nfflush(stdout);\n"
       n (n - 1) n;
      print_itr (n + 1)
    end
  in print_itr 1;
  Printf.fprintf oc "return update_jsonl_file(\"%s/%s_%s.jsonl\", *times, MUTANTS_LENGTH, ITR);\n}" log_dir mode_str file;
  close_out oc;
  (* _profile.c 生成 *)
  let oc = open_out (asprintf "%s/bench/%s%s_profile.c" log_dir file mode_str) in
  Printf.fprintf oc "%s\n%s\n%s\n%s"
    (asprintf "#include <stdio.h>\n#include <gc.h>\n#include \"../../../libC/types.h\"\n#include \"../../../benchC/bench_json.h\"\n#include \"%s%s_mutants.h\"\n" file mode_str)
    (asprintf "#define MUTANTS_LENGTH %d\n" mutants_length)
    "#ifndef STATIC\nrange *range_list;\n#endif\nstatic int gc_counts[MUTANTS_LENGTH], cast_counts[MUTANTS_LENGTH], inference_counts[MUTANTS_LENGTH], longest[MUTANTS_LENGTH];\nint i;\nint gc_num, gc_tmp, current_cast, current_inference, current_longest;\n"
    "int main(){\n";
  let rec print_itr n =
    if n = mutants_length + 1 then ()
    else begin 
      Printf.fprintf oc "mutant%d();\ngc_tmp = GC_get_total_bytes();\ngc_counts[%d] = gc_tmp - gc_num;\ngc_num = gc_tmp;\ncast_counts[%d] = current_cast;\ninference_counts[%d] = current_inference;\nlongest[%d] = current_longest;\ncurrent_cast = 0;\ncurrent_inference = 0;\ncurrent_longest = 0;\nrewind(stdin);\nfprintf(stderr, \"mutant%d done. \");\nfflush(stdout);\n"
       n (n - 1) (n - 1) (n - 1) (n - 1) n;
      print_itr (n + 1)
    end
  in print_itr 1;
  Printf.fprintf oc "return update_jsonl_file_profile(\"%s/%s_%s.jsonl\", gc_counts, cast_counts, inference_counts, longest, MUTANTS_LENGTH);\n}" log_dir mode_str file;
  close_out oc;
  (* build *)
  let cmd = build_clang_cmd None ~config ~bench:true ~log_dir ~file ~mode_str ~src_files ~profile:false in
  fprintf std_formatter "@.%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Compile_bad "clang(for time) fail";
  let cmd = build_clang_cmd None ~config ~bench:true ~log_dir ~file ~mode_str ~src_files ~profile:true in
  fprintf std_formatter "@.%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Compile_bad "clang(for profile) fail";
  (* run *)
  let cmd = asprintf "%s/bench/%s%s.out < samples/input/%s.txt > /dev/null" log_dir file mode_str file in
  fprintf std_formatter "%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Compile_bad ".out(for time) fail";
  let cmd = asprintf "%s/bench/%s%s_profile.out < samples/input/%s.txt > /dev/null" log_dir file mode_str file in
  fprintf std_formatter "%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Compile_bad ".out(for profile) fail";
  ()

(* tv renew *)
let pick_tv u = match u with
  | TyVar tv -> tv
  | _ -> raise @@ Failure "not_tv"

let rec tv_renew_ty u env = match u with
  | TyVar (i, _) -> 
    begin 
    try TyVar (Environment.find (string_of_int i) env), env with
    Not_found -> let tv = pick_tv (Typing.fresh_tyvar ()) in
    let env = Environment.add (string_of_int i) tv env in
    TyVar tv, env
    end
  | TyDyn | TyInt | TyBool | TyUnit -> u, env
  | TyFun (u1, u2) -> 
    let u1, env = tv_renew_ty u1 env in
    let u2, env = tv_renew_ty u2 env in
    TyFun (u1, u2), env
  | TyList u -> 
    let u, env = tv_renew_ty u env in
    TyList u, env

let rec tv_renew_coercion c env = match c with
  | CInj _ | CProj _ | CFail _ -> c, env
  | CTvInj ((i, _), p) -> 
    begin
    try CTvInj ((Environment.find (string_of_int i) env), p), env with
    Not_found -> let tv = pick_tv (Typing.fresh_tyvar ())in
    let env = Environment.add (string_of_int i) tv env in
    CTvInj (tv, p), env
    end
  | CTvProj ((i, _), p) -> 
    begin
    try CTvProj ((Environment.find (string_of_int i) env), p), env with
    Not_found -> let tv = pick_tv (Typing.fresh_tyvar ()) in
    let env = Environment.add (string_of_int i) tv env in
    CTvProj (tv, p), env
    end
  | CTvProjInj ((i, _), p, q) -> 
    begin
    try CTvProjInj ((Environment.find (string_of_int i) env), p, q), env with
    Not_found -> let tv = pick_tv (Typing.fresh_tyvar ()) in
    let env = Environment.add (string_of_int i) tv env in
    CTvProjInj (tv, p, q), env
    end
  | CId u ->
    let u, env = tv_renew_ty u env in
    CId u, env
  | CFun (c1, c2) ->
    let c1, env = tv_renew_coercion c1 env in
    let c2, env = tv_renew_coercion c2 env in
    CFun (c1, c2), env 
  | CList c ->
    let c, env = tv_renew_coercion c env in
    CList c, env
  | CSeq (c1, c2) ->
    let c1, env = tv_renew_coercion c1 env in
    let c2, env = tv_renew_coercion c2 env in
    CSeq (c1, c2), env 

let rec tv_renew_mf mf env = match mf with
  | MatchILit _ | MatchBLit _ | MatchULit -> mf, env
  | MatchVar (x, u) -> 
    let u, env = tv_renew_ty u env in
    MatchVar (x, u), env
  | MatchNil u -> 
    let u, env = tv_renew_ty u env in
    MatchNil u, env
  | MatchCons (mf1, mf2) ->
    let mf1, env = tv_renew_mf mf1 env in
    let mf2, env = tv_renew_mf mf2 env in
    MatchCons (mf1, mf2), env
  | MatchWild u -> 
    let u, env = tv_renew_ty u env in
    MatchWild u, env

module CC = struct
  open Syntax.CC

  let rec tv_renew_exp e env = match e with
    | Var (x, us) ->
      let env = List.fold_left (fun env -> fun u -> match u with Ty u -> snd (tv_renew_ty u env) | TyNu -> env) env us in
      let us = List.map (fun u -> match u with Ty u -> Syntax.Ty (fst @@ (tv_renew_ty u env)) | TyNu -> TyNu) us in
      Var (x, us), env
    | IConst _ | BConst _ | UConst -> e, env
    | BinOp (op, e1, e2) -> 
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      BinOp (op, e1, e2), env
    | IfExp (e1, e2, e3) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      let e3, env = tv_renew_exp e3 env in
      IfExp (e1, e2, e3), env
    | FunExp (x, u, e) ->
      let u, env = tv_renew_ty u env in
      let e, env = tv_renew_exp e env in
      FunExp (x, u, e), env
    | FixExp (x, y, u1, u2, e) ->
      let u1, env = tv_renew_ty u1 env in
      let u2, env = tv_renew_ty u2 env in
      let e, env = tv_renew_exp e env in
      FixExp (x, y, u1, u2, e), env
    | AppExp (e1, e2) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      AppExp (e1, e2), env
    | CAppExp (e, c) ->
      let e, env = tv_renew_exp e env in
      let c, env = tv_renew_coercion c env in
      CAppExp (e, c), env
    | CastExp (e, u1, u2, r_p) -> 
      let e, env = tv_renew_exp e env in
      let u1, env = tv_renew_ty u1 env in
      let u2, env = tv_renew_ty u2 env in
      CastExp (e, u1, u2, r_p), env
    | MatchExp (e, ms) ->
      let e, env = tv_renew_exp e env in
      let ms, env = tv_renew_ms ms env in
      MatchExp (e, ms), env
    | LetExp (x, tvs, e1, e2) ->
      let env = List.fold_left (fun env -> fun (i, _ as tv) -> Syntax.Environment.add (string_of_int i) tv env) env tvs  in
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      LetExp (x, tvs, e1, e2), env
    | NilExp u -> 
      let u, env = tv_renew_ty u env in
      NilExp u, env
    | ConsExp (e1, e2) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      ConsExp (e1, e2), env
    and tv_renew_ms ms env = match ms with
    | (mf, e) :: ms ->
      let mf, env = tv_renew_mf mf env in
      let e, env = tv_renew_exp e env in
      let ms, env = tv_renew_ms ms env in
      (mf, e) :: ms, env
    | [] -> [], env

  let tv_renew p = match p with
  | Exp e -> 
    let e, _ = tv_renew_exp e Syntax.Environment.empty in 
    Exp e
  | LetDecl (id, tvs, e) -> 
    let env = List.fold_left (fun env -> fun (i, _ as tv) -> Syntax.Environment.add (string_of_int i) tv env) Syntax.Environment.empty tvs  in
    let e, _ = tv_renew_exp e env in
    LetDecl (id, tvs, e)
end