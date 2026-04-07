open Format
open Lambda_S_dti

let rec repl ppf lexbuf programs ~config ~state =
  flush stderr; flush stdout;
  if lexbuf.Lexing.lex_curr_p.pos_fname = "" then fprintf std_formatter "# @?";
  let state, programs = 
    begin try 
      let cc_state =
        state 
        |> Pipeline.parse ppf lexbuf
        |> Pipeline.typing_ITGL ppf
        |> Pipeline.translate_to_CC ppf ~config ~bench_ppf:Utils.Format.empty_formatter ~bench:0
      in
      if config.compile then
        let programs = cc_state.program :: programs in
        (* Compilation *)
        match cc_state.program with
        | Syntax.CC.Exp _ -> 
          let _ = 
            { cc_state with program = Pipeline.bundle_programs programs }
            |> Pipeline.kNorm_funs ppf ~config
            |> Pipeline.closure ppf ~config
            |> Pipeline.toC ppf ~config ~bench:0
            |> Builder.build_run ~config
          in
          fprintf ppf "@.";
          Pipeline.init_state () ~config, []
          (* TODO: ファイルモードのとき，プログラムがきちんと書れていなくてもコンパイルが通ることがある (ex: bad.ml) *)
        | _ -> cc_state |> Pipeline.change_state_program (), programs
      else if config.kNorm then
        (* Evaluation on kNormalized term *)
        let state, kx, kv = 
          cc_state
          |> Pipeline.kNorm_funs ppf ~config
          |> Pipeline.keval ppf ~config
        in
        fprintf std_formatter "%a : %a = %a@." pp_print_string kx Pp.pp_ty2 state.ty Pp.KNorm.pp_value2 kv;
        state |> Pipeline.change_state_program (), []
      else
        (* Evaluation *)
        let state, x, v = 
          cc_state
          |> Pipeline.eval ppf ~config
        in
        fprintf std_formatter "%a : %a = %a@." pp_print_string x Pp.pp_ty2 state.ty Pp.CC.pp_value2 v;
        state |> Pipeline.change_state_program (), []
    with
    | Parser.Error -> (* Menhir *)
      let token = Lexing.lexeme lexbuf in
      fprintf err_formatter "Parser.Error: unexpected token %s@." token;
      Utils.Lexing.flush_input lexbuf;
      state, programs
    | Typing.Type_error message ->
      fprintf err_formatter "Type_error: %s@." message;
      state, programs
    | Syntax.Blame (r, p) -> 
      begin match p with
      | Pos -> fprintf err_formatter "Blame on the expression side:\n%a@." Utils.Error.pp_range r
      | Neg -> fprintf err_formatter "Blame on the environment side:\n%a@." Utils.Error.pp_range r
      end;
      state, programs
    | Failure message ->
      fprintf err_formatter "Failure: %s@." message;
      Utils.Lexing.flush_input lexbuf;
      state, programs
    end
  in
  repl ppf lexbuf programs ~config ~state

let start file ~(config:Config.t) =
  let ppf = if config.debug then err_formatter else Utils.Format.empty_formatter in
  let channel, lexbuf = Pipeline.lex ppf file in
  let config = Config.adjust config file in
  let state = Pipeline.init_state () ~config in
  try
    repl ppf lexbuf [] ~config ~state
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
  let config = { Config.default with opt_file = None } in
  let options = Arg.align [
      ("-d", Arg.Unit (fun () -> config.debug <- true), " Enable debug mode");
      ("-k", Arg.Unit (fun () -> config.kNorm <- true), " Evaluate on k-Normal form");
      ("-a", Arg.Unit (fun () -> config.alt <- true), " Use alternative translation");
      ("-c", Arg.Unit (fun () -> config.compile <- true), " Compile the program to C code");
      ("-b", Arg.Unit (fun () -> config.intoB <- true), " Translate into LB");
      ("-e", Arg.Unit (fun () -> config.eager <- true), " Eager list coercion-/cast-composition");
      ("-h", Arg.Unit (fun () -> config.hash <- true), " hash-consing / compose-memo on");
      ("--static", Arg.Unit (fun () -> config.static <- true), " Evaluate or compile only fully statically program");
    ]
  in
  let parse_argv arg = match !file with
  | None -> file := Some arg
  | Some _ -> raise @@ Arg.Bad "error: only one file can be specified"
  in
  Arg.parse options parse_argv usage;
  start !file ~config

(* clang logs/20260102-12:50:40/bench/zipwithSEC.c -D EAGER libC/*.c benchC/bench_json.c logs/20260102-12:50:40/SEC/zipwith*.c -o result/stdin.out -lgc -lcjson -O2 *)