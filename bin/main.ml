open Format
open Lambda_S1_dti

let config = { Config.default with opt_file = None }

let start file =
  config.opt_file <- file;
  if config.alt && config.intoB then failwith "-a and -b could not be at the same time";
  (* NOTE: when compiling, -k does not need *)
  if config.compile && config.kNorm then config.kNorm <- false;
  if not (config.compile) && config.eager then failwith "-e interpreter is yet";
  let ppf = if config.debug then err_formatter else Utils.Format.empty_formatter in
  Pipeline.print_title ppf "Lexer";
  let channel, lexbuf = match file with
  | None ->
    fprintf ppf "Reading from stdin@.";
    stdin, Lexing.from_channel stdin
  | Some f ->
    fprintf ppf "Reading from file \"%s\"@." f;
    let channel = open_in f in
    let lexbuf = Lexing.from_channel channel in
    lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = f};
    channel, lexbuf
  in
  try
    if config.intoB then 
      let env, tyenv, kfunenvs, kenv = Stdlib.pervasives_LB ~debug:config.debug ~compile:config.compile in
      if config.compile then Pipeline.read_compile ppf lexbuf tyenv kfunenvs config.opt_file ~intoB:config.intoB ~alt:config.alt ~eager:config.eager
      else Pipeline.read_eval_LB ppf lexbuf env tyenv kfunenvs kenv ~kNorm:config.kNorm ~debug:config.debug ~res_ppf:std_formatter
    else 
      let env, tyenv, kfunenvs, kenv = Stdlib.pervasives_LS ~alt:config.alt ~debug:config.debug ~compile:config.compile in
      if config.compile then Pipeline.read_compile ppf lexbuf tyenv kfunenvs config.opt_file ~intoB:config.intoB ~alt:config.alt ~eager:config.eager
      else Pipeline.read_eval_LS ppf lexbuf env tyenv kfunenvs kenv ~kNorm:config.kNorm ~debug:config.debug ~alt:config.alt ~res_ppf:std_formatter
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
      ("-k", Arg.Unit (fun () -> config.kNorm <- true), " Evaluate on k-Normal form");
      ("-a", Arg.Unit (fun () -> config.alt <- true), " Use alternative translation");
      ("-c", Arg.Unit (fun () -> config.compile <- true), " Compile the program to C code");
      ("-b", Arg.Unit (fun () -> config.intoB <- true), " Translate into LB");
      ("-e", Arg.Unit (fun () -> config.eager <- true), " Eager list coercion-/cast-composition")
    ]
  in
  let parse_argv arg = match !file with
  | None -> file := Some arg
  | Some _ -> raise @@ Arg.Bad "error: only one file can be specified"
  in
  Arg.parse options parse_argv usage;
  start !file

(* gcc logs/20260102-12:50:40/bench/zipwithSEC.c -D EAGER libC/*.c benchC/bench_json.c logs/20260102-12:50:40/SEC/zipwith*.c -o result/stdin.out -lgc -lcjson -O2 *)