open Format
open Lambda_S_dti

let config = { Config.default with opt_file = None }

let start file =
  (* configの初期設定 *)
  config.opt_file <- file;
  if config.alt && config.intoB then failwith "-a and -b could not be at the same time";
  (* NOTE: when compiling, -k does not need *)
  if config.compile && config.kNorm then config.kNorm <- false;
  if not (config.compile) && config.eager then failwith "-e interpreter is yet";
  (* NOTE: if -s, let alt be false, and intoB and eager be true *)
  if config.static then begin
    if not config.compile then failwith "-s interpreter is yet";
    config.alt <- false;
    config.intoB <- true;
    config.eager <- true;
  end;

  let ppf = if config.debug then err_formatter else Utils.Format.empty_formatter in

  let channel, lexbuf = Pipeline.lex ppf file in
  
  try
    if config.intoB then 
      let env, tyenv, kfunenvs, kenv = Stdlib.pervasives_LB ~config in
      if config.compile then Pipeline.read_compile ppf lexbuf tyenv kfunenvs config.opt_file ~config
      else Pipeline.read_eval_LB ppf lexbuf env tyenv kfunenvs kenv ~config ~res_ppf:std_formatter
    else 
      let env, tyenv, kfunenvs, kenv = Stdlib.pervasives_LS ~config in
      if config.compile then Pipeline.read_compile ppf lexbuf tyenv kfunenvs config.opt_file ~config
      else Pipeline.read_eval_LS ppf lexbuf env tyenv kfunenvs kenv ~config ~res_ppf:std_formatter
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
      ("-e", Arg.Unit (fun () -> config.eager <- true), " Eager list coercion-/cast-composition");
      ("--static", Arg.Unit (fun () -> config.static <- true), " Evaluate or compile only fully statically program")
    ]
  in
  let parse_argv arg = match !file with
  | None -> file := Some arg
  | Some _ -> raise @@ Arg.Bad "error: only one file can be specified"
  in
  Arg.parse options parse_argv usage;
  start !file

(* gcc logs/20260102-12:50:40/bench/zipwithSEC.c -D EAGER libC/*.c benchC/bench_json.c logs/20260102-12:50:40/SEC/zipwith*.c -o result/stdin.out -lgc -lcjson -O2 *)