open Syntax
open Types_lib

exception Stdlib_bug = Types_lib.Stdlib_bug
exception Stdlib_exit = Types_lib.Stdlib_exit

let builtins : builtin list =
  Io_lib.builtins @ Predicates_lib.builtins @ Basic_lib.builtins @ Math_lib.builtins
  @ Random_lib.builtins @ List_lib.builtins @ Array_lib.builtins

let pervasives ~config =
  let initial_envs = Environment.empty, Environment.empty in
  let add_to_envs (env, tyenv) builtin =
    (* CUnimplemented builtins have no C backing, so they must stay out of the
       environment while compiling -- otherwise they type-check fine (their
       ITGL/Native definition is still visible here) but later crash deep in
       the backend when it fails to find their (nonexistent) C name. *)
    if config.Config.compile && builtin.c_backing = CUnimplemented then
      env, tyenv
    else match builtin.impl with
    | Native (f, tysc) ->
      Environment.add builtin.name (f ~config) env, Environment.add builtin.name tysc tyenv
    | ITGL str ->
      let e = Parser.toplevel Lexer.main @@ Lexing.from_string str in
      let e, u = Typing.ITGL.type_of_program tyenv e in
      let tyenv, e, _ = Normalize.ITGL.normalize tyenv e u in
      let new_tyenv, f, _ = Translate.ITGL.translate ~config tyenv e in
      let _ = Typing.CC.type_of_program tyenv f in
      let f, _ = Translate.CC.translate ~config tyenv f in
      let _ = Typing.CC.type_of_program tyenv f in
      let env, _, _ = Eval.CC.eval_program ~config env f in
      env, new_tyenv
  in
  let env, tyenv = List.fold_left add_to_envs initial_envs builtins in
  let pick_tvs name = match Environment.find name tyenv with TyScheme (tvs, _) -> tvs in
  let initial_compile_env = (Environment.empty, Environment.empty, Environment.empty), V.empty, Environment.empty in
  let add_to_compile_env ((alphaenv, tvsenv,  betaenv), known, args) builtin = match builtin.c_backing with
    | CImpl cname -> (Environment.add builtin.name cname alphaenv, Environment.add cname (pick_tvs builtin.name) tvsenv, Environment.add cname cname betaenv), V.add cname known, Environment.add cname ([], 0) args
    | CUnimplemented -> (alphaenv, tvsenv, betaenv), known, args
  in
  let compile_env = List.fold_left add_to_compile_env initial_compile_env builtins in
  env, tyenv, compile_env
