open Syntax
open Config
open Types

let lift1 ~config (core : CC.value -> CC.value) : CC.value =
  if config.intoB then
    CC.FunBV (fun _ v -> core v)
  else if config.alt then
    CC.FunDualV (fun _ ->
      (fun v -> core v),
      (function
        | v, CC.CoercionV c -> Eval.CC.toplevel_coerce ~config (core v) c
        | _ -> raise @@ Stdlib_bug "lift1: expected coercion argument"))
  else
    CC.FunSV (fun _ -> function
      | v, CC.CoercionV c -> Eval.CC.toplevel_coerce ~config (core v) c
      | _ -> raise @@ Stdlib_bug "lift1: expected coercion argument")
