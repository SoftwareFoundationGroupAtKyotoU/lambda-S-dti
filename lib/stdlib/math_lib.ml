open Syntax
open Type_utils
open Types_lib

let core_sqrt = function
  | CC.FloatV f -> CC.FloatV (sqrt f)
  | _ -> raise @@ Stdlib_bug "sqrt: unexpected value"
let lib_sqrt ~config = Prim_lib.lift1 ~config core_sqrt

let core_sin = function
  | CC.FloatV f -> CC.FloatV (sin f)
  | _ -> raise @@ Stdlib_bug "sin: unexpected value"
let lib_sin ~config = Prim_lib.lift1 ~config core_sin

let core_exp = function
  | CC.FloatV f -> CC.FloatV (exp f)
  | _ -> raise @@ Stdlib_bug "exp: unexpected value"
let lib_exp ~config = Prim_lib.lift1 ~config core_exp

let core_log = function
  | CC.FloatV f -> CC.FloatV (log f)
  | _ -> raise @@ Stdlib_bug "log: unexpected value"
let lib_log ~config = Prim_lib.lift1 ~config core_log

let core_round = function
  | CC.FloatV f -> CC.FloatV (Float.round f)
  | _ -> raise @@ Stdlib_bug "round: unexpected value"
let lib_round ~config = Prim_lib.lift1 ~config core_round

let lib_max_int ~config:_ = CC.IntV max_int
let lib_min_int ~config:_ = CC.IntV min_int

let builtins : builtin list = [
    { name = "max_int"; impl = Native (lib_max_int, tysc_of_ty TyInt);                      c_backing = CImpl "max_int" };
    { name = "min_int"; impl = Native (lib_min_int, tysc_of_ty TyInt);                      c_backing = CImpl "min_int" };
    { name = "succ";    impl = ITGL "let succ x = x + 1;;";                                 c_backing = CImpl "succ" };
    { name = "prec";    impl = ITGL "let prec x = x - 1;;";                                 c_backing = CImpl "prec" };
    { name = "min";     impl = ITGL "let min x y = if x < y then x else y;;";               c_backing = CImpl "min" };
    { name = "max";     impl = ITGL "let max x y = if x > y then x else y;;";               c_backing = CImpl "max" };
    { name = "abs";     impl = ITGL "let abs x = if x < 0 then -x else x;;";                c_backing = CImpl "abs_ml" };
    { name = "sqrt";  impl = Native (lib_sqrt, tysc_of_ty @@ TyFun (TyFloat, TyFloat));  c_backing = CImpl "sqrt_ml" };
    { name = "sin";   impl = Native (lib_sin, tysc_of_ty @@ TyFun (TyFloat, TyFloat));   c_backing = CImpl "sin_ml" };
    { name = "exp";   impl = Native (lib_exp, tysc_of_ty @@ TyFun (TyFloat, TyFloat));   c_backing = CImpl "exp_ml" };
    { name = "log";   impl = Native (lib_log, tysc_of_ty @@ TyFun (TyFloat, TyFloat));   c_backing = CImpl "log_ml" };
    { name = "round"; impl = Native (lib_round, tysc_of_ty @@ TyFun (TyFloat, TyFloat)); c_backing = CImpl "round_ml" };
    { name = "fmin";  impl = ITGL "let fmin x y = if x <. y then x else y;;";            c_backing = CImpl "fmin_ml" };
    { name = "fmax";  impl = ITGL "let fmax x y = if x >. y then x else y;;";            c_backing = CImpl "fmax_ml" };
  ]
