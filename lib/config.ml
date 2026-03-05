type t = {
  mutable debug : bool;
  mutable kNorm : bool;
  mutable alt : bool;
  mutable compile : bool;
  mutable intoB : bool;
  mutable eager : bool;
  mutable static : bool;
  mutable hash : bool;
  mutable opt_file : string option;
}

let default = {
  debug = false;
  kNorm = false;
  alt = false;
  compile = false;
  intoB = false;
  eager = false;
  static = false;
  hash = false;
  opt_file = None;
}

let create ~alt ~intoB ~eager ~compile ~static ~hash ~opt_file () =
  { default with alt; intoB; eager; compile; static; hash; opt_file }