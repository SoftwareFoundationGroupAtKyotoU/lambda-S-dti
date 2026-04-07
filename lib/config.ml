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

let create ~kNorm ~alt ~intoB ~eager ~compile ~static ~hash ~opt_file () =
  { default with kNorm; alt; intoB; eager; compile; static; hash; opt_file }
  
let adjust config file =
  (* configの初期設定 *)
  config.opt_file <- file;
  if config.alt && config.intoB then failwith "-a and -b could not be at the same time";
  (* NOTE: when compiling, -k does not need *)
  if config.compile && config.kNorm then config.kNorm <- false;
  if not (config.compile) && config.eager then failwith "-e interpreter is yet";
  (* NOTE: if --static, let alt be false, and intoB and eager be true *)
  if config.static then begin
    if not config.compile then failwith "--static interpreter is yet"; (* because -e should be true for compiler *)
    config.alt <- false;
    config.intoB <- true;
    config.eager <- true;
  end;
  config