type t = {
  (* execution formula *)
  debug : bool;
  compile : bool;
  (* translation formula *)
  alt : bool;
  intoB : bool;
  (* evaluation formula *)
  eager : bool;
  monotonic : bool;
  (* modes for compiler *)
  static : bool;
  hash : bool;
  (* clang optimization level, e.g. "-O3" *)
  opt_level : string;
  (* filemode *)
  file : string option;
}

let valid_opt_levels = ["-O0"; "-O1"; "-O2"; "-O3"; "-Os"; "-Oz"; "-Ofast"]

let create ?(debug=false) ?(alt=false) ?(intoB=false) ?(eager=false) ?(compile=false) ?(static=false) ?(hash=false) ?(monotonic=true) ?(opt_level="-O3") ?(file=None) () =
  (* invalid combination *)
  if alt && intoB then
    failwith "Config error: -a and -b could not be at the same time";
  if monotonic && intoB then
    failwith "Config error: --monotonic and -b could not be at the same time";
  if not (List.mem opt_level valid_opt_levels) then
    failwith (Printf.sprintf "Config error: invalid opt_level %s (must be one of %s)"
      opt_level (String.concat ", " valid_opt_levels));
  if not compile && hash then 
    failwith "NotImplemented: hash consing for interpreter is yet";
  if not compile && static then
    failwith "NotImplemented: --static interpreter is yet";
  if compile && intoB && hash then
    failwith "NotImplemented: hash consing is only for coercion";
  (* NOTE: if --static, let alt and hash be false, and intoB and eager be true *)
  let alt, intoB, eager, monotonic, hash =
    if static then 
      (false, true, true, false, false)
    else 
      (alt, intoB, eager, monotonic, hash)
  in
  { debug; alt; intoB; eager; compile; static; hash; monotonic; opt_level; file }