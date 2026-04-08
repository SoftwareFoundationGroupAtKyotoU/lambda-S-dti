type t = {
  debug : bool;
  kNorm : bool;
  alt : bool;
  compile : bool;
  intoB : bool;
  eager : bool;
  static : bool;
  hash : bool;
  opt_file : string option;
}

let create ?(debug=false) ?(kNorm=false) ?(alt=false) ?(intoB=false) ?(eager=false) ?(compile=false) ?(static=false) ?(hash=false) ?(opt_file=None) () =
  (* invalid combination *)
  if alt && intoB then 
    failwith "Config error: -a and -b could not be at the same time";
  if not compile && intoB && not eager then 
    failwith "NotImplemented: lazy cast application for -b interpreter is yet";
  if not compile && not intoB && eager then 
    failwith "NotImplemented: eager coercion application for not -b interpreter is yet";
  if not compile && hash then 
    failwith "NotImplemented: hash consing for interpreter is yet";
  if not compile && static then
    failwith "NotImplemented: --static interpreter is yet";
  if compile && intoB && hash then
    failwith "NotImplemented: hash consing is only for coercion";
  (* NOTE: if --static, let alt be false, and intoB and eager be true *)
  let alt, intoB, eager =
    if static then 
      (false, true, true)
    else 
      (alt, intoB, eager)
  in
  (* NOTE: when compiling, -k is always true *)
  let kNorm = if compile then true else kNorm in
  { debug; kNorm; alt; intoB; eager; compile; static; hash; opt_file }