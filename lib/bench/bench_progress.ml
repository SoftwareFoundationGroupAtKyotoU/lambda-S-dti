type t = {
  label : string;
  total : int;
  mutable done_ : int;
  start_t : float;
  width : int;
}

let create ~label ~total ~ordinal ~total_targets =
  (* 見出しを出してからバーを開始 *)
  Printf.printf "\n==> [%d/%d] %s (%d mutants)\n%!"
    ordinal total_targets label total;
  { label; total; done_ = 0; start_t = Unix.gettimeofday (); width = 28 }

let print ?(final=false) (p:t) =
  let now     = Unix.gettimeofday () in
  let done_i  = p.done_ in
  let total_i = max 1 p.total in
  let frac    = float_of_int done_i /. float_of_int total_i in
  let elapsed = now -. p.start_t in
  let eta     = if frac > 0.0 then elapsed *. (1.0 -. frac) /. frac else Float.nan in
  let filled  = int_of_float (Float.min 1.0 frac *. float_of_int p.width) in
  let bar     = (String.make filled '#') ^ (String.make (p.width - filled) '-') in
  Printf.printf "\r%-16s [%s] %d/%d (%.1f%%)  t=%.1fs  ETA:%s%!"
    p.label bar done_i total_i (100. *. frac) elapsed
    (if Float.is_nan eta then " ?" else Printf.sprintf " %.1fs" eta);
  if final then Printf.printf "\n%!"

let tick (p:t) =
  p.done_ <- p.done_ + 1;
  print p