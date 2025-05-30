(** Utility functions to handle ranges. *)
module Error = struct
  open Format
  open Lexing

  (* type position is {pos_fname : string; pos_lnum : int; pos_bol : int; pos_cnum : int;} in module Lexing *)

  type range = {
    start_p: position;
    end_p: position;
  }

  (* for INTV or ID in parser *)
  type 'a with_range = {
    value: 'a;
    range: range;
  }

  let join_range r1 r2 = {
    start_p=r1.start_p;
    end_p=r2.end_p;
  }

  (* for the range of 0 in -e -> 0 - e *)
  let dummy_range = {
    start_p=dummy_pos;
    end_p=dummy_pos;
  }

  let pp_range ppf {start_p=p1; end_p=p2} =
    if p1.pos_fname <> "" then
      fprintf ppf "File \"%s\", " p1.pos_fname;
    fprintf ppf "line %d, character %d -- line %d, character %d"
      p1.pos_lnum
      (p1.pos_cnum - p1.pos_bol)
      p2.pos_lnum
      (p2.pos_cnum - p2.pos_bol)
end

(** Utility functions for Format module. *)
module Format = struct
  open Format

  (** No-op formatter. *)
  let empty_formatter = make_formatter (fun _ _ _ -> ()) (fun _ -> ())

  (** If "debug" is true, then returns err_formatter. Otherwise returns empty_formatter. *)
  let make_print_debug debug f =
    if debug then
      fprintf err_formatter f
    else
      fprintf empty_formatter f
end

(** Utility functions for Lexing module. *)
(* TODO : why does it exist? *)
module Lexing = struct
  (** Altenative to Lexing.flush_input so that pos_bol is also reset to 0. *)
  let flush_input lexbuf =
    Lexing.flush_input lexbuf;
    lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_bol = 0}
end

(** Utility functions for List module. *)
module List = struct

  (** Zip two lists. The length of the result will be the same as the length of the shorter list. *)
  let zip l1 l2 =
    let rec zip' l1 l2 l = match l1, l2 with
      | [], _ | _, [] -> List.rev l
      | (x :: xs), (y :: ys) -> zip' xs ys @@ (x, y) :: l
    in
    zip' l1 l2 []

  (** Generate a list of length "n" where all items are "i" for TyNu in translate.ml. *)
  let repeat i n =
    let rec f i n l = if n <= 0 then l else f i (n - 1) @@ i :: l in
    f i n []
end
