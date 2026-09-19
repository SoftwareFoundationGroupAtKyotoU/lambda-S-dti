open Syntax

(* User-facing errors raised by parser.mly's grammar actions (unbound type name, malformed
 * record literal, etc.), as well as internal-invariant violations that predate this module.
 * Kept in its own plain .ml file (not parser.mly's header) because menhir auto-generates a
 * restrictive parser.mli that only exports the token type, `exception Error`, and `toplevel` --
 * nothing else defined in the %{ %} header block is visible outside parser.ml. Anything that
 * needs to be seen from other modules (Pipeline, bin/main.ml, the test suite) has to live here
 * instead. *)
exception Parser_bug of string

(* id -> ty, fully resolved. Persists across toplevel statements within one session (unlike
 * parser.mly's own tyvenv, which is reset every single toplevel call for 'a-style type-variable
 * scoping), so it is NOT reset on every parse. Only cleared via reset, called by
 * Pipeline.init_state at the start of a fresh session. *)
let tynameenv : ty Environment.t ref = ref Environment.empty

let reset () = tynameenv := Environment.empty
