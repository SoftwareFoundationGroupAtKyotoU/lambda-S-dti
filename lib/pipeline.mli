open Format
open Syntax

exception Not_Exp

type 't state

val init_state : 'a -> config:Config.t -> 'a state
val bundle_states : CC.program state list -> CC.program state
val fresh_program : 'a state -> unit state

val lex : formatter -> string option -> in_channel * Lexing.lexbuf
val parse : formatter -> Lexing.lexbuf -> 'a state -> ITGL.program state
val typing_ITGL : formatter -> ITGL.program state -> ITGL.program state
val translate_to_CC : formatter -> ITGL.program state -> config:Config.t ->bench_ppf:formatter -> bench:int -> CC.program state * ty
val eval : formatter -> formatter -> CC.program state -> config:Config.t -> CC.program state * string * CC.value
val kNorm_funs : formatter -> CC.program state -> config:Config.t -> KNorm.program state
val closure : formatter -> KNorm.program state -> config:Config.t -> Cls.program state
val toC : formatter -> Cls.program state -> config:Config.t -> bench:int -> string

val mutate_all : ITGL.program state -> ITGL.program list