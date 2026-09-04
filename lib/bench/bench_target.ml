type mode = S | A | B | STATIC

(* if you want to measure B, add B in modes *)
let modes = [S; A; STATIC]

let string_of_mode = function
  | S -> "S"
  | A -> "A"
  | B -> "B"
  | STATIC -> "STATIC"

let full_mode_name mode eager hash =
  Printf.sprintf "%s%s%s" (string_of_mode mode) (if eager then "E" else "L") (if hash then "H" else "N")

type target = {
  file : string; mode : mode; eager : bool; hash : bool;
  mutants : Syntax.ITGL.program list;
}

(* -------- Parsing & mutation (1回で両モードに使い回す) --------------- *)
let parse_and_mutate (file : string) : Syntax.ITGL.program list =
  let path = Bench_config.sample_path ~lang:`Gradti file in
  let ppf = Utils.Format.empty_formatter in
  let _, lexeme = Pipeline.lex ppf (Some path) in
  Pipeline.init_state () ~config:(Config.create ~compile:true ())
  |> Pipeline.parse ppf lexeme
  |> Pipeline.mutate_all

let expand_targets ~eagernesses ~hash_modes (prepared : (string * Syntax.ITGL.program list) list) : target list =
  List.concat_map (fun (file, mutants) ->
    List.concat_map (fun mode -> 
      List.concat_map (fun eager ->
        List.map (fun hash -> 
          { file; mode; eager; hash; mutants }
        ) hash_modes
      ) eagernesses
    ) modes
  ) prepared