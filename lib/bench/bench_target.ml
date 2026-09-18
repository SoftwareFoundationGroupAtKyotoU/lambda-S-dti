type mode = S | A | B | STATIC

(* if you want to measure B, add B in modes *)
let modes = [S; A; STATIC]

let string_of_mode = function
  | S -> "S"
  | A -> "A"
  | B -> "B"
  | STATIC -> "STATIC"

let full_mode_name mode eager hash monotonic =
  Printf.sprintf "%s%s%s%s"
    (string_of_mode mode)
    (if eager     then "E" else "L")
    (if hash      then "H" else "N")
    (if monotonic then "M" else "G")

type target = {
  file : string; mode : mode; eager : bool; hash : bool; monotonic : bool;
  mutants : Syntax.ITGL.program list;
}

(* -------- Parsing & mutation (1回で両モードに使い回す) --------------- *)
let parse_and_mutate (file : string) : Syntax.ITGL.program list =
  let path = Bench_config.sample_path ~lang:`Gradti file in
  let ppf = Utils.Format.empty_formatter in
  let config = Config.create ~compile:true () in
  let channel, lexbuf = Pipeline.lex ppf (Some path) in
  let rec loop acc =
    match Pipeline.parse ppf lexbuf (Pipeline.init_state () ~config) with
    | state -> loop (state :: acc)
    | exception Lexer.Eof -> acc
  in
  let states = loop [] in
  close_in channel;
  let state = Pipeline.bundle_states_ITGL states in
  Pipeline.mutate_all ppf state

let restrict_axis (only : bool option) (requested : bool list) : bool list =
  match only with
  | None -> requested
  | Some b -> if List.mem b requested then [b] else []

let expand_targets ~eagernesses ~hash_modes ~monotonicities (prepared : (string * Syntax.ITGL.program list) list) : target list =
  List.concat_map (fun (file, mutants) ->
    let r = Bench_config.restriction_of file in
    let file_eagernesses = restrict_axis r.eager_only eagernesses in
    let file_monotonicities = restrict_axis r.monotonic_only monotonicities in
    if file_eagernesses = [] || file_monotonicities = [] then begin
      Format.eprintf
        "[Skip] %s: no (eager,monotonic) combination survives its axis restriction given the requested flags@." file;
      []
    end else
      List.concat_map (fun mode ->
        List.concat_map (fun eager ->
          List.concat_map (fun hash ->
            List.map (fun monotonic ->
              { file; mode; eager; hash; monotonic; mutants }
            ) file_monotonicities
          ) hash_modes
        ) file_eagernesses
      ) modes
  ) prepared

let restrict_grift_targets ~monotonicities files = 
  List.concat_map (fun file ->
    let r = Bench_config.restriction_of file in
    let file_monotonicities = restrict_axis r.monotonic_only monotonicities in
    if file_monotonicities = [] then begin
      Format.eprintf
        "[Skip grift] %s: no monotonic combination survives its axis restriction given the requested flags@." file;
      []
    end else
      List.map (fun b -> (file, b)) file_monotonicities
  ) files