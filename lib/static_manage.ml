open Syntax

module StaticTyManager = struct
  module StaticTy = Map.Make (struct type t = ty let compare = compare end)

  type state = {
    counter : int;
    cache : string StaticTy.t;
  }

  let current_state = ref {
    counter = 0;
    cache = StaticTy.empty;
  }

  let clear () = 
    current_state := { counter = 0; cache = StaticTy.empty }

  let save () = !current_state

  let restore s = 
    current_state := s

  let register u =
    if not (StaticTy.mem u !current_state.cache) then
      let c = !current_state.counter + 1 in
      let name = Printf.sprintf "ty%d" c in
      current_state := {
        counter = c;
        cache = StaticTy.add u name !current_state.cache;
      }

  let find u = StaticTy.find u !current_state.cache

  let get_definitions () = StaticTy.bindings !current_state.cache
end