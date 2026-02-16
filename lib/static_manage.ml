open Syntax
open Utils.Error

module TyManager = struct
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

module RangeManager = struct
  module Range = Map.Make (struct type t = range let compare = compare end)

  type state = {
    counter : int;
    cache : int Range.t;
  }

  let current_state = ref {
    counter = -1;
    cache = Range.empty;
  }

  let clear () = 
    current_state := { counter = -1; cache = Range.empty }

  let save () = !current_state

  let restore s = 
    current_state := s

  let range_id r = 
    try
      Range.find r !current_state.cache
    with Not_found ->
      let c = !current_state.counter + 1 in
      current_state := {
        counter = c;
        cache = Range.add r c !current_state.cache;
      };
      c

  let get_definitions () = Range.bindings !current_state.cache
end

module CrcManager = struct
  module StaticCrc = Map.Make (struct type t = Cls.coercion let compare = compare end)

  type state = {
    counter : int;
    cache : string StaticCrc.t;
  }

  let current_state = ref {
    counter = 0;
    cache = StaticCrc.empty;
  }

  let clear () = 
    current_state := { counter = 0; cache = StaticCrc.empty }

  let save () = !current_state

  let restore s = 
    current_state := s

  let register s =
    if not (StaticCrc.mem s !current_state.cache) then
      let c = !current_state.counter + 1 in
      let name = Printf.sprintf "crc%d" c in
      current_state := {
        counter = c;
        cache = StaticCrc.add s name !current_state.cache;
      }
  
  let mem s = StaticCrc.mem s !current_state.cache

  let find s = StaticCrc.find s !current_state.cache

  let get_definitions () = StaticCrc.bindings !current_state.cache
end

let static_clear () = 
  TyManager.clear ();
  RangeManager.clear ();
  CrcManager.clear ()

let static_save () =
  TyManager.save (), RangeManager.save (), CrcManager.save ()

let static_restore (s1, s2, s3) =
  TyManager.restore s1;
  RangeManager.restore s2;
  CrcManager.restore s3
