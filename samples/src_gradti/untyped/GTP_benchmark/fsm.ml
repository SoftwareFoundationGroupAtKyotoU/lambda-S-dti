(* An N-states, N-inputs Automaton: simulate a population of automata
   playing the iterated prisoner's dilemma against each other.
   Translated from benchmarks/fsm/{typed,untyped}/{automata,population,utilities,main}.rkt
   via automata.ml/population.ml/utilities.ml/main.ml. *)

type automaton = { current : int; original : int; payoff : float; table : int array array };;

(* array_init internally calls Array.make, so (like OCaml's ref value
   restriction, extended here to monotonic arrays) it cannot be reused
   polymorphically at different element types within one file -- it gets
   monomorphized to its first use. Hence one copy per element type needed. *)
let array_init_int n f =
  let arr = Array.make n (f 0) in
  for i = 1 to n - 1 do
    arr.(i) <- f i
  done;
  arr
in

let array_init_int_array n f =
  let arr = Array.make n (f 0) in
  for i = 1 to n - 1 do
    arr.(i) <- f i
  done;
  arr
in

(* ---- automata.ml ---- *)

let make_random_automaton n =
  let transitions () = array_init_int n (fun idx -> random_int n) in
  let original_current = random_int n in
  { current = original_current; original = original_current; payoff = 0.0;
    table = array_init_int_array n (fun idx -> transitions ()) }
in

let automaton_reset a =
  { a with current = a.original; payoff = 0.0 }
in

let payoff_table = [| [| (3.0, 3.0); (0.0, 4.0) |]; [| (4.0, 0.0); (1.0, 1.0) |] |] in
let payoff current1 current2 =
  payoff_table.(current1).(current2)
in

let match_pair auto1 auto2 rounds_per_match =
  let rec loop current1 payoff1 current2 payoff2 n =
    if n = 0 then (current1, payoff1, current2, payoff2)
    else
      let (p1, p2) = payoff current1 current2 in
      let n1 = auto1.table.(current1).(current2) in
      let n2 = auto2.table.(current2).(current1) in
      loop n1 (payoff1 +. p1) n2 (payoff2 +. p2) (n - 1)
  in
  let (new1, p1, new2, p2) = loop auto1.current auto1.payoff auto2.current auto2.payoff rounds_per_match in
  ({ auto1 with current = new1; payoff = p1 }, { auto2 with current = new2; payoff = p2 })
in

(* ---- population.ml ----
   Population = Automaton* * Automaton*, Automaton* = [Arrayof Automaton] *)

let def_coo = 2 in

let array_init_automaton n f =
  let arr = Array.make n (f 0) in
  for i = 1 to n - 1 do
    arr.(i) <- f i
  done;
  arr
in

let build_random_population n =
  let v = array_init_automaton n (fun idx -> make_random_automaton def_coo) in
  (v, v)
in

let population_payoffs population =
  let (pop, _) = population in
  list_map (fun a -> a.payoff) (array_to_list pop)
in

let population_reset a_star =
  array_iteri (fun i x -> a_star.(i) <- automaton_reset x) a_star
in

let match_up_star population0 rounds_per_match =
  let (a_star, _) = population0 in
  population_reset a_star;
  let n = Array.length a_star in
  let i = ref 0 in
  while !i < n - 1 do
    let p1 = a_star.(!i) in
    let p2 = a_star.(!i + 1) in
    let (a1, a2) = match_pair p1 p2 rounds_per_match in
    a_star.(!i) <- a1;
    a_star.(!i + 1) <- a2;
    i := !i + 2
  done;
  population0
in

let shuffle_vector src dst =
  array_iteri (fun i x -> dst.(i) <- x) src;
  array_iteri
    (fun i x ->
      let j = random_int (i + 1) in
      (if j <> i then dst.(i) <- dst.(j) else ());
      dst.(j) <- x)
    src;
  (dst, src)
in

(* ---- utilities.ml ---- *)

let sum l = list_fold_left (fun acc x -> acc +. x) 0.0 l in

let relative_average l w =
  sum l /. w /. float_of_int (list_length l)
in

let accumulated_percents probabilities =
  let total = sum probabilities in
  let rec relative_to_absolute payoffs so_far =
    match payoffs with
    | [] -> []
    | p :: rest ->
      let nxt = so_far +. p in
      (nxt /. total) :: relative_to_absolute rest nxt
  in
  relative_to_absolute probabilities 0.0
in

let choose_randomly probabilities speed =
  let percents = accumulated_percents probabilities in
  let pick () =
    let r = random_float 1.0 in
    let rec loop percents = match percents with
      | [] -> 0
      | p :: rest -> if r <. p then 0 else 1 + loop rest
    in
    loop percents
  in
  list_init speed (fun idx -> pick ())
in

let death_birth population rate =
  let (a_star, b_star) = population in
  let payoffs = list_map (fun x -> x.payoff) (array_to_list a_star) in
  let substitutes = choose_randomly payoffs rate in
  list_iteri (fun i p -> a_star.(i) <- automaton_reset b_star.(p)) substitutes;
  shuffle_vector a_star b_star
in

(* ---- main.ml ---- *)

let assert_ v p =
  (* `exit` has type `int -> unit` here (not `int -> 'a`), so the failure
     branch needs a dummy float after it to type-match the success branch;
     it never actually runs since `exit` terminates the process first. *)
  if p v then v else (print_string "assert failed\n"; exit 1; 0.0)
in

let payoff_p x = x >=. 0.0 in

let rec evolve p c s r =
  if c = 0 then []
  else
    let p2 = match_up_star p r in
    let pp = population_payoffs p2 in
    let p3 = death_birth p2 s in
    assert_ (relative_average pp (float_of_int r)) payoff_p :: evolve p3 (c - 1) s r
in

let rec print_floats l =
  match l with
  | [] -> ()
  | x :: rest -> print_float x; print_string " "; print_floats rest
in

random_init 7480;
let result = evolve (build_random_population 300) 500 100 20 in
print_floats result;
print_newline ();;
