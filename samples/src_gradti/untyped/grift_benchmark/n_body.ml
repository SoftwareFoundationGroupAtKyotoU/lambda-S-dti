let pi = 3.141592653589793;;
let days_per_year = 365.24;;
let solar_mass = (4.0 *. pi) *. pi;;
let dt = 0.01;;

let make_body x y z vx vy vz mass =
  let v = Array.make 7 0.0 in
  (**)
  v.(0) <- x;
  v.(1) <- y;
  v.(2) <- z;
  v.(3) <- vx;
  v.(4) <- vy;
  v.(5) <- vz;
  v.(6) <- mass;
  v;;

let set_body_x b v = b.(0) <- v;;
let body_x b = b.(0);;

let set_body_y b v = b.(1) <- v;;
let body_y b = b.(1);;

let set_body_z b v = b.(2) <- v;;
let body_z b = b.(2);;

let set_body_vx b v = b.(3) <- v;;
let body_vx b = b.(3);;

let set_body_vy b v = b.(4) <- v;;
let body_vy b = b.(4);;

let set_body_vz b v = b.(5) <- v;;
let body_vz b = b.(5);;

let set_body_mass b v = b.(6) <- v;;
let body_mass b = b.(6);;

let sun = make_body 0.0 0.0 0.0 0.0 0.0 0.0 solar_mass;;

let jupiter =
  make_body
    4.84143144246472090
    (-.1.16032004402742839)
    (-.1.03622044471123109e-1)
    (1.66007664274403694e-3 *. days_per_year)
    (7.69901118419740425e-3 *. days_per_year)
    (-.6.90460016972063023e-5 *. days_per_year)
    (9.54791938424326609e-4 *. solar_mass);;

let saturn =
  make_body
    8.34336671824457987
    4.12479856412430479
    (-.4.03523417114321381e-1)
    (-.2.76742510726862411e-3 *. days_per_year)
    (4.99852801234917238e-3 *. days_per_year)
    (2.30417297573763929e-5 *. days_per_year)
    (2.85885980666130812e-4 *. solar_mass);;

let uranus =
  make_body
    1.28943695621391310e1
    (-.1.51111514016986312e1)
    (-.2.23307578892655734e-1)
    (2.96460137564761618e-03 *. days_per_year)
    (2.37847173959480950e-03 *. days_per_year)
    (-.2.96589568540237556e-05 *. days_per_year)
    (4.36624404335156298e-05 *. solar_mass);;

let neptune =
  make_body
    1.53796971148509165e+01
    (-.2.59193146099879641e+01)
    1.79258772950371181e-01
    (2.68067772490389322e-03 *. days_per_year)
    (1.62824170038242295e-03 *. days_per_year)
    (-.9.51592254519715870e-05 *. days_per_year)
    (5.15138902046611451e-05 *. solar_mass);;

let system = [| sun; jupiter; saturn; uranus; neptune |];;

let system_size = 5;;

(* ------------------------------- *)
let offset_momentum () =
  let rec offset_momentum_loop i1 px py pz =
    if i1 = system_size then
      begin
        system.(0).(3) <- (0.0 -. px) /. solar_mass;
        system.(0).(4) <- (0.0 -. py) /. solar_mass;
        system.(0).(5) <- (0.0 -. pz) /. solar_mass
      end
    else
      let j = system.(i1) in
      offset_momentum_loop (i1 + 1)
        (px +. (j.(3) *. j.(6)))
        (py +. (j.(4) *. j.(6)))
        (pz +. (j.(5) *. j.(6)))
  in
  offset_momentum_loop 0 0.0 0.0 0.0;;

(* ------------------------------- *)
let energy () =
  let rec energy_loop_o o e =
    if o = system_size then
      e
    else
      let o1 = system.(o) in
      let sqs = (o1.(3) *. o1.(3)) +. (o1.(4) *. o1.(4)) +. (o1.(5) *. o1.(5)) in
      let e = e +. ((0.5 *. o1.(6)) *. sqs) in
      let rec energy_loop_i o o1 i e =
        if i = system_size then
          energy_loop_o (o + 1) e
        else
          let i1 = system.(i) in
          let dx = o1.(0) -. i1.(0) in
          let dy = o1.(1) -. i1.(1) in
          let dz = o1.(2) -. i1.(2) in
          let dist = sqrt ((dx *. dx) +. (dy *. dy) +. (dz *. dz)) in
          let e = e -. ((o1.(6) *. i1.(6)) /. dist) in
          energy_loop_i o o1 (i + 1) e
      in
      energy_loop_i o o1 (o + 1) e
  in
  energy_loop_o 0 0.0;;

(* ------------------------------- *)
let advance () =
  let rec advance_loop_o o =
    if o = system_size then
      ()
    else
      let o1 = system.(o) in
      let rec advance_loop_i i3 vx vy vz o1 =
        if i3 < system_size then
          let i1 = system.(i3) in
          let dx = o1.(0) -. i1.(0) in
          let dy = o1.(1) -. i1.(1) in
          let dz = o1.(2) -. i1.(2) in
          let dist2 = (dx *. dx) +. (dy *. dy) +. (dz *. dz) in
          let mag = dt /. (dist2 *. (sqrt dist2)) in
          let dxmag = dx *. mag in
          let dymag = dy *. mag in
          let dzmag = dz *. mag in
          let om = o1.(6) in
          let im = i1.(6) in
          (**)
          i1.(3) <- i1.(3) +. (dxmag *. om);
          i1.(4) <- i1.(4) +. (dymag *. om);
          i1.(5) <- i1.(5) +. (dzmag *. om);
          advance_loop_i (i3 + 1) (vx -. (dxmag *. im)) (vy -. (dymag *. im)) (vz -. (dzmag *. im)) o1
        else
          begin
            o1.(3) <- vx;
            o1.(4) <- vy;
            o1.(5) <- vz;
            o1.(0) <- o1.(0) +. (dt *. vx);
            o1.(1) <- o1.(1) +. (dt *. vy);
            o1.(2) <- o1.(2) +. (dt *. vz)
          end
      in
      (**)
      advance_loop_i (o + 1) o1.(3) o1.(4) o1.(5) o1;
      advance_loop_o (o + 1)
  in
  advance_loop_o 0;;

(* main *)
(**)
offset_momentum ();
print_float (energy ());
for i = 0 to (read_int ()) - 1 do
  advance ()
done;
print_float (energy ());;
