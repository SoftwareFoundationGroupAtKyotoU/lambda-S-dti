(* NOTE: unlike the other files in this directory, the definition order here
   does not match ray.grift line-for-line. OCaml/ITGL has no forward
   references or mutual `let rec ... and ...` across top-level bindings, but
   ray.grift's functions call each other out of definition order (e.g.
   sendray -> loop -> sphere-center, defined later in the original). The
   functions below are topologically sorted (callees before callers)
   instead; block contents otherwise follow the original as closely as
   possible. *)

let make_point x y z = (x, y, z);;

let point_x p = let (x, _, _) = p in x;;
let point_y p = let (_, y, _) = p in y;;
let point_z p = let (_, _, z) = p in z;;

let sq x = x *. x;;

let mag x y z = sqrt ((sq x) +. (sq y) +. (sq z));;

let unit_vector x y z =
  let d = mag x y z in
  make_point (x /. d) (y /. d) (z /. d);;

let distance p1 p2 =
  mag (point_x p1 -. point_x p2) (point_y p1 -. point_y p2) (point_z p1 -. point_z p2);;

let world = Array.make 33 (0.0, 0.0, (0.0, 0.0, 0.0));;

let eye = make_point 0.0 0.0 200.0;;

let make_sphere color radius center = (color, radius, center);;

let sphere_color s = let (c, _, _) = s in c;;
let sphere_radius s = let (_, r, _) = s in r;;
let sphere_center s = let (_, _, c) = s in c;;

let sphere_normal s pt =
  let c = sphere_center s in
  unit_vector (point_x c -. point_x pt) (point_y c -. point_y pt) (point_z c -. point_z pt);;

let lambert s ipoint ray =
  let n = sphere_normal s ipoint in
  fmax 0.0
    ((point_x ray *. point_x n) +. (point_y ray *. point_y n) +. (point_z ray *. point_z n));;

let rec loop pt ray index lst_len lst surface hit dist =
  if index = lst_len then
    (surface, hit)
  else
    let s = lst.(index) in
    let xr = point_x ray in
    let yr = point_y ray in
    let zr = point_z ray in
    let sc = sphere_center s in
    let a = (sq xr) +. (sq yr) +. (sq zr) in
    let b = 2.0 *. (((point_x pt -. point_x sc) *. xr)
                    +. ((point_y pt -. point_y sc) *. yr)
                    +. ((point_z pt -. point_z sc) *. zr)) in
    let c = ((sq (point_x pt -. point_x sc)) +. (sq (point_y pt -. point_y sc)))
            +. ((sq (point_z pt -. point_z sc)) +. (-. (sq (sphere_radius s)))) in
    if a =. 0.0 then
      let n = (-. c) /. b in
      let h = make_point (point_x pt +. (n *. xr)) (point_y pt +. (n *. yr)) (point_z pt +. (n *. zr)) in
      let d = distance h pt in
      if d <. dist then
        loop pt ray (index + 1) lst_len lst s h d
      else
        loop pt ray (index + 1) lst_len lst surface hit dist
    else
      let disc = (sq b) -. (4.0 *. (a *. c)) in
      if disc <. 0.0 then
        loop pt ray (index + 1) lst_len lst surface hit dist
      else
        let discrt = sqrt disc in
        let minus_b = -. b in
        let two_a = 2.0 *. a in
        let n = fmin ((minus_b +. discrt) /. two_a) ((minus_b -. discrt) /. two_a) in
        let h = make_point (point_x pt +. (n *. xr)) (point_y pt +. (n *. yr)) (point_z pt +. (n *. zr)) in
        let d = distance h pt in
        if d <. dist then
          loop pt ray (index + 1) lst_len lst s h d
        else
          loop pt ray (index + 1) lst_len lst surface hit dist;;

let sendray pt ray =
  let (s, ipoint) =
    loop pt ray 0 (Array.length world) world
      (0.0, 0.0, (0.0, 0.0, 0.0)) (0.0, 0.0, 0.0) 1e308
  in
  (lambert s ipoint ray) *. (sphere_color s);;

let color_at x y =
  let ray = unit_vector (x -. point_x eye) (y -. point_y eye) (-. (point_z eye)) in
  int_of_float (round ((sendray eye ray) *. 255.0));;

let tracer res =
  let extent = res * 100 in
  (**)
  print_char 'P';
  print_int 2;
  print_char ' ';
  print_int extent;
  print_char ' ';
  print_int extent;
  print_char ' ';
  print_int 255;
  print_newline ();
  for y = 0 to extent - 1 do
    for x = 0 to extent - 1 do
      print_int (color_at (-.50.0 +. ((float_of_int x) /. (float_of_int res)))
                          (-.50.0 +. ((float_of_int y) /. (float_of_int res))));
      print_newline ()
    done
  done;;

let defsphere i x y z r c =
  let s = make_sphere c r (make_point x y z) in
  (**)
  world.(i) <- s;
  s;;

(* main *)
let res = read_int () in
(**)
ignore (defsphere 32 0.0 (-.300.0) (-.1200.0) 200.0 0.8);
ignore (defsphere 31 (-.80.0) (-.150.0) (-.1200.0) 200.0 0.7);
ignore (defsphere 30 70.0 (-.100.0) (-.1200.0) 200.0 0.9);
let counter = ref 29 in
(**)
for x = -2 to 2 do
  for z = 2 to 7 do
    (**)
    ignore (defsphere !counter ((float_of_int x) *. 200.0) 300.0 ((float_of_int z) *. (-.400.0)) 40.0 0.75);
    counter := !counter - 1
  done
done;
tracer res;;
