let inv_sqrt_2x_pi = 0.39894228040143270286;;

let cummulative_normal_distribution (input_x : float) =
  let sign = input_x <. 0.0 in
  let x_input = if input_x <. 0.0 then input_x *. -.1.0 else input_x in
  let exp_values = exp (-.0.5 *. (x_input *. x_input)) in
  let n_prime_of_x = exp_values *. inv_sqrt_2x_pi in
  let x_k2 = 1.0 /. (1.0 +. (0.2316419 *. x_input)) in
  let x_k2_2 = x_k2 *. x_k2 in
  let x_k2_3 = x_k2_2 *. x_k2 in
  let x_k2_4 = x_k2_3 *. x_k2 in
  let x_k2_5 = x_k2_4 *. x_k2 in
  let x1 = 0.319381530  *. x_k2 in
  let x2 = -.0.356563782 *. x_k2_2 in
  let x3 = 1.781477937  *. x_k2_3 in
  let x4 = -.1.821255978 *. x_k2_4 in
  let x5 = 1.330274429  *. x_k2_5 in
  let x = x1 +. (x5 +. (x4 +. (x2 +. x3))) in
  let x = 1.0 -. (x *. n_prime_of_x) in
  if sign then 1.0 -. x else x;;

let black_scholes (spot : float) (strike : float) (rate : float) (volatility : float) (time : float) (option_type : int) (timet : float) =
  let log = log (spot /. strike) in
  let pow = 0.5 *. (volatility *. volatility) in
  let den = volatility *. (sqrt time) in
  let d1 = (log +. (time *. (rate +. pow))) /. den in
  let d2 = d1 -. den in
  let n_of_d1 = cummulative_normal_distribution d1 in
  let n_of_d2 = cummulative_normal_distribution d2 in
  let fut_value = strike *. (exp (-.1.0 *. (rate *. time))) in
  if option_type = 0 then
    (spot *. n_of_d1) -. (fut_value *. n_of_d2)
  else
    (fut_value *. (1.0 -. n_of_d2)) -. (spot *. (1.0 -. n_of_d1));;

let make_option (spot_price : float) (strike_price : float) (rfi_rate : float) (divr : float) (volatility : float) (time : float) (option_type : char) (divs : float) (deriv_gem_value : float) =
  (spot_price, strike_price, rfi_rate, divr, volatility, time, option_type, divs, deriv_gem_value);;

let read_option_type () =
  let c = read_char () in
  if int_of_char c = int_of_char 'P' then c
  else if int_of_char c = int_of_char 'C' then c
  else if int_of_char c = int_of_char ' ' then read_char ()
  else read_char ();;

let read_option () =
  let spot_price = read_float () in
  let strike_price = read_float () in
  let rfi_rate = read_float () in
  let dividend_rate = read_float () in
  let volatility = read_float () in
  let maturity_len = read_float () in
  let option_type = read_option_type () in
  let divs = read_float () in
  let deriv_gem_value = read_float () in
  make_option spot_price strike_price rfi_rate dividend_rate volatility maturity_len option_type divs deriv_gem_value;;

let number_of_runs = 100;;

(* main *)
let number_of_options = read_int () in
let fake_data = (0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 'P', 0.0, 0.0) in
let data = Array.make number_of_options fake_data in
let spots = Array.make number_of_options 0.0 in
let strikes = Array.make number_of_options 0.0 in
let rates = Array.make number_of_options 0.0 in
let volatilities = Array.make number_of_options 0.0 in
let otypes = Array.make number_of_options 0 in
let otimes = Array.make number_of_options 0.0 in
(**)
for i = 0 to number_of_options - 1 do
  data.(i) <- read_option ()
done;
for i = 0 to number_of_options - 1 do
  let (spot, strike, rate, _, vol, time, otype, _, _) = data.(i) in
  (**)
  otypes.(i) <- (if int_of_char otype = int_of_char 'P' then 1 else 0);
  spots.(i) <- spot;
  strikes.(i) <- strike;
  rates.(i) <- rate;
  volatilities.(i) <- vol;
  otimes.(i) <- time
done;
let prices = Array.make number_of_options 0.0 in
(**)
for j = 0 to number_of_runs - 1 do
  for i = 0 to number_of_options - 1 do
    prices.(i) <- black_scholes spots.(i) strikes.(i) rates.(i) volatilities.(i) otimes.(i) otypes.(i) 0.0
  done
done;
for i = 0 to number_of_options - 1 do
  print_float prices.(i)
done;;
