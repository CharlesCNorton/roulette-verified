(**  Test driver for extracted roulette code.
     Compiles and runs the extracted OCaml, verifying concrete
     evaluations match the Coq sanity-check lemmas. *)

open Roulette_extracted

(* Convert extracted nat to OCaml int *)
let rec nat_to_int = function
  | O -> 0
  | S n -> 1 + nat_to_int n

let int_to_nat n =
  let rec go n = if n <= 0 then O else S (go (n - 1)) in go n

let () =
  (* extraction_test_straight_win: simulate_spin (Straight 17) 100 17 = 3600 *)
  let r = simulate_spin (Straight (int_to_nat 17)) (int_to_nat 100) (int_to_nat 17) in
  assert (nat_to_int r = 3600);

  (* extraction_test_straight_lose: simulate_spin (Straight 17) 100 5 = 0 *)
  let r = simulate_spin (Straight (int_to_nat 17)) (int_to_nat 100) (int_to_nat 5) in
  assert (nat_to_int r = 0);

  (* extraction_test_red_win: simulate_spin RedBet 50 1 = 100 *)
  let r = simulate_spin RedBet (int_to_nat 50) (int_to_nat 1) in
  assert (nat_to_int r = 100);

  (* extraction_test_red_zero: simulate_spin RedBet 50 0 = 0 *)
  let r = simulate_spin RedBet (int_to_nat 50) (int_to_nat 0) in
  assert (nat_to_int r = 0);

  (* well_formed_dec returns true for valid bets *)
  assert (well_formed_dec (Straight (int_to_nat 0)) = True);
  assert (well_formed_dec (Straight (int_to_nat 36)) = True);
  assert (well_formed_dec (Straight (int_to_nat 37)) = False);

  (* rejection_bound 256 = 222 *)
  let rb = rejection_bound (int_to_nat 256) in
  assert (nat_to_int rb = 222);

  (* count_wins RedBet = 18 *)
  let cw = count_wins RedBet in
  assert (nat_to_int cw = 18);

  (* fairness_product RedBet = 36 (extracted as fainess_product) *)
  let fp = fainess_product RedBet in
  assert (nat_to_int fp = 36);

  Printf.printf "All extraction tests passed.\n"
