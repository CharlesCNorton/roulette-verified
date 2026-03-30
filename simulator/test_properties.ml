(* QCheck property tests validating the proved theorems empirically.
   Each property corresponds to a theorem in roulette.v. *)

open Roulette_native

(* -- Generators ---------------------------------------------------- *)

let gen_pocket = QCheck.Gen.int_range 0 36

let gen_even_money_bet =
  QCheck.Gen.oneof_list [RedBet; BlackBet; OddBet; EvenBet; LowBet; HighBet]

let gen_bet =
  QCheck.Gen.oneof [
    QCheck.Gen.map (fun n -> Straight n) gen_pocket;
    QCheck.Gen.map (fun _ -> RedBet) QCheck.Gen.unit;
    QCheck.Gen.map (fun _ -> BlackBet) QCheck.Gen.unit;
    QCheck.Gen.map (fun _ -> OddBet) QCheck.Gen.unit;
    QCheck.Gen.map (fun _ -> EvenBet) QCheck.Gen.unit;
    QCheck.Gen.map (fun _ -> LowBet) QCheck.Gen.unit;
    QCheck.Gen.map (fun _ -> HighBet) QCheck.Gen.unit;
    QCheck.Gen.map (fun c -> Column c) (QCheck.Gen.int_range 1 3);
    QCheck.Gen.map (fun d -> Dozen d) (QCheck.Gen.int_range 1 3);
    QCheck.Gen.map (fun r -> Street r) (QCheck.Gen.int_range 1 12);
    QCheck.Gen.map (fun _ -> Basket) QCheck.Gen.unit;
  ]

(* -- Properties ---------------------------------------------------- *)

(* rng_to_pocket_valid: mod 37 always produces a valid pocket *)
let prop_rng_valid =
  QCheck.Test.make ~count:100_000 ~name:"rng_to_pocket_valid"
    QCheck.int (fun raw ->
      let p = rng_to_pocket (abs raw) in
      p >= 0 && p < n_pockets)

(* rng_surjective: every pocket is reachable *)
let prop_rng_surjective =
  QCheck.Test.make ~count:37 ~name:"rng_surjective"
    (QCheck.make gen_pocket) (fun n ->
      rng_to_pocket n = n)

(* straight_covers_1: each straight bet covers exactly 1 pocket *)
let prop_straight_coverage =
  QCheck.Test.make ~count:37 ~name:"straight_covers_1"
    (QCheck.make gen_pocket) (fun k ->
      count_wins (Straight k) = 1)

(* even_money_all_cover_18: every even-money bet covers 18 *)
let prop_even_money_18 =
  QCheck.Test.make ~count:1000 ~name:"even_money_covers_18"
    (QCheck.make gen_even_money_bet) (fun b ->
      count_wins b = 18)

(* fairness_product = 36 for standard bets *)
let prop_fairness_product =
  QCheck.Test.make ~count:10_000 ~name:"fairness_product_36"
    (QCheck.make gen_bet) (fun b ->
      let fp = fairness_product b in
      match b with
      | Basket -> fp = 28
      | _ -> fp = 36)

(* payout_binary: return is 0 or stake + stake*payout *)
let prop_payout_binary =
  QCheck.Test.make ~count:100_000 ~name:"payout_binary"
    QCheck.(pair (make gen_bet) (make gen_pocket)) (fun (b, outcome) ->
      let stake = 100 in
      let r = net_return b stake outcome in
      r = 0 || r = stake + stake * payout_ratio b)

(* zero_loses_outside: 0 loses all even-money bets *)
let prop_zero_loses =
  QCheck.Test.make ~count:1000 ~name:"zero_loses_outside"
    (QCheck.make gen_even_money_bet) (fun b ->
      not (bet_wins b 0))

(* house_edge: for even-money bets, losses > wins *)
let prop_house_edge =
  QCheck.Test.make ~count:1000 ~name:"house_edge"
    (QCheck.make gen_even_money_bet) (fun b ->
      n_pockets - count_wins b > count_wins b)

(* red_black_disjoint: no pocket is both red and black *)
let prop_red_black_disjoint =
  QCheck.Test.make ~count:37 ~name:"red_black_disjoint"
    (QCheck.make gen_pocket) (fun n ->
      not (is_red n && is_black n))

(* basket_fairness: Basket product = 28 *)
let prop_basket =
  QCheck.Test.make ~count:1 ~name:"basket_fairness_28"
    QCheck.unit (fun () ->
      fairness_product Basket = 28)

(* expected_return_numerator: sum of returns = fairness_product for unit stake *)
let prop_expected_return =
  QCheck.Test.make ~count:10_000 ~name:"expected_return_sum"
    (QCheck.make gen_bet) (fun b ->
      expected_return_numerator b 1 = fairness_product b)

(* uniform_distribution: over N*37 draws, each pocket gets exactly N hits *)
let prop_uniform_modular () =
  let m = 1000 in
  let total = n_pockets * m in
  let counts = Array.make n_pockets 0 in
  for v = 0 to total - 1 do
    let p = rng_to_pocket v in
    counts.(p) <- counts.(p) + 1
  done;
  Array.for_all (fun c -> c = m) counts

(* max_deviation: over any range, no two pockets differ by more than 1 *)
let prop_max_deviation () =
  let n = 10_000 in
  let counts = Array.make n_pockets 0 in
  for v = 0 to n - 1 do
    let p = rng_to_pocket v in
    counts.(p) <- counts.(p) + 1
  done;
  let mn = Array.fold_left min max_int counts in
  let mx = Array.fold_left max 0 counts in
  mx - mn <= 1

(* -- Runner -------------------------------------------------------- *)

let () =
  let ok = ref true in
  List.iter (fun t ->
    let result = QCheck.Test.check_exn t in
    ignore result)
    [ prop_rng_valid;
      prop_rng_surjective;
      prop_straight_coverage;
      prop_even_money_18;
      prop_fairness_product;
      prop_payout_binary;
      prop_zero_loses;
      prop_house_edge;
      prop_red_black_disjoint;
      prop_basket;
      prop_expected_return ];
  if not (prop_uniform_modular ()) then begin
    Printf.eprintf "FAIL: uniform_modular\n";
    ok := false
  end;
  if not (prop_max_deviation ()) then begin
    Printf.eprintf "FAIL: max_deviation\n";
    ok := false
  end;
  if !ok then
    Printf.printf "All property tests passed.\n"
  else begin
    Printf.eprintf "Some tests failed.\n";
    exit 1
  end
