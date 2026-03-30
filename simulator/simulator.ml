(* Executable simulator: runs N spins and reports distribution stats. *)

open Roulette_native

let () =
  let n_spins = 1_000_000 in
  let counts = Array.make n_pockets 0 in
  for _ = 1 to n_spins do
    let raw = Random.int (n_pockets * 1000) in
    let p = rng_to_pocket raw in
    counts.(p) <- counts.(p) + 1
  done;
  let expected = float_of_int n_spins /. float_of_int n_pockets in
  let max_dev = ref 0.0 in
  for i = 0 to n_pockets - 1 do
    let dev = abs_float (float_of_int counts.(i) -. expected) in
    if dev > !max_dev then max_dev := dev
  done;
  Printf.printf "Spins: %d\n" n_spins;
  Printf.printf "Expected per pocket: %.1f\n" expected;
  Printf.printf "Max deviation: %.1f (%.3f%%)\n" !max_dev (!max_dev /. expected *. 100.0);
  Printf.printf "Fairness products:\n";
  List.iter (fun (name, b) ->
    Printf.printf "  %-12s: %d\n" name (fairness_product b))
    [ "Straight 0", Straight 0;
      "Red",        RedBet;
      "Black",      BlackBet;
      "Odd",        OddBet;
      "Even",       EvenBet;
      "Low",        LowBet;
      "High",       HighBet;
      "Column 1",   Column 1;
      "Dozen 1",    Dozen 1;
      "Basket",     Basket ]
