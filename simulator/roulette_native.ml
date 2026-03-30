(* Native OCaml roulette logic matching the verified Rocq specification.
   Uses machine integers for performance; validated against the extracted
   Peano code for correctness. *)

let n_pockets = 37
let n_pockets_us = 38

let color_table =
  [| 0; (* Green *)
     1; 2; 1; 2; 1; 2; 1; 2;   (* 1-8:  R B R B R B R B *)
     1; 2; 2; 1; 2; 1; 2; 1;   (* 9-16: R B B R B R B R *)
     2; 1; 1; 2; 1; 2; 1; 2;   (* 17-24: B R R B R B R B *)
     1; 2; 1; 2; 2; 1; 2; 1;   (* 25-32: R B R B B R B R *)
     2; 1; 2; 1 |]              (* 33-36: B R B R *)
(* 0=Green, 1=Red, 2=Black *)

let pocket_color n =
  if n >= 0 && n < Array.length color_table then color_table.(n)
  else 0

let is_red n = pocket_color n = 1
let is_black n = pocket_color n = 2

let rng_to_pocket raw = raw mod n_pockets

let in_street n row =
  if row < 1 || row > 12 then false
  else
    let base = (row - 1) * 3 + 1 in
    n >= base && n <= base + 2

let in_column n col =
  col >= 1 && col <= 3 && n >= 1 && n <= 36 && (n mod 3 = col mod 3)

let in_dozen n doz =
  match doz with
  | 1 -> n >= 1 && n <= 12
  | 2 -> n >= 13 && n <= 24
  | 3 -> n >= 25 && n <= 36
  | _ -> false

type bet_type =
  | Straight of int
  | Split of int * int
  | Street of int
  | Corner of int * int * int * int
  | SixLine of int * int
  | Trio of int
  | Basket
  | Column of int
  | Dozen of int
  | RedBet | BlackBet
  | OddBet | EvenBet
  | LowBet | HighBet

let bet_wins b n =
  match b with
  | Straight k -> n = k
  | Split (a, b) -> n = a || n = b
  | Street row -> in_street n row
  | Corner (a, b, c, d) -> n = a || n = b || n = c || n = d
  | SixLine (r1, r2) -> in_street n r1 || in_street n r2
  | Trio 1 -> n = 0 || n = 1 || n = 2
  | Trio 2 -> n = 0 || n = 2 || n = 3
  | Trio _ -> false
  | Basket -> n = 0 || n = 1 || n = 2 || n = 3
  | Column col -> in_column n col
  | Dozen doz -> in_dozen n doz
  | RedBet -> is_red n
  | BlackBet -> is_black n
  | OddBet -> n >= 1 && n <= 36 && n mod 2 = 1
  | EvenBet -> n >= 1 && n <= 36 && n mod 2 = 0
  | LowBet -> n >= 1 && n <= 18
  | HighBet -> n >= 19 && n <= 36

let payout_ratio b =
  match b with
  | Straight _ -> 35
  | Split _ -> 17
  | Street _ -> 11
  | Corner _ -> 8
  | SixLine _ -> 5
  | Trio _ -> 11
  | Basket -> 6
  | Column _ -> 2
  | Dozen _ -> 2
  | RedBet | BlackBet | OddBet | EvenBet | LowBet | HighBet -> 1

let net_return b stake outcome =
  if bet_wins b outcome then stake + stake * payout_ratio b
  else 0

let count_wins b =
  let c = ref 0 in
  for n = 0 to n_pockets - 1 do
    if bet_wins b n then incr c
  done;
  !c

let fairness_product b =
  count_wins b * (payout_ratio b + 1)

let expected_return_numerator b stake =
  let s = ref 0 in
  for n = 0 to n_pockets - 1 do
    s := !s + net_return b stake n
  done;
  !s
