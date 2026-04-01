
type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

module Nat :
 sig
  val add : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val even : nat -> bool

  val odd : nat -> bool

  val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : nat -> nat -> nat list

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val n_POCKETS : nat

val rng_to_pocket : nat -> nat

type color =
| Green
| Red
| Black

val color_table : color list

val pocket_color : nat -> color

val is_red : nat -> bool

val is_black : nat -> bool

type bet_type =
| Straight of nat
| Split of nat * nat
| Street of nat
| Corner of nat * nat * nat * nat
| SixLine of nat * nat
| Trio of nat
| Basket
| FiveNumber
| Column of nat
| Dozen of nat
| RedBet
| BlackBet
| OddBet
| EvenBet
| LowBet
| HighBet

val in_column : nat -> nat -> bool

val in_dozen : nat -> nat -> bool

val in_street : nat -> nat -> bool

val bet_wins : bet_type -> nat -> bool

val payout_ratio : bet_type -> nat

val net_return : bet_type -> nat -> nat -> nat

val count_wins : bet_type -> nat

val fairness_product : bet_type -> nat

val table_adjacent_directed : nat -> nat -> bool

val table_adjacent : nat -> nat -> bool

val well_formed_dec : bet_type -> bool

val expected_return_numerator : bet_type -> nat -> nat

val rejection_bound : nat -> nat

val simulate_spin : bet_type -> nat -> nat -> nat

val simulate_session : bet_type -> nat -> nat list -> nat
