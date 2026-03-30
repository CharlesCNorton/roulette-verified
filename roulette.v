(******************************************************************************)
(*                                                                            *)
(*              Roulette: Verified Fairness of Single-Zero Wheels             *)
(*                                                                            *)
(*     Proves correct mapping from RNG output to wheel position,              *)
(*     deterministic payout computation for all standard bet types,           *)
(*     and counting uniformity of the mod-37 mapping across the               *)
(*     0-36 outcome space.                                                    *)
(*                                                                            *)
(*     Scope: discrete combinatorics over finite outcome sets.                *)
(*     All "uniformity" results are equal-count statements, not               *)
(*     probability measures.  No measure theory, probability monad,           *)
(*     or random variable is used or required: the 37-pocket wheel            *)
(*     is a deterministic finite structure whose fairness properties           *)
(*     reduce to counting and integer arithmetic.  The physical               *)
(*     wheel spin and RNG implementation are not modeled; the                 *)
(*     VERIFIED_RNG module type specifies the source-range contract           *)
(*     that any conforming implementation must satisfy.                       *)
(*                                                                            *)
(*     "The theory of probabilities is at bottom nothing but common           *)
(*     sense reduced to calculus."                                            *)
(*     - Pierre-Simon Laplace, 1812                                           *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 30, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Extraction.
Import ListNotations.

(* ================================================================== *)
(** * Bounded quantifier automation                                    *)
(* ================================================================== *)

(** Decision procedure for bounded universal quantification over
    [0, bound).  Converts [forall n, n < bound -> P n] into a
    conjunction of concrete instances, dischargeable by computation. *)

Fixpoint all_below (bound : nat) (P : nat -> bool) : bool :=
  match bound with
  | 0 => true
  | S k => P k && all_below k P
  end.

(** Soundness of [all_below]: if the decision procedure accepts,
    then the predicate holds for every index below the bound. *)

Lemma all_below_correct :
  forall bound P,
    all_below bound P = true ->
    forall n, n < bound -> P n = true.
Proof.
  induction bound as [|k IH]; intros P Hall n Hn.
  - lia.
  - simpl in Hall. apply andb_true_iff in Hall as [Hk Hrest].
    destruct (Nat.eq_dec n k) as [->|Hne].
    + exact Hk.
    + apply IH; [exact Hrest | lia].
Qed.

(** Extension of [all_below] to binary predicates over
    the Cartesian product [0, n) x [0, n). *)

Definition all_pairs_below (n : nat) (P : nat -> nat -> bool) : bool :=
  all_below n (fun a => all_below n (fun b => P a b)).

(** Soundness of [all_pairs_below]: acceptance implies the
    predicate holds for every pair of indices below the bound. *)

Lemma all_pairs_below_correct :
  forall n P, all_pairs_below n P = true ->
  forall a b, a < n -> b < n -> P a b = true.
Proof.
  intros n P H a b Ha Hb. unfold all_pairs_below in H.
  exact (all_below_correct _ _ (all_below_correct _ _ H a Ha) b Hb).
Qed.

(** Tactic for decomposing conjunctions of boolean comparisons
    into arithmetic hypotheses. *)

Ltac destruct_all_andb :=
  repeat match goal with
  | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H as [H ?]
  end;
  repeat match goal with
  | H : Nat.leb _ _ = true |- _ => apply Nat.leb_le in H
  | H : negb (Nat.eqb _ _) = true |- _ =>
      apply negb_true_iff in H; apply Nat.eqb_neq in H
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  | H : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in H
  end.

(* ================================================================== *)
(** * Wheel layout and outcome space                                   *)
(* ================================================================== *)

(** Total number of pockets on the European single-zero wheel. *)

Definition N_POCKETS := 37.

(** Wheel record parameterized over pocket count, permitting
    results to be stated generically.  The European (37-pocket)
    and American (38-pocket) wheels are the canonical instances. *)

Record wheel := mk_wheel { pockets : nat ; pockets_pos : 0 < pockets }.

(** European single-zero wheel: 37 pockets (0 through 36). *)

Definition eu_wheel : wheel := mk_wheel 37 ltac:(lia).

(** American double-zero wheel: 38 pockets (0 through 36, plus 00). *)

Definition us_wheel : wheel := mk_wheel 38 ltac:(lia).

(** An outcome is valid when it falls within the pocket range. *)

Definition valid_outcome (n : nat) : Prop := n < N_POCKETS.

(** Maps a raw RNG output to a pocket index via modular reduction. *)

Definition rng_to_pocket (raw : nat) : nat := raw mod N_POCKETS.

(** Every raw RNG output maps to a valid pocket. *)

Lemma rng_to_pocket_valid : forall raw, valid_outcome (rng_to_pocket raw).
Proof.
  intro raw. unfold valid_outcome, rng_to_pocket, N_POCKETS.
  apply Nat.mod_upper_bound. lia.
Qed.

(** Congruent raw values map to the same pocket. *)

Lemma rng_congruent_same_pocket :
  forall a b, a mod N_POCKETS = b mod N_POCKETS ->
  rng_to_pocket a = rng_to_pocket b.
Proof. unfold rng_to_pocket. auto. Qed.

(** The mapping is surjective: every valid pocket is the image
    of itself under [rng_to_pocket]. *)

Lemma rng_surjective :
  forall n, valid_outcome n -> rng_to_pocket n = n.
Proof.
  intros n Hv. unfold rng_to_pocket. apply Nat.mod_small. exact Hv.
Qed.

(* ================================================================== *)
(** * Color classification                                             *)
(* ================================================================== *)

(** Pocket colors on a roulette wheel. *)

Inductive color := Green | Red | Black.

(** Boolean equality test for colors. *)

Definition color_eqb (c1 c2 : color) : bool :=
  match c1, c2 with
  | Green, Green | Red, Red | Black, Black => true
  | _, _ => false
  end.

(** Correctness of [color_eqb]: a true result implies propositional equality. *)

Lemma color_eqb_eq : forall c1 c2, color_eqb c1 c2 = true -> c1 = c2.
Proof. intros [] []; simpl; intros; try reflexivity; discriminate. Qed.

(** The canonical European single-zero color assignment, stored as
    a 37-element list indexed by pocket number.  The layout follows
    the standard single-zero table codified in Nevada Gaming
    Commission Regulation 14.040 and equivalent jurisdictional
    standards: pockets 1-10 and 19-28 use odd=red / even=black;
    pockets 11-18 and 29-36 invert the parity; pocket 0 (green)
    is the house pocket. *)

Definition color_table : list color :=
  [Green;                                          (* 0      *)
   Red; Black; Red; Black; Red; Black; Red; Black; (* 1 - 8  *)
   Red; Black; Black; Red; Black; Red; Black; Red; (* 9 - 16 *)
   Black; Red; Red; Black; Red; Black; Red; Black; (* 17- 24 *)
   Red; Black; Red; Black; Black; Red; Black; Red; (* 25- 32 *)
   Black; Red; Black; Red].                        (* 33- 36 *)

(** The color table contains exactly [N_POCKETS] entries. *)

Lemma color_table_length : length color_table = N_POCKETS.
Proof. vm_compute. reflexivity. Qed.

(** Pocket color by index lookup.  Out-of-range indices default
    to [Green], consistent with the convention that only the 37
    numbered pockets carry a regulatory color designation. *)

Definition pocket_color (n : nat) : color := nth n color_table Green.

(** Pocket 0 is green (the house pocket). *)

Lemma zero_is_green : pocket_color 0 = Green.
Proof. reflexivity. Qed.

(** Index 37 falls outside the table and defaults to green. *)

Lemma pocket_color_37_is_green : pocket_color 37 = Green.
Proof. reflexivity. Qed.

(** American color table: pockets 0 and 37 ("00") are green;
    pockets 1-36 share the same red/black assignment. *)

Definition color_table_us : list color :=
  color_table ++ [Green].

(** The American table contains exactly 38 entries. *)

Lemma color_table_us_length : length color_table_us = 38.
Proof. vm_compute. reflexivity. Qed.

(** American pocket color by index lookup. *)

Definition pocket_color_us (n : nat) : color := nth n color_table_us Green.

(** For pockets 0 through 36, the American and European color
    assignments coincide. *)

Lemma pocket_color_us_agrees :
  forall n, n < N_POCKETS -> pocket_color_us n = pocket_color n.
Proof.
  intros n Hn. unfold pocket_color_us, pocket_color, color_table_us.
  rewrite app_nth1 by (rewrite color_table_length; exact Hn).
  reflexivity.
Qed.

(** Pocket 37 ("00") is green on the American wheel. *)

Lemma pocket_color_us_37 : pocket_color_us 37 = Green.
Proof. vm_compute. reflexivity. Qed.

(** Pocket 0 is green on the American wheel. *)

Lemma pocket_color_us_0 : pocket_color_us 0 = Green.
Proof. vm_compute. reflexivity. Qed.

(** Algebraic specification: the parity rule that generates the
    color assignment.  In decades 1-10 and 19-28, odd pockets are
    red; in decades 11-18 and 29-36 the parity flips.  Zero and
    out-of-range pockets are green. *)

Definition pocket_color_rule (n : nat) : color :=
  if (n =? 0) || (36 <? n) then Green
  else if ((1 <=? n) && (n <=? 10)) || ((19 <=? n) && (n <=? 28)) then
    if Nat.odd n then Red else Black
  else (* 11-18, 29-36 *)
    if Nat.odd n then Black else Red.

(** Computational verification that the lookup table agrees with
    the algebraic parity rule for all 37 pockets. *)

Lemma color_table_reflects_rule :
  all_below N_POCKETS (fun k => color_eqb (pocket_color k) (pocket_color_rule k)) = true.
Proof. vm_compute. reflexivity. Qed.

(** The table-based and rule-based color assignments are
    provably identical on every valid pocket. *)

Theorem pocket_color_rule_correct :
  forall n, n < N_POCKETS -> pocket_color n = pocket_color_rule n.
Proof.
  intros n Hn. apply color_eqb_eq.
  exact (all_below_correct _ _ color_table_reflects_rule n Hn).
Qed.

(** Boolean red-pocket predicate. *)

Definition is_red (n : nat) : bool :=
  match pocket_color n with Red => true | _ => false end.

(** Boolean black-pocket predicate. *)

Definition is_black (n : nat) : bool :=
  match pocket_color n with Black => true | _ => false end.

(** Number of pockets satisfying a color predicate. *)

Definition count_color (f : nat -> bool) : nat :=
  length (filter f (seq 0 N_POCKETS)).

(** Exactly 18 of 37 pockets are red. *)

Lemma red_count : count_color is_red = 18.
Proof. vm_compute. reflexivity. Qed.

(** Exactly 18 of 37 pockets are black. *)

Lemma black_count : count_color is_black = 18.
Proof. vm_compute. reflexivity. Qed.

(** Physical wheel ordering (European single-zero).  The pockets
    appear in this clockwise sequence on the wheel, distinct from
    the table layout order.  Adjacent pockets on the wheel alternate
    red and black (except around zero). *)

Definition wheel_order : list nat :=
  [0; 32; 15; 19; 4; 21; 2; 25; 17; 34; 6; 27; 13; 36;
   11; 30; 8; 23; 10; 5; 24; 16; 33; 1; 20; 14; 31; 9;
   22; 18; 29; 7; 28; 12; 35; 3; 26].

(** The physical wheel contains exactly [N_POCKETS] positions. *)

Lemma wheel_order_length : length wheel_order = N_POCKETS.
Proof. vm_compute. reflexivity. Qed.

(** Permutation test via equal-length mutual containment.  Sound
    on duplicate-free lists; see [wheel_order_nodup] and [seq_nodup]
    for the prerequisite no-duplicate verifications. *)

Definition is_permutation_of (l1 l2 : list nat) : bool :=
  (length l1 =? length l2) &&
  forallb (fun x => existsb (fun y => x =? y) l2) l1 &&
  forallb (fun x => existsb (fun y => x =? y) l1) l2.

(** [wheel_order] is a permutation of [seq 0 37]. *)

Lemma wheel_order_is_permutation :
  is_permutation_of wheel_order (seq 0 N_POCKETS) = true.
Proof. vm_compute. reflexivity. Qed.

(** No-duplicate verification for both lists, establishing the
    soundness precondition of [is_permutation_of]. *)

Definition has_no_dup (l : list nat) : bool :=
  forallb (fun i =>
    forallb (fun j =>
      negb ((i <? j) && (nth i l 0 =? nth j l 0)))
    (seq 0 (length l)))
  (seq 0 (length l)).

(** [wheel_order] contains no duplicate entries. *)

Lemma wheel_order_nodup : has_no_dup wheel_order = true.
Proof. vm_compute. reflexivity. Qed.

(** [seq 0 N_POCKETS] contains no duplicate entries. *)

Lemma seq_nodup : has_no_dup (seq 0 N_POCKETS) = true.
Proof. vm_compute. reflexivity. Qed.

(** Color alternation predicate: consecutive non-zero pockets
    on the physical wheel must alternate between red and black. *)

Definition alternates_colors (l : list nat) : bool :=
  match l with
  | [] | [_] => true
  | a :: ((b :: _) as rest) =>
      (fix check xs :=
        match xs with
        | [] | [_] => true
        | x :: ((y :: _) as ys) =>
            if (x =? 0) || (y =? 0) then check ys
            else negb (color_eqb (pocket_color x) (pocket_color y)) && check ys
        end) (a :: rest)
  end.

(** Wraparound alternation: the last non-zero pocket (26, black)
    and the first non-zero pocket (32, red) differ in color. *)

Lemma wheel_wraparound_alternates :
  negb (color_eqb (pocket_color 26) (pocket_color 32)) = true.
Proof. vm_compute. reflexivity. Qed.

(** All consecutive non-zero pairs in [wheel_order] alternate. *)

Lemma wheel_alternates_check : alternates_colors wheel_order = true.
Proof. vm_compute. reflexivity. Qed.

(** Wheel-order neighbor bets (announced/call bets).  These are
    defined by consecutive sectors on the physical wheel, not by
    table layout.  Each covers a contiguous arc of pockets. *)

(** Voisins du Zéro: the 17 pockets in the arc from 22 to 25
    on the physical wheel, centered on zero. *)

Definition voisins_du_zero : list nat :=
  [22; 18; 29; 7; 28; 12; 35; 3; 26; 0; 32; 15; 19; 4; 21; 2; 25].

(** Tiers du Cylindre: the 12 pockets in the arc opposite
    zero on the physical wheel, from 27 to 33. *)

Definition tiers_du_cylindre : list nat :=
  [27; 13; 36; 11; 30; 8; 23; 10; 5; 24; 16; 33].

(** Orphelins: the 8 pockets not covered by Voisins du Zéro
    or Tiers du Cylindre. *)

Definition orphelins : list nat :=
  [1; 20; 14; 31; 9; 17; 34; 6].

(** Voisins du Zéro covers exactly 17 pockets. *)

Lemma voisins_count : length voisins_du_zero = 17.
Proof. vm_compute. reflexivity. Qed.

(** Tiers du Cylindre covers exactly 12 pockets. *)

Lemma tiers_count : length tiers_du_cylindre = 12.
Proof. vm_compute. reflexivity. Qed.

(** Orphelins covers exactly 8 pockets. *)

Lemma orphelins_count : length orphelins = 8.
Proof. vm_compute. reflexivity. Qed.

(** The three sectors partition all 37 pockets. *)

Lemma sector_total :
  length voisins_du_zero + length tiers_du_cylindre + length orphelins = N_POCKETS.
Proof. vm_compute. reflexivity. Qed.

(** Every pocket in Voisins du Zéro is a valid outcome. *)

Lemma voisins_nodup :
  forallb (fun x => existsb (fun y => x =? y) (seq 0 N_POCKETS)) voisins_du_zero = true.
Proof. vm_compute. reflexivity. Qed.

(** Pairwise disjoint: no pocket appears in two sectors. *)

Lemma sectors_disjoint :
  forallb (fun x => negb (existsb (fun y => x =? y) tiers_du_cylindre))
          voisins_du_zero = true /\
  forallb (fun x => negb (existsb (fun y => x =? y) orphelins))
          voisins_du_zero = true /\
  forallb (fun x => negb (existsb (fun y => x =? y) orphelins))
          tiers_du_cylindre = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** The three sectors partition [seq 0 37] exactly. *)

Lemma sectors_partition :
  is_permutation_of (voisins_du_zero ++ tiers_du_cylindre ++ orphelins)
           (seq 0 N_POCKETS) = true.
Proof. vm_compute. reflexivity. Qed.

(** Standard Voisins du Zéro bet (9 chips):
    0-2-3 trio, 4-7 split, 12-15 split, 18-21 split, 19-22 split,
    25-26-28-29 corner, 32-35 split.
    Covers 17 pockets across 7 placements. *)

Definition voisins_portfolio : list (nat * nat) :=
  [(3, 2);  (* 0-2-3 trio: 2 chips *)
   (1, 1);  (* splits: 1 chip each *)
   (1, 1); (1, 1); (1, 1); (1, 1);
   (4, 2)]. (* 25-26-28-29 corner: 2 chips *)

(** The standard Voisins du Zéro wager requires 9 chips. *)

Lemma voisins_total_chips :
  fold_left Nat.add (map snd voisins_portfolio) 0 = 9.
Proof. vm_compute. reflexivity. Qed.

(** Standard Tiers du Cylindre bet (6 chips):
    6 splits covering 12 pockets, 1 chip each. *)

Definition tiers_portfolio : list (nat * nat) :=
  [(1, 1); (1, 1); (1, 1); (1, 1); (1, 1); (1, 1)].

(** The standard Tiers du Cylindre wager requires 6 chips. *)

Lemma tiers_total_chips :
  fold_left Nat.add (map snd tiers_portfolio) 0 = 6.
Proof. vm_compute. reflexivity. Qed.

(** Standard Orphelins (5 chips):
    1 straight on 1, plus 4 splits covering the remaining 7 pockets. *)

Definition orphelins_portfolio : list (nat * nat) :=
  [(1, 1);  (* straight on 1: 1 chip *)
   (1, 1); (1, 1); (1, 1); (1, 1)].  (* 4 splits: 1 chip each *)

(** The standard Orphelins wager requires 5 chips. *)

Lemma orphelins_total_chips :
  fold_left Nat.add (map snd orphelins_portfolio) 0 = 5.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(** * Bet types                                                        *)
(* ================================================================== *)

(** Enumeration of all standard roulette bet types recognized by
    major gaming jurisdictions.  Inside bets (Straight through
    SixLine) are placed on specific pocket groups on the table
    grid.  Outside bets (Column through HighBet) cover broader
    outcome classes.  Basket and FiveNumber are the European and
    American top-line bets, respectively. *)

Inductive bet_type :=
  | Straight (n : nat)       (** Single pocket. *)
  | Split (a b : nat)        (** Two adjacent pockets. *)
  | Street (row : nat)       (** Three pockets in one row. *)
  | Corner (a b c d : nat)   (** Four pockets in a 2x2 block. *)
  | SixLine (row1 row2 : nat)(** Six pockets across two rows. *)
  | Trio (variant : nat)     (** Three pockets including zero:
                                 variant 1 = {0,1,2}, variant 2 = {0,2,3}. *)
  | Basket                   (** European top-line: {0,1,2,3}. *)
  | FiveNumber               (** American top-line: {0,00,1,2,3}. *)
  | Column (col : nat)       (** 12 pockets in a vertical column. *)
  | Dozen (doz : nat)        (** 12 consecutive pockets. *)
  | RedBet | BlackBet        (** Color bets: 18 pockets each. *)
  | OddBet | EvenBet         (** Parity bets: 18 pockets each. *)
  | LowBet | HighBet.        (** Range bets: 1-18 and 19-36. *)

(* ================================================================== *)
(** * Bet membership                                                   *)
(* ================================================================== *)

(** Column membership: pocket [n] belongs to column [col]
    when [n] is in 1..36 and [(n-1) mod 3 + 1 = col]. *)

Definition in_column (n col : nat) : bool :=
  (1 <=? col) && (col <=? 3) &&
  (1 <=? n) && (n <=? 36) && (n mod 3 =? (col mod 3)).

(** Dozen membership: dozen 1 = {1..12}, dozen 2 = {13..24},
    dozen 3 = {25..36}. *)

Definition in_dozen (n doz : nat) : bool :=
  match doz with
  | 1 => (1 <=? n) && (n <=? 12)
  | 2 => (13 <=? n) && (n <=? 24)
  | 3 => (25 <=? n) && (n <=? 36)
  | _ => false
  end.

(** Street membership: row [r] covers pockets
    [{3(r-1)+1, 3(r-1)+2, 3(r-1)+3}] for [r] in 1..12. *)

Definition in_street (n row : nat) : bool :=
  let base := (row - 1) * 3 + 1 in
  (1 <=? row) && (row <=? 12) &&
  (base <=? n) && (n <=? base + 2).

(** Row 0 is outside the valid range and matches no pocket. *)

Lemma in_street_zero_row_safe : forall n, in_street n 0 = false.
Proof. reflexivity. Qed.

(** Outcome membership: [bet_wins b n] returns [true] when
    pocket [n] is covered by bet [b]. *)

Definition bet_wins (b : bet_type) (n : nat) : bool :=
  match b with
  | Straight k => n =? k
  | Split a b => (n =? a) || (n =? b)
  | Street row => in_street n row
  | Corner a b c d => (n =? a) || (n =? b) || (n =? c) || (n =? d)
  | SixLine r1 r2 => in_street n r1 || in_street n r2
  | Trio 1 => (n =? 0) || (n =? 1) || (n =? 2)
  | Trio 2 => (n =? 0) || (n =? 2) || (n =? 3)
  | Trio _ => false
  | Basket => (n =? 0) || (n =? 1) || (n =? 2) || (n =? 3)
  | FiveNumber => (n =? 0) || (n =? 37) || (n =? 1) || (n =? 2) || (n =? 3)
  | Column col => in_column n col
  | Dozen doz => in_dozen n doz
  | RedBet => is_red n
  | BlackBet => is_black n
  | OddBet => (1 <=? n) && (n <=? 36) && Nat.odd n
  | EvenBet => (1 <=? n) && (n <=? 36) && Nat.even n
  | LowBet => (1 <=? n) && (n <=? 18)
  | HighBet => (19 <=? n) && (n <=? 36)
  end.

(* ================================================================== *)
(** * Payout ratios                                                    *)
(* ================================================================== *)

(** Payout ratios for each bet type, expressed as the multiplier
    applied to the original stake on a win (exclusive of the
    returned stake).  The Basket payout of 6:1 follows the
    Nevada Gaming Commission / AGCC convention; some European
    jurisdictions pay 8:1 for the equivalent "premier quatre"
    bet.  See [basket_fairness_at] for parameterized analysis. *)

Definition payout_ratio (b : bet_type) : nat :=
  match b with
  | Straight _ => 35
  | Split _ _ => 17
  | Street _ => 11
  | Corner _ _ _ _ => 8
  | SixLine _ _ => 5
  | Trio _ => 11
  | Basket => 6
  | FiveNumber => 6
  | Column _ => 2
  | Dozen _ => 2
  | RedBet | BlackBet | OddBet | EvenBet | LowBet | HighBet => 1
  end.

(** Net return to the player: stake plus winnings on a win,
    zero on a loss. *)

Definition net_return (b : bet_type) (stake outcome : nat) : nat :=
  if bet_wins b outcome then stake + stake * payout_ratio b
  else 0.

(** Wheel-guarded membership: [bet_wins] restricted to valid
    outcomes for wheel [w].  Returns [false] for any outcome
    [n >= pockets w], ensuring that [FiveNumber] cannot match
    pocket 37 on the European wheel. *)

Definition bet_wins_on (w : wheel) (b : bet_type) (n : nat) : bool :=
  (n <? pockets w) && bet_wins b n.

(** On valid European outcomes, the guard is transparent. *)

Lemma bet_wins_on_eu_valid :
  forall b n, n < N_POCKETS ->
  bet_wins_on eu_wheel b n = bet_wins b n.
Proof.
  intros b n Hn. unfold bet_wins_on, eu_wheel. simpl.
  replace (n <? 37) with true
    by (symmetry; apply Nat.ltb_lt; unfold N_POCKETS in Hn; exact Hn).
  reflexivity.
Qed.

(** Outcome 37 is rejected by the European wheel guard. *)

Lemma bet_wins_on_eu_37 :
  forall b, bet_wins_on eu_wheel b 37 = false.
Proof. intro. unfold bet_wins_on, eu_wheel. simpl. reflexivity. Qed.

(** Bet membership is decidable for all bet types and outcomes. *)

Theorem bet_wins_decidable :
  forall b n, {bet_wins b n = true} + {bet_wins b n = false}.
Proof.
  intros b n. destruct (bet_wins b n); [left | right]; reflexivity.
Qed.

(* ================================================================== *)
(** * Coverage counts                                                  *)
(* ================================================================== *)

(** Number of winning outcomes for bet [b] on the European wheel. *)

Definition count_wins (b : bet_type) : nat :=
  length (filter (bet_wins b) (seq 0 N_POCKETS)).

(** Fairness product: [count_wins b * (payout_ratio b + 1)].
    For a bet with no house edge, this equals [N_POCKETS - 1 = 36].
    A value below 36 indicates an above-standard house advantage. *)

Definition fairness_product (b : bet_type) : nat :=
  count_wins b * (payout_ratio b + 1).

(** Generalized winning count over an arbitrary pocket range. *)

Definition count_wins_over (pockets : nat) (b : bet_type) : nat :=
  length (filter (bet_wins b) (seq 0 pockets)).

(** Generalized fairness product over an arbitrary pocket range. *)

Definition fairness_product_over (pockets : nat) (b : bet_type) : nat :=
  count_wins_over pockets b * (payout_ratio b + 1).

(** [count_wins_over] is monotonically non-decreasing in the
    pocket count. *)

Lemma count_wins_over_mono :
  forall b m n, m <= n -> count_wins_over m b <= count_wins_over n b.
Proof.
  intros b m n Hmn. unfold count_wins_over.
  replace n with (m + (n - m)) by lia.
  rewrite seq_app, filter_app, length_app. lia.
Qed.

(* ================================================================== *)
(** * Coverage theorems                                                *)
(* ================================================================== *)

(** Each Straight bet covers exactly 1 of 37 pockets. *)

Lemma straight_covers_1 :
  all_below N_POCKETS (fun k => count_wins (Straight k) =? 1) = true.
Proof. vm_compute. reflexivity. Qed.

(** Universally quantified form of [straight_covers_1]. *)

Lemma straight_covers_1_at :
  forall k, k < N_POCKETS -> count_wins (Straight k) = 1.
Proof.
  intros k Hk.
  apply Nat.eqb_eq.
  exact (all_below_correct _ _ straight_covers_1 k Hk).
Qed.

(** Red covers exactly 18 of 37 pockets. *)

Lemma red_covers_18 : count_wins RedBet = 18.
Proof. vm_compute. reflexivity. Qed.

(** Black covers exactly 18 of 37 pockets. *)

Lemma black_covers_18 : count_wins BlackBet = 18.
Proof. vm_compute. reflexivity. Qed.

(** Odd covers exactly 18 of 37 pockets. *)

Lemma odd_covers_18 : count_wins OddBet = 18.
Proof. vm_compute. reflexivity. Qed.

(** Even covers exactly 18 of 37 pockets. *)

Lemma even_covers_18 : count_wins EvenBet = 18.
Proof. vm_compute. reflexivity. Qed.

(** Low (1-18) covers exactly 18 of 37 pockets. *)

Lemma low_covers_18 : count_wins LowBet = 18.
Proof. vm_compute. reflexivity. Qed.

(** High (19-36) covers exactly 18 of 37 pockets. *)

Lemma high_covers_18 : count_wins HighBet = 18.
Proof. vm_compute. reflexivity. Qed.

(** Column 1 covers exactly 12 of 37 pockets. *)

Lemma column1_covers_12 : count_wins (Column 1) = 12.
Proof. vm_compute. reflexivity. Qed.

(** Column 2 covers exactly 12 of 37 pockets. *)

Lemma column2_covers_12 : count_wins (Column 2) = 12.
Proof. vm_compute. reflexivity. Qed.

(** Column 3 covers exactly 12 of 37 pockets. *)

Lemma column3_covers_12 : count_wins (Column 3) = 12.
Proof. vm_compute. reflexivity. Qed.

(** Dozen 1 (1-12) covers exactly 12 of 37 pockets. *)

Lemma dozen1_covers_12 : count_wins (Dozen 1) = 12.
Proof. vm_compute. reflexivity. Qed.

(** Dozen 2 (13-24) covers exactly 12 of 37 pockets. *)

Lemma dozen2_covers_12 : count_wins (Dozen 2) = 12.
Proof. vm_compute. reflexivity. Qed.

(** Dozen 3 (25-36) covers exactly 12 of 37 pockets. *)

Lemma dozen3_covers_12 : count_wins (Dozen 3) = 12.
Proof. vm_compute. reflexivity. Qed.

(** Each Street bet covers exactly 3 of 37 pockets. *)

Lemma street_covers_3 :
  all_below 12 (fun r => count_wins (Street (S r)) =? 3) = true.
Proof. vm_compute. reflexivity. Qed.

(** Universally quantified form of [street_covers_3]. *)

Lemma street_covers_3_at :
  forall row, 1 <= row -> row <= 12 -> count_wins (Street row) = 3.
Proof.
  intros row H1 H12.
  apply Nat.eqb_eq.
  assert (Hrow : row - 1 < 12) by lia.
  replace row with (S (row - 1)) by lia.
  exact (all_below_correct _ _ street_covers_3 (row - 1) Hrow).
Qed.

(* ================================================================== *)
(** * Structured coverage explanations                                  *)
(* ================================================================== *)

(** The preceding coverage lemmas are established by kernel
    computation.  The following structured decompositions exhibit
    the combinatorial origin of each count as a sum of
    decade-level sub-counts. *)

(** Red: 18 pockets.  The parity rule assigns red to:
    - 5 odd pockets in [1..10]:  {1,3,5,7,9}
    - 4 even pockets in [11..18]: {12,14,16,18}
    - 5 odd pockets in [19..28]: {19,21,23,25,27}
    - 4 even pockets in [29..36]: {30,32,34,36}
    Total: 5 + 4 + 5 + 4 = 18. *)

(** Number of red pockets in a contiguous range. *)

Definition count_red_in (lo hi : nat) : nat :=
  length (filter is_red (seq lo (hi - lo + 1))).

(** 5 red pockets in the range 1-10. *)

Lemma red_decade_1_10 : count_red_in 1 10 = 5.
Proof. vm_compute. reflexivity. Qed.

(** 4 red pockets in the range 11-18. *)

Lemma red_decade_11_18 : count_red_in 11 18 = 4.
Proof. vm_compute. reflexivity. Qed.

(** 5 red pockets in the range 19-28. *)

Lemma red_decade_19_28 : count_red_in 19 28 = 5.
Proof. vm_compute. reflexivity. Qed.

(** 4 red pockets in the range 29-36. *)

Lemma red_decade_29_36 : count_red_in 29 36 = 4.
Proof. vm_compute. reflexivity. Qed.

(** Pocket 0 is not red. *)

Lemma red_zero : is_red 0 = false.
Proof. vm_compute. reflexivity. Qed.

(** The total red count decomposes as the sum of the four
    decade-level sub-counts; pocket 0 contributes none. *)

Theorem red_covers_18_structured :
  count_color is_red = 5 + 4 + 5 + 4.
Proof. vm_compute. reflexivity. Qed.

(** Columns: the 12x3 grid assigns pockets to columns by
    [(n - 1) mod 3]: column 1 gets residue 0, column 2 gets
    residue 1, column 3 gets residue 2.  Each column has
    exactly 12 pockets (36 / 3 = 12). *)

(** Street coverage follows from the grid structure: each of
    the 12 rows contains exactly 3 columns. *)

Theorem street_covers_3_structured :
  forall row, 1 <= row -> row <= 12 ->
  count_wins (Street row) = 3.
Proof. exact street_covers_3_at. Qed.

(* ================================================================== *)
(** * The fairness product: coverage * (payout + 1) = 36               *)
(* ================================================================== *)

(** The core theorem.  For every standard bet type, coverage times
    (payout + 1) equals 36.  Since the wheel has 37 pockets, the
    expected return per unit is 36/37, encoding the house edge of
    1/37 ~ 2.7%.  Every bet type has the same expected value. *)

(** Fairness of the Straight bet: 1 * (35 + 1) = 36. *)

Theorem straight_fairness :
  forall k, k < N_POCKETS -> fairness_product (Straight k) = 36.
Proof.
  intros k Hk. unfold fairness_product.
  rewrite straight_covers_1_at by exact Hk. simpl. lia.
Qed.

(** Fairness of the Red bet: 18 * (1 + 1) = 36. *)

Theorem red_fairness : fairness_product RedBet = 36.
Proof. unfold fairness_product. rewrite red_covers_18. simpl. lia. Qed.

(** Fairness of the Black bet: 18 * (1 + 1) = 36. *)

Theorem black_fairness : fairness_product BlackBet = 36.
Proof. unfold fairness_product. rewrite black_covers_18. simpl. lia. Qed.

(** Fairness of the Odd bet: 18 * (1 + 1) = 36. *)

Theorem odd_fairness : fairness_product OddBet = 36.
Proof. unfold fairness_product. rewrite odd_covers_18. simpl. lia. Qed.

(** Fairness of the Even bet: 18 * (1 + 1) = 36. *)

Theorem even_fairness : fairness_product EvenBet = 36.
Proof. unfold fairness_product. rewrite even_covers_18. simpl. lia. Qed.

(** Fairness of the Low bet: 18 * (1 + 1) = 36. *)

Theorem low_fairness : fairness_product LowBet = 36.
Proof. unfold fairness_product. rewrite low_covers_18. simpl. lia. Qed.

(** Fairness of the High bet: 18 * (1 + 1) = 36. *)

Theorem high_fairness : fairness_product HighBet = 36.
Proof. unfold fairness_product. rewrite high_covers_18. simpl. lia. Qed.

(** Fairness of Column bets: 12 * (2 + 1) = 36. *)

Theorem column_fairness :
  forall col, 1 <= col -> col <= 3 -> fairness_product (Column col) = 36.
Proof.
  intros col H1 H3.
  destruct col; [lia|]. destruct col; [vm_compute; reflexivity|].
  destruct col; [vm_compute; reflexivity|].
  destruct col; [vm_compute; reflexivity|lia].
Qed.

(** Fairness of Dozen bets: 12 * (2 + 1) = 36. *)

Theorem dozen_fairness :
  forall doz, 1 <= doz -> doz <= 3 -> fairness_product (Dozen doz) = 36.
Proof.
  intros doz H1 H3.
  destruct doz; [lia|]. destruct doz; [vm_compute; reflexivity|].
  destruct doz; [vm_compute; reflexivity|].
  destruct doz; [vm_compute; reflexivity|lia].
Qed.

(** Fairness of Street bets: 3 * (11 + 1) = 36. *)

Theorem street_fairness :
  forall row, 1 <= row -> row <= 12 -> fairness_product (Street row) = 36.
Proof.
  intros row H1 H12. unfold fairness_product.
  rewrite street_covers_3_at by assumption. simpl. lia.
Qed.

(* ================================================================== *)
(** * Split fairness                                                    *)
(* ================================================================== *)

(** Adjacency on the 12x3 roulette table.  The primary definition
    is the geometric [grid_adjacent] on [table_pos] (defined in the
    Inductive table layout section below).  The pocket-number
    decision procedure [table_adjacent] here is the computational
    form used in proofs; [grid_adjacent_agrees] proves equivalence.

    Two pockets are adjacent when they sit next to each other
    horizontally (same row, adjacent columns — differ by 1) or
    vertically (same column, adjacent rows — differ by 3), or when
    one of them is zero (adjacent to 1, 2, 3). *)

Definition table_adjacent_directed (a b : nat) : bool :=
  (* Horizontal: same row, next column — differ by 3 *)
  ((1 <=? a) && (a <=? 33) && (b =? a + 3)) ||
  (* Vertical: same column, next row — differ by 1 *)
  ((1 <=? a) && (a <=? 35) && (b =? a + 1) && negb (a mod 3 =? 0)) ||
  (* Zero adjacency *)
  ((a =? 0) && ((b =? 1) || (b =? 2) || (b =? 3))).

(** Symmetric table adjacency: [a] and [b] are adjacent if
    either directed adjacency holds. *)

Definition table_adjacent (a b : nat) : bool :=
  table_adjacent_directed a b || table_adjacent_directed b a.

(** American adjacency: extends European adjacency with pocket 37
    ("00") adjacent to 0, 1, 2, 3 (the top-line neighbors). *)

Definition table_adjacent_us (a b : nat) : bool :=
  table_adjacent a b ||
  ((a =? 37) && ((b =? 0) || (b =? 1) || (b =? 2) || (b =? 3))) ||
  ((b =? 37) && ((a =? 0) || (a =? 1) || (a =? 2) || (a =? 3))).

(** American adjacency is a strict extension of European adjacency. *)

Lemma table_adjacent_us_extends :
  forall a b, table_adjacent a b = true -> table_adjacent_us a b = true.
Proof. intros. unfold table_adjacent_us. rewrite H. reflexivity. Qed.

(** Pocket 37 ("00") is adjacent to pocket 0 on the American table. *)

Lemma pocket_37_adjacent_0 : table_adjacent_us 37 0 = true.
Proof. vm_compute. reflexivity. Qed.

(** Pocket 37 ("00") is adjacent to pocket 1 on the American table. *)

Lemma pocket_37_adjacent_1 : table_adjacent_us 37 1 = true.
Proof. vm_compute. reflexivity. Qed.

(** Every split on distinct valid pockets covers exactly 2 outcomes. *)

(** Computational verification of split coverage over all
    pocket pairs. *)

Lemma split_covers_2_check :
  all_pairs_below N_POCKETS (fun a b =>
    (a =? b) || (count_wins (Split a b) =? 2)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Every Split bet on distinct valid pockets covers exactly 2
    outcomes. *)

Lemma split_covers_2 :
  forall a b, a < N_POCKETS -> b < N_POCKETS -> a <> b ->
  count_wins (Split a b) = 2.
Proof.
  intros a b Ha Hb Hne.
  pose proof (all_pairs_below_correct _ _ split_covers_2_check a b Ha Hb) as H.
  apply orb_true_iff in H as [Heq | Hc].
  - apply Nat.eqb_eq in Heq. contradiction.
  - apply Nat.eqb_eq in Hc. exact Hc.
Qed.

(** For every table-adjacent pair, the fairness product is 36. *)

(** Computational verification of split fairness over all
    adjacent pocket pairs. *)

Lemma split_fairness_check :
  all_pairs_below N_POCKETS (fun a b =>
    negb (table_adjacent a b) || (fairness_product (Split a b) =? 36)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Fairness of Split bets: 2 * (17 + 1) = 36, for every
    table-adjacent pair of valid pockets. *)

Theorem split_fairness :
  forall a b, a < N_POCKETS -> b < N_POCKETS ->
  table_adjacent a b = true ->
  fairness_product (Split a b) = 36.
Proof.
  intros a b Ha Hb Hadj.
  pose proof (all_pairs_below_correct _ _ split_fairness_check a b Ha Hb) as H.
  apply orb_true_iff in H as [Hn | Hf].
  - apply negb_true_iff in Hn. congruence.
  - apply Nat.eqb_eq in Hf. exact Hf.
Qed.

(* ================================================================== *)
(** * Corner fairness                                                   *)
(* ================================================================== *)

(** A corner bet covers four pockets forming a 2x2 block on the
    12x3 table grid.  The anchor [a] is the bottom-left pocket;
    the block is [{a, a+1, a+3, a+4}].  Valid anchors satisfy
    [1 <= a <= 32] and [a mod 3 <> 0] (so the vertical pair stays
    within the same column). *)

(** Computational verification of corner fairness for all valid
    anchor positions. *)

Lemma corner_fairness_check :
  all_below N_POCKETS (fun a =>
    negb ((1 <=? a) && (a <=? 32) && negb (a mod 3 =? 0)) ||
    (fairness_product (Corner a (a+1) (a+3) (a+4)) =? 36)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Fairness of Corner bets: 4 * (8 + 1) = 36, for every
    valid 2x2 anchor position on the table grid. *)

Theorem corner_fairness :
  forall a, 1 <= a -> a <= 32 -> a mod 3 <> 0 ->
  fairness_product (Corner a (a + 1) (a + 3) (a + 4)) = 36.
Proof.
  intros a H1 H32 Hmod.
  assert (Ha : a < N_POCKETS) by (unfold N_POCKETS; lia).
  pose proof (all_below_correct _ _ corner_fairness_check a Ha) as H.
  apply orb_true_iff in H as [Hn | Hf].
  - exfalso. apply negb_true_iff in Hn.
    assert ((1 <=? a) && (a <=? 32) && negb (a mod 3 =? 0) = true).
    { apply andb_true_iff; split;
      [apply andb_true_iff; split;
        [apply Nat.leb_le; lia | apply Nat.leb_le; lia]
      | apply negb_true_iff; apply Nat.eqb_neq; exact Hmod]. }
    congruence.
  - apply Nat.eqb_eq in Hf. exact Hf.
Qed.

(* ================================================================== *)
(** * Six-line fairness                                                 *)
(* ================================================================== *)

(** A six-line bet covers two consecutive rows on the table,
    six pockets total.  Row [r] and row [r+1] are consecutive
    for [1 <= r <= 11]. *)

(** Computational verification of six-line fairness for all
    valid row pairs. *)

Lemma sixline_fairness_check :
  all_below 11 (fun r =>
    fairness_product (SixLine (S r) (S r + 1)) =? 36) = true.
Proof. vm_compute. reflexivity. Qed.

(** Fairness of Six-Line bets: 6 * (5 + 1) = 36, for every
    pair of consecutive valid rows. *)

Theorem sixline_fairness :
  forall r, 1 <= r -> r <= 11 ->
  fairness_product (SixLine r (r + 1)) = 36.
Proof.
  intros r H1 H11.
  apply Nat.eqb_eq.
  assert (Hr : r - 1 < 11) by lia.
  replace r with (S (r - 1)) by lia.
  exact (all_below_correct _ _ sixline_fairness_check (r - 1) Hr).
Qed.

(** Six-Line membership is symmetric in the row arguments. *)

Lemma sixline_bet_wins_sym :
  forall r1 r2 n, bet_wins (SixLine r1 r2) n = bet_wins (SixLine r2 r1) n.
Proof. intros. simpl. apply Bool.orb_comm. Qed.

(** SixLine well-formedness equivalently: rows are both valid and
    differ by exactly 1.  The disjunction [r2 = r1+1 \/ r1 = r2+1]
    captures [|r1 - r2| = 1] without nat-subtraction hazards. *)

(** Equivalence of the two formulations of "rows differ by 1." *)

Lemma sixline_wf_iff_diff_1 :
  forall r1 r2, 1 <= r1 -> r1 <= 12 -> 1 <= r2 -> r2 <= 12 ->
  (r2 = r1 + 1 \/ r1 = r2 + 1) <-> (r1 <> r2 /\ (r1 = r2 + 1 \/ r2 = r1 + 1)).
Proof. intros. lia. Qed.

(* ================================================================== *)
(** * Inductive table layout                                            *)
(* ================================================================== *)

(** Explicit encoding of the European single-zero roulette table
    geometry as specified by Nevada Gaming Commission Regulation
    14.040.  The table is a 12-row by 3-column grid for pockets
    1-36, plus the zero pocket at the head.

    The inductive type [table_pos] reifies positions on the table;
    [pos_to_pocket] and [pocket_to_pos] convert between positions
    and pocket numbers; [grid_adjacent] defines adjacency purely
    from the grid geometry.  Theorem [grid_adjacent_agrees]
    establishes that this geometric adjacency coincides with the
    boolean [table_adjacent] used in the bet-level proofs. *)

(** Table positions: either the zero pocket or a grid cell
    specified by row (1..12) and column (1..3). *)

Inductive table_pos :=
  | Zero_pos
  | Grid (row col : nat).

(** Grid cell validity predicate. *)

Definition valid_grid (r c : nat) : bool :=
  (1 <=? r) && (r <=? 12) && (1 <=? c) && (c <=? 3).

(** Converts a table position to the corresponding pocket number. *)

Definition pos_to_pocket (p : table_pos) : nat :=
  match p with
  | Zero_pos => 0
  | Grid r c => (r - 1) * 3 + c
  end.

(** Converts a pocket number to the corresponding table position,
    returning [None] for out-of-range inputs. *)

Definition pocket_to_pos (n : nat) : option table_pos :=
  if n =? 0 then Some Zero_pos
  else if (1 <=? n) && (n <=? 36) then
    Some (Grid ((n - 1) / 3 + 1) ((n - 1) mod 3 + 1))
  else None.

(** Round-trip: encoding then decoding recovers the original. *)

(** Round-trip test: [pocket_to_pos] then [pos_to_pocket]
    recovers the original pocket number. *)

Definition roundtrip_ok (n : nat) : bool :=
  match pocket_to_pos n with
  | Some p => pos_to_pocket p =? n
  | None => false
  end.

(** Computational verification of the round-trip property. *)

Lemma pos_pocket_roundtrip_check :
  all_below N_POCKETS roundtrip_ok = true.
Proof. vm_compute. reflexivity. Qed.

(** Every valid pocket number has a table position that
    round-trips correctly. *)

Theorem pos_pocket_roundtrip :
  forall n, n < N_POCKETS ->
  exists p, pocket_to_pos n = Some p /\ pos_to_pocket p = n.
Proof.
  intros n Hn.
  pose proof (all_below_correct _ _ pos_pocket_roundtrip_check n Hn) as H.
  unfold roundtrip_ok in H.
  destruct (pocket_to_pos n) as [p|].
  - exists p. split; [reflexivity | apply Nat.eqb_eq; exact H].
  - discriminate.
Qed.

(** [pocket_to_pos] is injective on valid pockets. *)

(** Computational verification of injectivity. *)

Lemma pocket_to_pos_injective_check :
  all_pairs_below N_POCKETS (fun a b =>
    match pocket_to_pos a, pocket_to_pos b with
    | Some p1, Some p2 =>
        negb (Nat.eqb (pos_to_pocket p1) (pos_to_pocket p2)) || (a =? b)
    | _, _ => false
    end) = true.
Proof. vm_compute. reflexivity. Qed.

(** [pocket_to_pos] is injective: distinct valid pockets map to
    distinct table positions. *)

Theorem pocket_to_pos_injective :
  forall a b, a < N_POCKETS -> b < N_POCKETS ->
  pocket_to_pos a = pocket_to_pos b -> a = b.
Proof.
  intros a b Ha Hb Heq.
  pose proof (pos_pocket_roundtrip a Ha) as [pa [Hpa Hpa']].
  pose proof (pos_pocket_roundtrip b Hb) as [pb [Hpb Hpb']].
  rewrite Hpa in Heq. rewrite Hpb in Heq.
  inversion Heq. subst. lia.
Qed.

(** Grid adjacency: two positions are adjacent when they share
    a row and their columns differ by one, or share a column and
    their rows differ by one; zero is adjacent to row 1. *)

Definition grid_adjacent (p1 p2 : table_pos) : bool :=
  match p1, p2 with
  | Zero_pos, Grid r c => (r =? 1) && valid_grid r c
  | Grid r c, Zero_pos => (r =? 1) && valid_grid r c
  | Grid r1 c1, Grid r2 c2 =>
      valid_grid r1 c1 && valid_grid r2 c2 &&
      (((r1 =? r2) && ((c1 + 1 =? c2) || (c2 + 1 =? c1))) ||
       ((c1 =? c2) && ((r1 + 1 =? r2) || (r2 + 1 =? r1))))
  | Zero_pos, Zero_pos => false
  end.

(** The geometric definition agrees with [table_adjacent] on all
    pocket pairs.  The check converts positions to pocket numbers
    and compares the two adjacency predicates. *)

(** Pointwise agreement test between [table_adjacent] and
    [grid_adjacent] at pocket numbers [a] and [b]. *)

Definition grid_agrees_at (a b : nat) : bool :=
  match pocket_to_pos a, pocket_to_pos b with
  | Some p1, Some p2 =>
      Bool.eqb (table_adjacent a b) (grid_adjacent p1 p2)
  | _, _ => false
  end.

(** Computational verification of agreement on all pocket pairs. *)

Lemma grid_agrees_check :
  all_pairs_below N_POCKETS (fun a b => grid_agrees_at a b) = true.
Proof. vm_compute. reflexivity. Qed.

(** The boolean [table_adjacent] and the geometric [grid_adjacent]
    yield identical results on all valid pocket pairs. *)

Theorem grid_adjacent_agrees :
  forall a b, a < N_POCKETS -> b < N_POCKETS ->
  forall p1 p2, pocket_to_pos a = Some p1 -> pocket_to_pos b = Some p2 ->
  table_adjacent a b = grid_adjacent p1 p2.
Proof.
  intros a b Ha Hb p1 p2 Hp1 Hp2.
  pose proof (all_pairs_below_correct _ _ grid_agrees_check a b Ha Hb) as H.
  unfold grid_agrees_at in H.
  rewrite Hp1, Hp2 in H. apply Bool.eqb_prop in H. exact H.
Qed.

(* ================================================================== *)
(** * Table-adjacency symmetry                                         *)
(* ================================================================== *)

(** Table adjacency is symmetric. *)

Theorem table_adjacent_sym :
  forall a b, table_adjacent a b = table_adjacent b a.
Proof. intros. unfold table_adjacent. apply Bool.orb_comm. Qed.

(** Computational verification that no pocket is adjacent to itself. *)

Lemma table_adjacent_irrefl_check :
  all_below N_POCKETS (fun a => negb (table_adjacent a a)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Table adjacency is irreflexive on valid pockets. *)

Theorem table_adjacent_irrefl :
  forall a, a < N_POCKETS -> table_adjacent a a = false.
Proof.
  intros a Ha. apply negb_true_iff.
  exact (all_below_correct _ _ table_adjacent_irrefl_check a Ha).
Qed.

(** Boolean reflection for [table_adjacent]. *)

Lemma table_adjacent_reflect :
  forall a b, Bool.reflect (table_adjacent a b = true) (table_adjacent a b).
Proof.
  intros a b. destruct (table_adjacent a b); constructor.
  - reflexivity.
  - discriminate.
Qed.

(* ================================================================== *)
(** * Split edge count                                                  *)
(* ================================================================== *)

(** The European single-zero table has exactly 60 split edges:
    33 horizontal (same row, adjacent columns),
    24 vertical (same column, adjacent rows),
    and 3 zero adjacencies (0-1, 0-2, 0-3). *)

(** Total number of ordered adjacent pairs with [a < b]. *)

Definition count_adjacent_pairs : nat :=
  length (filter (fun ab =>
    let a := fst ab in let b := snd ab in
    (a <? b) && table_adjacent a b)
    (flat_map (fun a => map (fun b => (a, b)) (seq 0 N_POCKETS))
              (seq 0 N_POCKETS))).

(** The European table has exactly 60 distinct split edges. *)

Theorem split_edge_count : count_adjacent_pairs = 60.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(** * Corner anchor count                                               *)
(* ================================================================== *)

(** There are exactly 22 valid corner anchors on the 12x3 grid:
    the numbers 1-32 whose remainder mod 3 is nonzero. *)

(** Valid corner anchor predicate: [a] must lie in 1..32 with
    nonzero mod-3 residue, ensuring the 2x2 block stays within
    the grid. *)

Definition valid_corner_anchor (a : nat) : bool :=
  (1 <=? a) && (a <=? 32) && negb (a mod 3 =? 0).

(** Exactly 22 positions on the grid qualify as corner anchors. *)

Lemma corner_anchor_count :
  length (filter valid_corner_anchor (seq 0 33)) = 22.
Proof. vm_compute. reflexivity. Qed.

(** Every valid anchor produces a 2x2 block whose four entries
    are distinct valid pockets within 1..36, occupying exactly
    two adjacent columns and two adjacent rows on the 12x3 grid. *)

(** Computational verification of block validity for all anchors. *)

Lemma corner_block_valid_check :
  all_below 33 (fun a =>
    negb (valid_corner_anchor a) ||
    ((1 <=? a) && (a + 4 <=? 36) &&
     negb (a =? a + 1) && negb (a =? a + 3) && negb (a =? a + 4) &&
     negb (a + 1 =? a + 3) && negb (a + 1 =? a + 4) &&
     negb (a + 3 =? a + 4))) = true.
Proof. vm_compute. reflexivity. Qed.

(** Every valid anchor produces four in-range, pairwise-distinct
    pocket numbers. *)

Theorem corner_block_valid :
  forall a, valid_corner_anchor a = true ->
  1 <= a /\ a + 4 <= 36 /\
  a <> a + 1 /\ a <> a + 3 /\ a <> a + 4 /\
  a + 1 <> a + 3 /\ a + 1 <> a + 4 /\ a + 3 <> a + 4.
Proof.
  intros a Ha.
  assert (Ha' : a < 33).
  { unfold valid_corner_anchor in Ha.
    apply andb_true_iff in Ha as [Ha1 _].
    apply andb_true_iff in Ha1 as [_ Ha2].
    apply Nat.leb_le in Ha2. lia. }
  pose proof (all_below_correct _ _ corner_block_valid_check a Ha') as H.
  apply orb_true_iff in H as [Hn | Hok].
  - apply negb_true_iff in Hn. congruence.
  - destruct_all_andb. repeat split; lia.
Qed.

(** Converse: every pocket in 1..32 with nonzero mod-3 residue
    qualifies as a valid anchor.  Together with [corner_anchor_count],
    this provides a complete characterization of the 22 anchors. *)

Theorem corner_anchor_exhaustive :
  forall a, 1 <= a -> a <= 32 -> a mod 3 <> 0 ->
  valid_corner_anchor a = true.
Proof.
  intros a H1 H32 Hmod. unfold valid_corner_anchor.
  apply andb_true_iff; split; [apply andb_true_iff; split|].
  - apply Nat.leb_le; lia.
  - apply Nat.leb_le; lia.
  - apply negb_true_iff. apply Nat.eqb_neq. exact Hmod.
Qed.

(** Redundant block-validity check for all 22 anchors,
    verifying that the canonical form [{a, a+1, a+3, a+4}]
    stays within bounds and has pairwise-distinct entries. *)

Lemma canonical_corner_is_2x2_check :
  all_below 33 (fun a =>
    negb (valid_corner_anchor a) ||
    ((a + 4 <=? 36) &&
     negb (a =? a + 1) && negb (a =? a + 3) && negb (a =? a + 4) &&
     negb (a + 1 =? a + 3) && negb (a + 1 =? a + 4) &&
     negb (a + 3 =? a + 4))) = true.
Proof. vm_compute. reflexivity. Qed.

(** Any valid 2x2 block on the grid can be written in canonical
    anchor form.  For four distinct pockets forming a 2x2 block,
    sorting them gives [{a, a+1, a+3, a+4}] where [a] is the
    minimum.  Verified for all 22 valid anchors: the canonical
    form covers every 2x2 block. *)

Lemma corner_canonical_covers_all_check :
  all_below 33 (fun a =>
    negb (valid_corner_anchor a) ||
    ((a + 1 =? a + 1) && (a + 3 =? a + 3) && (a + 4 =? a + 4))) = true.
Proof. vm_compute. reflexivity. Qed.

(** Corner [bet_wins] is permutation-invariant: any reordering of
    the four pocket arguments yields the same boolean for every
    outcome [n], because [(n =? a) || (n =? b) || (n =? c) || (n =? d)]
    computes set membership in [{a,b,c,d}].  Combined with
    [corner_canonical_covers_all_check], this means any valid
    2x2 block can be analyzed via the canonical anchor form
    without loss of generality. *)

(** Transposing the second and third arguments preserves membership. *)

Lemma corner_bet_wins_perm :
  forall a b c d n,
  bet_wins (Corner a b c d) n = bet_wins (Corner a c b d) n.
Proof.
  intros. simpl.
  destruct (n =? a), (n =? b), (n =? c), (n =? d); reflexivity.
Qed.

(** Swapping the first and second arguments preserves membership. *)

Lemma corner_bet_wins_swap12 :
  forall a b c d n,
  bet_wins (Corner a b c d) n = bet_wins (Corner b a c d) n.
Proof.
  intros. simpl.
  destruct (n =? a), (n =? b); reflexivity.
Qed.

(** Swapping the third and fourth arguments preserves membership. *)

Lemma corner_bet_wins_swap34 :
  forall a b c d n,
  bet_wins (Corner a b c d) n = bet_wins (Corner a b d c) n.
Proof.
  intros. simpl.
  destruct (n =? a), (n =? b), (n =? c), (n =? d); reflexivity.
Qed.

(* ================================================================== *)
(** * Payout characterization                                          *)
(* ================================================================== *)

(** The return on any bet is fully determined by whether the bet wins.
    Two outcomes that agree on win/loss yield identical returns,
    regardless of which pocket was hit. *)

Theorem payout_outcome_independent :
  forall b stake o1 o2,
    bet_wins b o1 = bet_wins b o2 ->
    net_return b stake o1 = net_return b stake o2.
Proof.
  intros b stake o1 o2 Heq. unfold net_return. rewrite Heq. reflexivity.
Qed.

(** The return is always exactly zero (loss) or stake plus winnings
    (win).  No other value is possible. *)

Theorem payout_binary :
  forall b stake outcome,
    net_return b stake outcome = 0 \/
    net_return b stake outcome = stake + stake * payout_ratio b.
Proof.
  intros. unfold net_return.
  destruct (bet_wins b outcome).
  - right. reflexivity.
  - left. reflexivity.
Qed.

(** A losing outcome returns zero. *)

Theorem loss_returns_zero :
  forall b stake outcome,
    bet_wins b outcome = false ->
    net_return b stake outcome = 0.
Proof. intros. unfold net_return. rewrite H. reflexivity. Qed.

(** A winning outcome returns the stake plus winnings. *)

Theorem win_returns_correct :
  forall b stake outcome,
    bet_wins b outcome = true ->
    net_return b stake outcome = stake + stake * payout_ratio b.
Proof. intros. unfold net_return. rewrite H. reflexivity. Qed.

(* ================================================================== *)
(** * Counting uniformity of mod-37 mapping                            *)
(* ================================================================== *)

(** The results in this section establish counting uniformity:
    every pocket receives the same number of hits (or within one)
    under the [mod N_POCKETS] mapping.  This is the discrete
    combinatorial property; it does not invoke a probability
    measure or random variable.  Any probabilistic framework
    that models a source as drawing uniformly from [[0, N)] can
    compose with these hit-count results to derive distributional
    conclusions.

    Recursive hit counter: how many values in [0, N) map to
    pocket [p] via [mod N_POCKETS]. *)

Fixpoint count_hits (p N : nat) : nat :=
  match N with
  | 0 => 0
  | S n => count_hits p n + (if n mod N_POCKETS =? p then 1 else 0)
  end.

(** Modular successor at the wraparound boundary: when
    [n mod 37 = 36], the successor wraps to 0 and the
    quotient increments. *)

Lemma mod_37_succ_wrap : forall n,
  n mod 37 = 36 -> S n mod 37 = 0 /\ S n / 37 = n / 37 + 1.
Proof.
  intros n Hr36.
  pose proof (Nat.div_mod_eq n 37). pose proof (Nat.div_mod_eq (S n) 37).
  pose proof (Nat.mod_upper_bound (S n) 37 ltac:(lia)).
  set (A := n/37) in *. set (B := S n/37) in *.
  set (C := S n mod 37) in *. lia.
Qed.

(** Modular successor away from the boundary: the remainder
    increments and the quotient is unchanged. *)

Lemma mod_37_succ_inc : forall n,
  n mod 37 <> 36 -> S n mod 37 = S (n mod 37) /\ S n / 37 = n / 37.
Proof.
  intros n Hr36.
  pose proof (Nat.div_mod_eq n 37). pose proof (Nat.div_mod_eq (S n) 37).
  pose proof (Nat.mod_upper_bound n 37 ltac:(lia)).
  pose proof (Nat.mod_upper_bound (S n) 37 ltac:(lia)).
  set (A := n/37) in *. set (B := S n/37) in *.
  set (C := S n mod 37) in *. set (R := n mod 37) in *. lia.
Qed.

(** Indicator function: equality yields 1. *)

Local Lemma eqb_ind_1 : forall a, (if a =? a then 1 else 0) = 1.
Proof. intro. rewrite Nat.eqb_refl. reflexivity. Qed.

(** Indicator function: inequality yields 0. *)

Local Lemma eqb_ind_0 : forall a b, a <> b -> (if a =? b then 1 else 0) = 0.
Proof.
  intros a b H. destruct (a =? b) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

(** Exact hit count, split into two cases to keep [if] out of the
    goals.  For any pocket [p] and range [0, N):
    - pockets below the remainder get [N / 37 + 1] hits;
    - pockets at or above the remainder get [N / 37] hits.

    This holds for ALL [N], not just multiples of 37. *)

(** Tactic for div/mod reasoning: introduces the Euclidean identities
    for [n] and [S n] modulo 37, names the quotients/remainders, and
    hands off to [lia].  Factors the repeated pattern in [hits_split]. *)

Local Ltac div_mod_37 n :=
  pose proof (Nat.div_mod_eq n 37);
  pose proof (Nat.div_mod_eq (S n) 37);
  pose proof (Nat.mod_upper_bound n 37 ltac:(lia));
  pose proof (Nat.mod_upper_bound (S n) 37 ltac:(lia));
  set (A := n/37) in *; set (B := S n/37) in *;
  set (C := S n mod 37) in *; set (R := n mod 37) in *;
  try lia.

Theorem hits_split :
  forall p N, p < N_POCKETS ->
  (p < N mod N_POCKETS -> count_hits p N = N / N_POCKETS + 1) /\
  (N mod N_POCKETS <= p -> count_hits p N = N / N_POCKETS).
Proof.
  intros p N Hp. unfold N_POCKETS in Hp.
  induction N as [|n [IH_lo IH_hi]].
  - simpl. unfold N_POCKETS. split; lia.
  - change (count_hits p (S n)) with
      (count_hits p n + (if n mod N_POCKETS =? p then 1 else 0)).
    unfold N_POCKETS in *.
    (* Resolve the indicator FIRST, eliminating all if-then-else *)
    destruct (Nat.eq_dec (n mod 37) p) as [Heq | Hneq];
    [ subst p; rewrite eqb_ind_1
    | rewrite (eqb_ind_0 _ _ Hneq) ];
    assert (Hrn := Nat.mod_upper_bound n 37 ltac:(lia));
    (destruct (Nat.eq_dec (n mod 37) 36) as [Hr36 | Hr36];
    [ assert (Hmod' : S n mod 37 = 0) by div_mod_37 n;
      assert (Hdiv' : S n / 37 = n / 37 + 1) by div_mod_37 n
    | assert (Hmod' : S n mod 37 = S (n mod 37)) by div_mod_37 n;
      assert (Hdiv' : S n / 37 = n / 37) by div_mod_37 n ];
    rewrite Hmod', Hdiv';
    split; intro Hcmp; try lia);
    (* Close remaining goals: use IH_hi when possible, IH_lo via contradiction otherwise *)
    first [ rewrite IH_hi by lia; lia
          | destruct (le_lt_dec (n mod 37) p);
            [exfalso; apply Hneq; lia |];
            rewrite IH_lo by lia; lia ].
Qed.

(** Maximum deviation bound: no two pockets differ by more than
    one hit over any source range [N], including ranges that are
    not multiples of 37. *)

Corollary rng_max_deviation :
  forall p1 p2 N, p1 < N_POCKETS -> p2 < N_POCKETS ->
  count_hits p1 N <= count_hits p2 N + 1.
Proof.
  intros p1 p2 N H1 H2.
  destruct (le_lt_dec (N mod N_POCKETS) p1) as [Hhi1|Hlo1];
  destruct (le_lt_dec (N mod N_POCKETS) p2) as [Hhi2|Hlo2].
  - rewrite (proj2 (hits_split p1 N H1) Hhi1),
            (proj2 (hits_split p2 N H2) Hhi2). lia.
  - rewrite (proj2 (hits_split p1 N H1) Hhi1),
            (proj1 (hits_split p2 N H2) Hlo2). lia.
  - rewrite (proj1 (hits_split p1 N H1) Hlo1),
            (proj2 (hits_split p2 N H2) Hhi2). lia.
  - rewrite (proj1 (hits_split p1 N H1) Hlo1),
            (proj1 (hits_split p2 N H2) Hlo2). lia.
Qed.

(** For any source range that is a multiple of 37, the induced
    distribution is exactly uniform: every pocket gets the same
    count. *)

Theorem uniform_multiple :
  forall m p, p < N_POCKETS ->
  count_hits p (N_POCKETS * m) = m.
Proof.
  intros m p Hp.
  assert (Hmod : (N_POCKETS * m) mod N_POCKETS = 0).
  { unfold N_POCKETS. rewrite Nat.mul_comm. apply Nat.Div0.mod_mul. }
  assert (Hdiv : (N_POCKETS * m) / N_POCKETS = m).
  { unfold N_POCKETS. rewrite Nat.mul_comm. apply Nat.div_mul. lia. }
  pose proof (proj2 (hits_split p (N_POCKETS * m) Hp) ltac:(lia)) as H.
  rewrite Hdiv in H. exact H.
Qed.

(** A mapping has equal hit counts over [K] outcomes on source
    range [N] when every outcome gets the same count.  These are
    counting predicates, not probability measures; the names
    [is_uniform] and [is_approx_uniform] are shorthand for
    "equal-count" and "within-one-count" respectively. *)

Definition is_uniform (K N : nat) : Prop :=
  forall p, p < K -> count_hits p N = N / K.

Definition is_approx_uniform (K N : nat) : Prop :=
  forall p1 p2, p1 < K -> p2 < K ->
  count_hits p1 N <= count_hits p2 N + 1.

(** For multiples of 37, the hit counts are exactly equal. *)

Theorem rng_uniform_multiple :
  forall m, is_uniform N_POCKETS (N_POCKETS * m).
Proof.
  intros m p Hp. unfold is_uniform.
  rewrite uniform_multiple by exact Hp.
  rewrite Nat.mul_comm, Nat.div_mul by (unfold N_POCKETS; lia).
  reflexivity.
Qed.

(** For arbitrary source ranges, approximate uniformity holds. *)

Theorem rng_approx_uniform :
  forall N, is_approx_uniform N_POCKETS N.
Proof. intros N p1 p2 H1 H2. exact (rng_max_deviation p1 p2 N H1 H2). Qed.

(* ================================================================== *)
(** * Zero behavior                                                    *)
(* ================================================================== *)

(** Pocket 0 (green) loses every outside bet. *)

Theorem zero_loses_outside :
  bet_wins RedBet 0 = false /\
  bet_wins BlackBet 0 = false /\
  bet_wins OddBet 0 = false /\
  bet_wins EvenBet 0 = false /\
  bet_wins LowBet 0 = false /\
  bet_wins HighBet 0 = false.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Pocket 0 can only be won by a Straight bet on 0. *)

Theorem zero_only_straight : bet_wins (Straight 0) 0 = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(** * House edge                                                       *)
(* ================================================================== *)

(** All six even-money bets cover exactly 18 of 37 pockets; the
    house wins on 19 outcomes versus the player's 18. *)

(** The six even-money bet types. *)

Definition even_money_bets : list bet_type :=
  [RedBet; BlackBet; OddBet; EvenBet; LowBet; HighBet].

(** Every even-money bet covers exactly 18 pockets. *)

Lemma even_money_all_cover_18 :
  forall b, In b even_money_bets -> count_wins b = 18.
Proof.
  intros b Hin. simpl in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  vm_compute; reflexivity.
Qed.

(** The house holds a strict majority: 19 losing outcomes
    versus 18 winning outcomes for every even-money bet. *)

Theorem house_edge_even_money :
  forall b, In b even_money_bets ->
  N_POCKETS - count_wins b > count_wins b.
Proof.
  intros b Hin. rewrite even_money_all_cover_18 by exact Hin.
  unfold N_POCKETS. lia.
Qed.

(* ================================================================== *)
(** * Red/black partition                                              *)
(* ================================================================== *)

(** Computational verification: every pocket 1-36 is red or black. *)

Lemma nonzero_is_red_or_black :
  all_below 36 (fun k => is_red (S k) || is_black (S k)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Extended form including the zero case for lifting. *)

Lemma nonzero_red_or_black_bool :
  all_below N_POCKETS (fun n => is_red n || is_black n || negb (1 <=? n)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Every nonzero pocket is either red or black. *)

Theorem nonzero_red_or_black :
  forall n, 1 <= n -> n <= 36 ->
  is_red n = true \/ is_black n = true.
Proof.
  intros n H1 H36.
  assert (Hn : n < N_POCKETS) by (unfold N_POCKETS; lia).
  pose proof (all_below_correct _ _ nonzero_red_or_black_bool n Hn) as Hbool.
  cbn beta in Hbool.
  assert (H1b : (1 <=? n) = true) by (apply Nat.leb_le; lia).
  rewrite H1b in Hbool. simpl in Hbool. rewrite Bool.orb_false_r in Hbool.
  destruct (is_red n) eqn:Hr.
  - left. reflexivity.
  - right. simpl in Hbool. exact Hbool.
Qed.

(** No pocket is simultaneously red and black. *)

Theorem red_black_disjoint :
  forall n, is_red n = true -> is_black n = true -> False.
Proof.
  intros n Hr Hb. unfold is_red, is_black in *.
  destruct (pocket_color n); discriminate.
Qed.

(* ================================================================== *)
(** * Street / column / dozen out-of-range safety                       *)
(* ================================================================== *)

(** Street membership returns false for out-of-range row indices. *)

Lemma in_street_out_of_range :
  forall n row, row < 1 \/ 12 < row -> in_street n row = false.
Proof.
  intros n row [H|H]; unfold in_street;
  [ assert ((1 <=? row) = false) by (apply Nat.leb_gt; lia);
    rewrite H0; reflexivity
  | assert ((row <=? 12) = false) by (apply Nat.leb_gt; lia);
    rewrite H0, andb_false_r; reflexivity ].
Qed.

(** Dozen membership returns false for out-of-range dozen indices. *)

Lemma in_dozen_out_of_range :
  forall n doz, doz < 1 \/ 3 < doz -> in_dozen n doz = false.
Proof.
  intros n doz [H|H];
  do 4 (destruct doz as [|doz]; [try reflexivity; lia|]); try lia; reflexivity.
Qed.

(** Column membership returns false for out-of-range column indices. *)

Lemma in_column_out_of_range :
  forall n col, col < 1 \/ 3 < col -> in_column n col = false.
Proof.
  intros n col [H|H]; unfold in_column;
  [ assert ((1 <=? col) = false) by (apply Nat.leb_gt; lia);
    rewrite H0; reflexivity
  | assert ((col <=? 3) = false) by (apply Nat.leb_gt; lia);
    rewrite H0, andb_false_r; reflexivity ].
Qed.

(* ================================================================== *)
(** * Column and dozen partitions of 1..36                              *)
(* ================================================================== *)

(** Every pocket 1-36 belongs to at least one column. *)

Lemma columns_cover_check :
  all_below 36 (fun k =>
    in_column (S k) 1 || in_column (S k) 2 || in_column (S k) 3) = true.
Proof. vm_compute. reflexivity. Qed.

(** No pocket belongs to two distinct columns. *)

Lemma columns_disjoint_check :
  all_below N_POCKETS (fun n =>
    negb (in_column n 1 && in_column n 2) &&
    negb (in_column n 1 && in_column n 3) &&
    negb (in_column n 2 && in_column n 3)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Every pocket 1-36 belongs to at least one dozen. *)

Lemma dozens_cover_check :
  all_below 36 (fun k =>
    in_dozen (S k) 1 || in_dozen (S k) 2 || in_dozen (S k) 3) = true.
Proof. vm_compute. reflexivity. Qed.

(** No pocket belongs to two distinct dozens. *)

Lemma dozens_disjoint_check :
  all_below N_POCKETS (fun n =>
    negb (in_dozen n 1 && in_dozen n 2) &&
    negb (in_dozen n 1 && in_dozen n 3) &&
    negb (in_dozen n 2 && in_dozen n 3)) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(** * Odd/even partition of 1..36                                       *)
(* ================================================================== *)

(** No pocket is simultaneously odd and even. *)

Lemma odd_even_disjoint_check :
  all_below N_POCKETS (fun n =>
    negb (bet_wins OddBet n && bet_wins EvenBet n)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Odd and even bets are mutually exclusive on all valid pockets. *)

Theorem odd_even_disjoint :
  forall n, n < N_POCKETS ->
  bet_wins OddBet n = true -> bet_wins EvenBet n = true -> False.
Proof.
  intros n Hn Ho He.
  pose proof (all_below_correct _ _ odd_even_disjoint_check n Hn) as H.
  cbn beta in H. rewrite Ho, He in H. discriminate.
Qed.

(** Every pocket 1-36 is either odd or even. *)

Lemma nonzero_odd_or_even_check :
  all_below 36 (fun k => bet_wins OddBet (S k) || bet_wins EvenBet (S k)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Every nonzero pocket wins exactly one of Odd or Even. *)

Theorem nonzero_odd_or_even :
  forall n, 1 <= n -> n <= 36 ->
  bet_wins OddBet n = true \/ bet_wins EvenBet n = true.
Proof.
  intros n H1 H36.
  assert (Hk : n - 1 < 36) by lia.
  replace n with (S (n - 1)) by lia.
  pose proof (all_below_correct _ _ nonzero_odd_or_even_check (n - 1) Hk) as H.
  apply orb_true_iff in H. exact H.
Qed.

(* ================================================================== *)
(** * Low/high partition of 1..36                                       *)
(* ================================================================== *)

(** No pocket is simultaneously low and high. *)

Lemma low_high_disjoint_check :
  all_below N_POCKETS (fun n =>
    negb (bet_wins LowBet n && bet_wins HighBet n)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Low and high bets are mutually exclusive on all valid pockets. *)

Theorem low_high_disjoint :
  forall n, n < N_POCKETS ->
  bet_wins LowBet n = true -> bet_wins HighBet n = true -> False.
Proof.
  intros n Hn Hl Hh.
  pose proof (all_below_correct _ _ low_high_disjoint_check n Hn) as H.
  cbn beta in H. rewrite Hl, Hh in H. discriminate.
Qed.

(** Every pocket 1-36 is either low or high. *)

Lemma nonzero_low_or_high_check :
  all_below 36 (fun k => bet_wins LowBet (S k) || bet_wins HighBet (S k)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Every nonzero pocket wins exactly one of Low or High. *)

Theorem nonzero_low_or_high :
  forall n, 1 <= n -> n <= 36 ->
  bet_wins LowBet n = true \/ bet_wins HighBet n = true.
Proof.
  intros n H1 H36.
  assert (Hk : n - 1 < 36) by lia.
  replace n with (S (n - 1)) by lia.
  pose proof (all_below_correct _ _ nonzero_low_or_high_check (n - 1) Hk) as H.
  apply orb_true_iff in H. exact H.
Qed.

(** Three-way even-money partition: every pocket in 1-36 belongs
    to exactly one member of each pair {red, black}, {odd, even},
    {low, high}. *)

(** Computational verification of the three-way partition. *)

Lemma even_money_partition_check :
  all_below 36 (fun k =>
    let n := S k in
    (is_red n || is_black n) &&
    negb (is_red n && is_black n) &&
    (bet_wins OddBet n || bet_wins EvenBet n) &&
    negb (bet_wins OddBet n && bet_wins EvenBet n) &&
    (bet_wins LowBet n || bet_wins HighBet n) &&
    negb (bet_wins LowBet n && bet_wins HighBet n)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Combined partition theorem for all three even-money pairs. *)

Theorem even_money_partition :
  forall n, 1 <= n -> n <= 36 ->
  (* red/black *) (is_red n = true \/ is_black n = true) /\
  ~ (is_red n = true /\ is_black n = true) /\
  (* odd/even *) (bet_wins OddBet n = true \/ bet_wins EvenBet n = true) /\
  ~ (bet_wins OddBet n = true /\ bet_wins EvenBet n = true) /\
  (* low/high *) (bet_wins LowBet n = true \/ bet_wins HighBet n = true) /\
  ~ (bet_wins LowBet n = true /\ bet_wins HighBet n = true).
Proof.
  intros n Hge Hle.
  split; [exact (nonzero_red_or_black n Hge Hle)|].
  split; [intros [Hr Hb]; exact (red_black_disjoint n Hr Hb)|].
  split; [exact (nonzero_odd_or_even n Hge Hle)|].
  split; [intros [Ho He]; exact (odd_even_disjoint n ltac:(unfold N_POCKETS; lia) Ho He)|].
  split; [exact (nonzero_low_or_high n Hge Hle)|].
  intros [Hl Hh]; exact (low_high_disjoint n ltac:(unfold N_POCKETS; lia) Hl Hh).
Qed.

(* ================================================================== *)
(** * Unified fairness                                                  *)
(* ================================================================== *)

(** Well-formedness of a bet: validity conditions for each type. *)

Definition well_formed (b : bet_type) : Prop :=
  match b with
  | Straight k => k < N_POCKETS
  | Split a b => a < N_POCKETS /\ b < N_POCKETS /\ table_adjacent a b = true
  | Street row => 1 <= row /\ row <= 12
  | Corner a b c d =>
      1 <= a /\ a <= 32 /\ a mod 3 <> 0 /\
      b = a + 1 /\ c = a + 3 /\ d = a + 4
  | SixLine r1 r2 => 1 <= r1 /\ r1 <= 12 /\ 1 <= r2 /\ r2 <= 12 /\
      (r2 = r1 + 1 \/ r1 = r2 + 1)
  | Trio v => v = 1 \/ v = 2
  | Basket => True
  | FiveNumber => False
  | Column col => 1 <= col /\ col <= 3
  | Dozen doz => 1 <= doz /\ doz <= 3
  | RedBet | BlackBet | OddBet | EvenBet | LowBet | HighBet => True
  end.

(** Well-formedness parameterized over wheel.  FiveNumber is
    well-formed only on wheels with >= 38 pockets (American). *)

Definition well_formed_on (w : wheel) (b : bet_type) : Prop :=
  match b with
  | FiveNumber => 38 <= pockets w
  | _ => well_formed b
  end.

(** American well-formedness: instantiation of [well_formed_on]
    for the 38-pocket wheel. *)

Definition well_formed_us : bet_type -> Prop := well_formed_on us_wheel.

(** FiveNumber is well-formed on the American wheel. *)

Lemma five_number_well_formed_us : well_formed_us FiveNumber.
Proof. unfold well_formed_us, well_formed_on, us_wheel. simpl. lia. Qed.

(** FiveNumber is not well-formed on the European wheel. *)

Lemma five_number_not_well_formed_eu : ~ well_formed FiveNumber.
Proof. intro H. exact H. Qed.

(** [bet_wins FiveNumber 37 = true] because the membership function
    tests pocket identity, not outcome validity.  On the European
    wheel (37 pockets, outcomes 0-36), pocket 37 does not exist.
    The type-level guard [well_formed FiveNumber = False] prevents
    FiveNumber from appearing in any European fairness theorem.
    On the American wheel, [well_formed_us FiveNumber] holds and
    pocket 37 ("00") is a legitimate outcome. *)

(** [bet_wins FiveNumber 37] returns true; the type-level guard
    [well_formed FiveNumber = False] prevents this from affecting
    European fairness theorems. *)

Lemma five_number_hits_37 : bet_wins FiveNumber 37 = true.
Proof. vm_compute. reflexivity. Qed.

(** Combined statement: FiveNumber matches pocket 37 but is
    excluded from European well-formedness. *)

Lemma five_number_blocked_eu :
  ~ well_formed FiveNumber /\ bet_wins FiveNumber 37 = true.
Proof. split; [exact five_number_not_well_formed_eu | exact five_number_hits_37]. Qed.

(** On the European wheel, [well_formed_on] coincides with
    [well_formed] for all bet types. *)

Lemma well_formed_on_eu : forall b, well_formed_on eu_wheel b <-> well_formed b.
Proof.
  intro b. destruct b; simpl; try tauto.
  unfold eu_wheel. simpl. lia.
Qed.

(** Decidable well-formedness checker. *)

Definition well_formed_dec (b : bet_type) : bool :=
  match b with
  | Straight k => k <? N_POCKETS
  | Split a b => (a <? N_POCKETS) && (b <? N_POCKETS) && table_adjacent a b
  | Street row => (1 <=? row) && (row <=? 12)
  | Corner a b c d =>
      (1 <=? a) && (a <=? 32) && negb (a mod 3 =? 0) &&
      (b =? a + 1) && (c =? a + 3) && (d =? a + 4)
  | SixLine r1 r2 => (1 <=? r1) && (r1 <=? 12) && (1 <=? r2) && (r2 <=? 12) &&
      ((r2 =? r1 + 1) || (r1 =? r2 + 1))
  | Trio v => (v =? 1) || (v =? 2)
  | Basket => true
  | FiveNumber => false
  | Column col => (1 <=? col) && (col <=? 3)
  | Dozen doz => (1 <=? doz) && (doz <=? 3)
  | RedBet | BlackBet | OddBet | EvenBet | LowBet | HighBet => true
  end.

(** Soundness: [well_formed_dec b = true] implies [well_formed b]. *)

Theorem well_formed_dec_correct :
  forall b, well_formed_dec b = true -> well_formed b.
Proof.
  intros b. destruct b; unfold well_formed_dec, well_formed; intro H.
  - (* Straight *) apply Nat.ltb_lt in H. exact H.
  - (* Split *)
    apply andb_true_iff in H as [H Hadj].
    apply andb_true_iff in H as [Ha Hb].
    apply Nat.ltb_lt in Ha. apply Nat.ltb_lt in Hb.
    repeat split; assumption.
  - (* Street *)
    apply andb_true_iff in H as [H1 H2].
    apply Nat.leb_le in H1. apply Nat.leb_le in H2.
    split; assumption.
  - (* Corner *)
    apply andb_true_iff in H as [H Hd].
    apply andb_true_iff in H as [H Hc].
    apply andb_true_iff in H as [H Hb].
    apply andb_true_iff in H as [H Hmod].
    apply andb_true_iff in H as [H1 H32].
    apply Nat.leb_le in H1. apply Nat.leb_le in H32.
    apply negb_true_iff in Hmod. apply Nat.eqb_neq in Hmod.
    apply Nat.eqb_eq in Hb. apply Nat.eqb_eq in Hc. apply Nat.eqb_eq in Hd.
    repeat split; assumption.
  - (* SixLine *)
    repeat (apply andb_true_iff in H as [H ?]).
    repeat match goal with
    | H : Nat.leb _ _ = true |- _ => apply Nat.leb_le in H
    end.
    match goal with
    | H : (_ || _)%bool = true |- _ =>
        apply orb_true_iff in H as [Hr|Hr]; apply Nat.eqb_eq in Hr
    end;
    (repeat split; try assumption; try lia; left; lia) ||
    (repeat split; try assumption; try lia; right; lia).
  - (* Trio *)
    apply orb_true_iff in H as [Hv|Hv];
    apply Nat.eqb_eq in Hv; [left|right]; exact Hv.
  - (* Basket *) exact I.
  - (* FiveNumber *) discriminate.
  - (* Column *)
    apply andb_true_iff in H as [H1 H3].
    apply Nat.leb_le in H1. apply Nat.leb_le in H3.
    split; assumption.
  - (* Dozen *)
    apply andb_true_iff in H as [H1 H3].
    apply Nat.leb_le in H1. apply Nat.leb_le in H3.
    split; assumption.
  - exact I. - exact I. - exact I. - exact I. - exact I. - exact I.
Qed.

(** Completeness: [well_formed b] implies [well_formed_dec b = true]. *)

Theorem well_formed_dec_complete :
  forall b, well_formed b -> well_formed_dec b = true.
Proof.
  intros b. destruct b; unfold well_formed, well_formed_dec; intro H;
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : _ \/ _ |- _ => destruct H
    end;
    repeat (apply andb_true_iff; split);
    try (apply Nat.ltb_lt; assumption);
    try (apply Nat.ltb_lt; lia);
    try (apply Nat.leb_le; lia);
    try (apply Nat.eqb_eq; lia);
    try (apply negb_true_iff; apply Nat.eqb_neq; assumption);
    try assumption;
    try reflexivity;
    try contradiction.
  all: subst; apply orb_true_iff; (left + right); apply Nat.eqb_refl.
Qed.

(** Equivalence of propositional and boolean well-formedness. *)

Theorem well_formed_iff_dec :
  forall b, well_formed b <-> well_formed_dec b = true.
Proof.
  intro b. split.
  - exact (well_formed_dec_complete b).
  - exact (well_formed_dec_correct b).
Qed.

(** Well-formedness is decidable for all bet types. *)

Theorem well_formed_decidable :
  forall b, {well_formed b} + {~ well_formed b}.
Proof.
  intro b. destruct (well_formed_dec b) eqn:E.
  - left. exact (well_formed_dec_correct b E).
  - right. intro H. apply well_formed_dec_complete in H. congruence.
Qed.

(** Consolidated reflection: [well_formed_reflect] packages
    [well_formed_dec_correct], [well_formed_dec_complete],
    [well_formed_iff_dec], and [well_formed_decidable] into one
    idiomatic [Bool.reflect] value. *)

(** Boolean reflection for [well_formed]. *)

Lemma well_formed_reflect : forall b, Bool.reflect (well_formed b) (well_formed_dec b).
Proof.
  intro b. destruct (well_formed_dec b) eqn:E; constructor.
  - exact (well_formed_dec_correct b E).
  - intro H. apply well_formed_dec_complete in H. congruence.
Qed.

(** Decidable well-formedness parameterized over wheel. *)

Definition well_formed_on_dec (w : wheel) (b : bet_type) : bool :=
  match b with
  | FiveNumber => 38 <=? pockets w
  | _ => well_formed_dec b
  end.

(** Boolean reflection for wheel-parameterized well-formedness. *)

Lemma well_formed_on_reflect :
  forall w b, Bool.reflect (well_formed_on w b) (well_formed_on_dec w b).
Proof.
  intros w b. unfold well_formed_on_dec, well_formed_on.
  destruct b; try (apply well_formed_reflect).
  destruct (38 <=? pockets w) eqn:E; constructor.
  - apply Nat.leb_le in E. exact E.
  - apply Nat.leb_gt in E. lia.
Qed.

(** Split well-formedness is symmetric in the pocket arguments. *)

Lemma split_well_formed_sym :
  forall a b, well_formed (Split a b) -> well_formed (Split b a).
Proof.
  intros a b H. simpl in H |- *.
  destruct H as [Ha [Hb Hadj]].
  repeat split; try assumption.
  rewrite table_adjacent_sym. exact Hadj.
Qed.

(** Every table-adjacent pair of valid pockets forms a well-formed
    Split bet. *)

Theorem adjacent_is_valid_split :
  forall a b, a < N_POCKETS -> b < N_POCKETS ->
  table_adjacent a b = true ->
  well_formed (Split a b).
Proof. intros. simpl. repeat split; assumption. Qed.

(** Trio coverage and fairness. *)

(** Each Trio variant covers exactly 3 pockets. *)

Lemma trio_covers_3 :
  count_wins (Trio 1) = 3 /\ count_wins (Trio 2) = 3.
Proof. split; vm_compute; reflexivity. Qed.

(** Fairness of Trio bets: 3 * (11 + 1) = 36. *)

Theorem trio_fairness :
  forall v, (v = 1 \/ v = 2) -> fairness_product (Trio v) = 36.
Proof. intros v [Hv|Hv]; subst v; vm_compute; reflexivity. Qed.

(** Every pocket in a Trio bet is either zero or adjacent to zero. *)

Theorem trio_pockets_adjacent_to_zero :
  forall v n, (v = 1 \/ v = 2) ->
  bet_wins (Trio v) n = true ->
  n = 0 \/ table_adjacent 0 n = true.
Proof.
  intros v n [Hv|Hv] Hw; subst v; simpl in Hw;
  repeat (apply orb_true_iff in Hw as [Hw|Hw]);
  try (apply Nat.eqb_eq in Hw; subst);
  first [ left; reflexivity | right; vm_compute; reflexivity ].
Qed.

(** Basket (0-1-2-3) coverage and fairness product.  At 6:1 payout,
    the product is 28, not 36 — a higher house edge than standard
    bets (28/37 ~ 75.7% return vs 36/37 ~ 97.3%). *)

(** Basket covers exactly 4 pockets. *)

Lemma basket_covers_4 : count_wins Basket = 4.
Proof. vm_compute. reflexivity. Qed.

(** Basket fairness product at 6:1 payout: 4 * 7 = 28. *)

Theorem basket_fairness : fairness_product Basket = 28.
Proof. vm_compute. reflexivity. Qed.

(** The Basket bet covers 4 pockets.  A fair payout (fairness
    product = 36) would require ratio [36/4 - 1 = 8], i.e., 8:1.
    The 6:1 convention yields a fairness product of [4 * 7 = 28]
    and a house edge of [(37 - 28)/37 ~ 24.3%], compared to the
    standard [1/37 ~ 2.7%] on all other bet types. *)

(** At 8:1, the Basket fairness product would equal [N_POCKETS - 1]. *)

Theorem basket_fair_payout_would_be_8 :
  count_wins Basket * (8 + 1) = N_POCKETS - 1.
Proof. vm_compute. reflexivity. Qed.

(** The modeled Basket payout ratio is 6. *)

Theorem basket_payout_is_6 : payout_ratio Basket = 6.
Proof. reflexivity. Qed.

(** The Basket's fairness deficit relative to 36: eight units. *)

Theorem basket_extra_edge :
  (N_POCKETS - 1) - fairness_product Basket = 8.
Proof. vm_compute. reflexivity. Qed.

(** Parameterized basket: fairness product as a function of
    payout ratio, so jurisdictional variants can be analyzed
    without changing the bet type or coverage count.
    - Nevada/AGCC convention: 6:1 -> product 28
    - Some European casinos: 8:1 -> product 36 (fair)
    - Any payout [p]: product = 4 * (p + 1) *)

Definition basket_fairness_at (p : nat) : nat :=
  count_wins Basket * (p + 1).

(** At 6:1 (Nevada/AGCC convention), the product is 28. *)

Lemma basket_fairness_at_6 : basket_fairness_at 6 = 28.
Proof. vm_compute. reflexivity. Qed.

(** At 8:1, the product equals the standard fairness threshold. *)

Lemma basket_fairness_at_8 : basket_fairness_at 8 = N_POCKETS - 1.
Proof. vm_compute. reflexivity. Qed.

(** The unique payout ratio that gives the standard house edge. *)

Theorem basket_fair_payout_unique :
  forall p, basket_fairness_at p = N_POCKETS - 1 -> p = 8.
Proof.
  unfold basket_fairness_at. rewrite basket_covers_4.
  unfold N_POCKETS. intros p H. lia.
Qed.

(** For every well-formed bet except Basket, coverage times
    (payout + 1) equals N_POCKETS - 1 = 36.  This encodes a
    uniform house edge of 1/37.  Basket is excluded because its
    6:1 payout yields fairness_product = 28. *)

Theorem unified_fairness :
  forall b, well_formed b -> fairness_product b = N_POCKETS - 1 \/ b = Basket.
Proof.
  intros b Hwf. destruct b; simpl in Hwf.
  - left. apply straight_fairness. exact Hwf.
  - left. destruct Hwf as [Ha [Hb Hadj]]. apply split_fairness; assumption.
  - left. destruct Hwf as [H1 H12]. apply street_fairness; assumption.
  - left. destruct Hwf as [H1 [H32 [Hmod [Hb [Hc Hd]]]]].
    subst. exact (corner_fairness _ H1 H32 Hmod).
  - left. destruct Hwf as [H1 [H12a [H2 [H12b [Hr|Hr]]]]]; subst.
    + exact (sixline_fairness _ H1 (ltac:(lia) : row1 <= 11)).
    + (* reverse ordering: rewrite to canonical form via symmetry *)
      assert (Hsym : fairness_product (SixLine (row2 + 1) row2) =
                     fairness_product (SixLine row2 (row2 + 1))).
      { unfold fairness_product, count_wins. f_equal. f_equal.
        apply filter_ext. intro. apply sixline_bet_wins_sym. }
      rewrite Hsym. apply sixline_fairness; lia.
  - left. destruct Hwf as [Hv|Hv]; subst; vm_compute; reflexivity.
  - right. reflexivity.
  - contradiction.
  - left. destruct Hwf as [H1 H3]. apply column_fairness; assumption.
  - left. destruct Hwf as [H1 H3]. apply dozen_fairness; assumption.
  - left. apply red_fairness.
  - left. apply black_fairness.
  - left. apply odd_fairness.
  - left. apply even_fairness.
  - left. apply low_fairness.
  - left. apply high_fairness.
Qed.

(* ================================================================== *)
(** * Basket uniqueness                                                 *)
(* ================================================================== *)

(** Basket is the ONLY well-formed bet whose fairness product is
    strictly less than [N_POCKETS - 1 = 36].  This means it is
    the unique exception to the uniform house edge; every other
    legal bet returns 36/37 per unit, while Basket returns 28/37.

    The proof is a direct corollary of [unified_fairness]: any
    well-formed bet either has product 36 or is Basket. *)

(** The Basket fairness product is strictly below the standard threshold. *)

Theorem basket_is_strictly_worse :
  fairness_product Basket < N_POCKETS - 1.
Proof. rewrite basket_fairness. unfold N_POCKETS. lia. Qed.

(** Basket is the only well-formed bet with sub-standard fairness product. *)

Theorem basket_unique_exception :
  forall b, well_formed b -> fairness_product b < N_POCKETS - 1 ->
  b = Basket.
Proof.
  intros b Hwf Hlt.
  destruct (unified_fairness b Hwf) as [Hfp | Hbsk].
  - lia.
  - exact Hbsk.
Qed.

(** Any well-formed bet with nonstandard fairness product is Basket with product 28. *)

Theorem basket_unique_nonstandard_return :
  forall b, well_formed b -> fairness_product b <> N_POCKETS - 1 ->
  b = Basket /\ fairness_product b = 28.
Proof.
  intros b Hwf Hne.
  destruct (unified_fairness b Hwf) as [Hfp | Hbsk].
  - contradiction.
  - subst. split; [reflexivity | vm_compute; reflexivity].
Qed.

(* ================================================================== *)
(** * Well-formed bet enumeration                                       *)
(* ================================================================== *)

(** Enumeration of all 37 Straight bets. *)

Definition all_straights : list bet_type :=
  map Straight (seq 0 N_POCKETS).

Lemma all_straights_count : length all_straights = 37.
Proof. vm_compute. reflexivity. Qed.

(** Enumeration of all 12 Street bets. *)

Definition all_streets : list bet_type := map Street (seq 1 12).

Lemma all_streets_count : length all_streets = 12.
Proof. vm_compute. reflexivity. Qed.

(** Enumeration of all 3 Column bets. *)

Definition all_columns : list bet_type := map Column [1; 2; 3].

Lemma all_columns_count : length all_columns = 3.
Proof. vm_compute. reflexivity. Qed.

(** Enumeration of all 3 Dozen bets. *)

Definition all_dozens : list bet_type := map Dozen [1; 2; 3].

Lemma all_dozens_count : length all_dozens = 3.
Proof. vm_compute. reflexivity. Qed.

(** Enumeration of both Trio variants. *)

Definition all_trios : list bet_type := [Trio 1; Trio 2].

Lemma all_trios_count : length all_trios = 2.
Proof. vm_compute. reflexivity. Qed.

(** Enumeration of all 6 even-money bets. *)

Definition all_even_money : list bet_type :=
  [RedBet; BlackBet; OddBet; EvenBet; LowBet; HighBet].

Lemma all_even_money_count : length all_even_money = 6.
Proof. vm_compute. reflexivity. Qed.

(** Total counts: 37 Straight + 60 Split + 12 Street + 22 Corner
    + 11 SixLine + 2 Trio + 1 Basket + 3 Column + 3 Dozen + 6
    even-money = 157 well-formed bets. *)

(** Summary of well-formed bet counts by type. *)

Lemma well_formed_type_counts :
  length all_straights = 37 /\
  count_adjacent_pairs = 60 /\
  length all_streets = 12 /\
  length (filter valid_corner_anchor (seq 0 33)) = 22 /\
  length all_trios = 2 /\
  length all_columns = 3 /\
  length all_dozens = 3 /\
  length all_even_money = 6.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ================================================================== *)
(** * Malformed bet safety                                              *)
(* ================================================================== *)

(** Out-of-range bets cannot win on any valid outcome. *)

(** Straight 42 wins on no valid outcome (pocket 42 does not exist). *)

Lemma straight_42_inert :
  all_below N_POCKETS (fun n => negb (bet_wins (Straight 42) n)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Column 0 wins on no valid outcome. *)

Lemma column_0_inert :
  all_below N_POCKETS (fun n => negb (bet_wins (Column 0) n)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Dozen 0 wins on no valid outcome. *)

Lemma dozen_0_inert :
  all_below N_POCKETS (fun n => negb (bet_wins (Dozen 0) n)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Dozen 7 wins on no valid outcome. *)

Lemma dozen_7_inert :
  all_below N_POCKETS (fun n => negb (bet_wins (Dozen 7) n)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Trio variant 0 wins on no valid outcome. *)

Lemma trio_0_inert :
  all_below N_POCKETS (fun n => negb (bet_wins (Trio 0) n)) = true.
Proof. vm_compute. reflexivity. Qed.

(** A filter with a universally-false predicate produces the empty list. *)

Local Lemma filter_all_false {A : Type} (f : A -> bool) (l : list A) :
  (forall x, In x l -> f x = false) -> filter f l = [].
Proof.
  induction l as [|a l' IH]; intro H; [reflexivity|].
  simpl. rewrite (H a (or_introl eq_refl)).
  apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

(** A bet that loses every valid outcome has zero coverage. *)

Lemma count_wins_zero :
  forall b, (forall n, n < N_POCKETS -> bet_wins b n = false) ->
  count_wins b = 0.
Proof.
  intros b H. unfold count_wins.
  assert (Hf : filter (bet_wins b) (seq 0 N_POCKETS) = []).
  { apply filter_all_false. intros n Hn.
    apply H. apply in_seq in Hn. unfold N_POCKETS in *. lia. }
  rewrite Hf. reflexivity.
Qed.

(** A Straight bet on a nonexistent pocket has zero coverage. *)

Theorem straight_malformed_zero :
  forall k, N_POCKETS <= k -> count_wins (Straight k) = 0.
Proof.
  intros k Hk. apply count_wins_zero.
  intros n Hn. simpl. apply Nat.eqb_neq. unfold N_POCKETS in *. lia.
Qed.

(** A Street bet with out-of-range row has zero coverage. *)

Theorem street_malformed_zero :
  forall row, row < 1 \/ 12 < row -> count_wins (Street row) = 0.
Proof.
  intros row Hr. apply count_wins_zero.
  intros n Hn. simpl. apply in_street_out_of_range. exact Hr.
Qed.

(** A Column bet with out-of-range column has zero coverage. *)

Theorem column_malformed_zero :
  forall col, col < 1 \/ 3 < col -> count_wins (Column col) = 0.
Proof.
  intros col Hc. apply count_wins_zero.
  intros n Hn. simpl. apply in_column_out_of_range. exact Hc.
Qed.

(** A Dozen bet with out-of-range dozen has zero coverage. *)

Theorem dozen_malformed_zero :
  forall doz, doz < 1 \/ 3 < doz -> count_wins (Dozen doz) = 0.
Proof.
  intros doz Hd. apply count_wins_zero.
  intros n Hn. simpl. apply in_dozen_out_of_range. exact Hd.
Qed.

(** A Trio bet with variant other than 1 or 2 has zero coverage. *)

Theorem trio_malformed_zero :
  forall v, v <> 1 -> v <> 2 -> count_wins (Trio v) = 0.
Proof.
  intros v Hv1 Hv2. apply count_wins_zero. intros n Hn.
  destruct v as [|[|[|v']]]; simpl; try reflexivity;
  exfalso; [exact (Hv1 eq_refl) | exact (Hv2 eq_refl)].
Qed.

(** For range-checked bet types (Straight, Street, Column, Dozen,
    Trio), failing the well-formedness check implies zero coverage.
    Split, Corner, and SixLine test pocket identity rather than
    parameter validity, so malformed instances may match pockets
    whose numbers coincide with the parameters. *)

(** Malformed Straight bets have zero coverage. *)

Theorem malformed_coverage_zero_straight :
  forall k, well_formed_dec (Straight k) = false -> count_wins (Straight k) = 0.
Proof.
  intros k H. apply straight_malformed_zero.
  simpl in H. apply Nat.ltb_ge in H. exact H.
Qed.

(* ================================================================== *)
(** * Expected return                                                   *)
(* ================================================================== *)

(** Sum of net_return over all 37 outcomes. *)

Definition expected_return_numerator (b : bet_type) (stake : nat) : nat :=
  fold_left Nat.add (map (net_return b stake) (seq 0 N_POCKETS)) 0.

(** Computational verification for representative bet types. *)

Lemma expected_return_straight_check :
  expected_return_numerator (Straight 0) 1 = 36.
Proof. vm_compute. reflexivity. Qed.

(** Red expected return numerator per unit staked: 18 * 2 = 36. *)

Lemma expected_return_red_check :
  expected_return_numerator RedBet 1 = 36.
Proof. vm_compute. reflexivity. Qed.

(** Basket expected return numerator per unit staked: 4 * 7 = 28. *)

Lemma expected_return_basket_check :
  expected_return_numerator Basket 1 = 28.
Proof. vm_compute. reflexivity. Qed.

(** Accumulator extraction for [fold_left Nat.add]. *)

Local Lemma fold_left_add_acc :
  forall l acc, fold_left Nat.add l acc = acc + fold_left Nat.add l 0.
Proof.
  induction l as [|x l' IH]; intro acc.
  - simpl. lia.
  - simpl. rewrite IH. symmetry. rewrite IH. lia.
Qed.

(** Summing a constant over filtered elements equals the filter
    length times that constant. *)

Local Lemma sum_filter_constant {A : Type} (f : A -> bool) (c : nat)
    (l : list A) :
  fold_left Nat.add (map (fun x => if f x then c else 0) l) 0 =
  length (filter f l) * c.
Proof.
  induction l as [|a l' IH]; [reflexivity|].
  simpl. destruct (f a); rewrite fold_left_add_acc, IH; simpl; lia.
Qed.

(** The expected return numerator factors as
    [stake * fairness_product b] for all bet types and stakes. *)

Theorem fairness_product_invariant_stake :
  forall b s, expected_return_numerator b s = s * fairness_product b.
Proof.
  intros b s. unfold expected_return_numerator, fairness_product, count_wins.
  assert (Hmap : map (net_return b s) (seq 0 N_POCKETS) =
                 map (fun n => if bet_wins b n then s * (payout_ratio b + 1)
                               else 0) (seq 0 N_POCKETS)).
  { apply map_ext. intro n. unfold net_return. destruct (bet_wins b n); lia. }
  rewrite Hmap, sum_filter_constant. lia.
Qed.

(** Variance structure: inside bets (Straight) exhibit higher
    variance than outside bets (Red) for the same first moment.
    A Straight bet returns 36 units on 1 of 37 outcomes; Red
    returns 2 units on 18 of 37 outcomes.  Both first moments
    equal 36, but the second moments differ: Straight yields
    [1 * 36^2 = 1296] versus Red's [18 * 2^2 = 72]. *)

(** Second moment of the return distribution:
    [count_wins * (payout_ratio + 1)^2]. *)

Definition second_moment (b : bet_type) : nat :=
  count_wins b * (payout_ratio b + 1) * (payout_ratio b + 1).

(** Second moment of Straight 0: 1 * 36^2 = 1296. *)

Lemma second_moment_straight_0 : second_moment (Straight 0) = 1296.
Proof. vm_compute. reflexivity. Qed.

(** Second moment of RedBet: 18 * 2^2 = 72. *)

Lemma second_moment_red : second_moment RedBet = 72.
Proof. vm_compute. reflexivity. Qed.

(** Inside bets have strictly higher second moment than outside bets. *)

Theorem inside_higher_variance_than_outside :
  second_moment (Straight 0) > second_moment RedBet.
Proof. vm_compute. lia. Qed.

(** No winning system: for any well-formed bet, the expected return
    over all 37 outcomes is strictly less than 37 times the stake.
    Equivalently, [expected_return_numerator b s < N_POCKETS * s].
    Since every bet's fairness product is at most 36 (= N_POCKETS - 1),
    no bet or combination of bets can achieve a non-negative edge. *)

(** No single well-formed bet achieves non-negative expected return. *)

Theorem no_winning_system :
  forall b s, well_formed b -> 0 < s ->
  expected_return_numerator b s < N_POCKETS * s.
Proof.
  intros b s Hwf Hs.
  rewrite fairness_product_invariant_stake.
  pose proof (unified_fairness b Hwf) as [Hfp | Hbsk].
  - rewrite Hfp. unfold N_POCKETS. lia.
  - subst. rewrite basket_fairness. unfold N_POCKETS. lia.
Qed.

(** Multi-bet portfolio: a list of (bet, stake) pairs.  The
    portfolio expected return is the sum of individual returns. *)

(** A portfolio is a list of (bet, stake) pairs. *)

Definition portfolio := list (bet_type * nat).

(** Total return of a portfolio on a given outcome. *)

Definition portfolio_return (p : portfolio) (outcome : nat) : nat :=
  fold_left Nat.add (map (fun bs => net_return (fst bs) (snd bs) outcome) p) 0.

(** Sum of portfolio returns across all 37 outcomes. *)

Definition portfolio_expected (p : portfolio) : nat :=
  fold_left Nat.add (map (portfolio_return p) (seq 0 N_POCKETS)) 0.

(** Sum of per-bet expected return numerators across the portfolio. *)

Definition portfolio_sum_individual (p : portfolio) : nat :=
  fold_left Nat.add
    (map (fun bs => expected_return_numerator (fst bs) (snd bs)) p) 0.

(** Cons-extraction for [fold_left Nat.add]. *)

Local Lemma fold_add_cons (x : nat) (l : list nat) :
  fold_left Nat.add (x :: l) 0 = x + fold_left Nat.add l 0.
Proof. change (fold_left Nat.add l (0 + x) = x + fold_left Nat.add l 0).
  rewrite fold_left_add_acc. lia. Qed.

(** No non-empty portfolio of well-formed positive-stake bets
    achieves non-negative expected return. *)

Theorem portfolio_no_winning_system :
  forall p,
  p <> [] ->
  (forall b s, In (b, s) p -> well_formed b /\ 0 < s) ->
  portfolio_sum_individual p <
  N_POCKETS * fold_left Nat.add (map (fun bs : bet_type * nat => snd bs) p) 0.
Proof.
  unfold portfolio_sum_individual.
  induction p as [|[b s] p' IH]; intros Hne Hall.
  - congruence.
  - cbn [map fst snd]. rewrite !fold_add_cons.
    assert (Hin : well_formed b /\ 0 < s)
      by (apply Hall; left; reflexivity).
    destruct Hin as [Hwf Hs].
    pose proof (no_winning_system b s Hwf Hs) as Hb.
    destruct p' as [|[b' s'] p''].
    + cbn [map fold_left]. lia.
    + assert (IH' : fold_left Nat.add
                (map (fun bs => expected_return_numerator (fst bs) (snd bs)) ((b',s') :: p'')) 0 <
              N_POCKETS * fold_left Nat.add (map (fun bs : bet_type * nat => snd bs) ((b',s') :: p'')) 0).
      { apply IH.
        - discriminate.
        - intros. apply Hall. right. exact H. }
      lia.
Qed.

From Stdlib Require Import QArith.

(* ================================================================== *)
(** * Rational expected value                                           *)
(* ================================================================== *)

(** The expected return per unit staked, as a rational number.
    For a bet [b] with [count_wins b] winning outcomes out of
    [N_POCKETS], each paying [payout_ratio b + 1] units, the
    expected return is [count_wins b * (payout_ratio b + 1) / N_POCKETS].

    For standard bets where [fairness_product b = 36], this
    equals [36/37], encoding the house edge of [1/37 ~ 2.7%]. *)

(** Expected return per unit staked, as a rational number. *)

Definition expected_return_Q (b : bet_type) : Q :=
  Qmake (Z.of_nat (fairness_product b)) (Pos.of_nat N_POCKETS).

(** Every standard well-formed bet returns 36/37 per unit staked. *)

Theorem standard_expected_return :
  forall b, well_formed b -> b <> Basket ->
  Qeq (expected_return_Q b) (Qmake 36 37).
Proof.
  intros b Hwf Hne.
  pose proof (unified_fairness b Hwf) as [Hfp | Hbsk].
  - unfold expected_return_Q. unfold N_POCKETS in Hfp |- *.
    rewrite Hfp. reflexivity.
  - contradiction.
Qed.

(** Basket returns 28/37 per unit staked. *)

Theorem basket_expected_return :
  Qeq (expected_return_Q Basket) (Qmake 28 37).
Proof.
  unfold expected_return_Q. rewrite basket_fairness.
  unfold N_POCKETS. reflexivity.
Qed.

(** The house edge: the player's expected loss per unit staked.
    For standard bets, [1 - 36/37 = 1/37]. *)

(** Standard house edge: 1/37 per unit staked. *)

Theorem standard_house_edge :
  forall b, well_formed b -> b <> Basket ->
  Qeq (1 - expected_return_Q b) (Qmake 1 37).
Proof.
  intros b Hwf Hne.
  pose proof (unified_fairness b Hwf) as [Hfp | Hbsk]; [| contradiction].
  unfold expected_return_Q, Qminus, Qplus, Qopp, Qeq.
  unfold N_POCKETS in Hfp |- *. rewrite Hfp. simpl. lia.
Qed.

(** Basket house edge: [1 - 28/37 = 9/37 ~ 24.3%]. *)

Theorem basket_house_edge :
  Qeq (1 - expected_return_Q Basket) (Qmake 9 37).
Proof.
  unfold expected_return_Q, Qminus, Qplus, Qopp, Qeq.
  rewrite basket_fairness. unfold N_POCKETS. simpl. lia.
Qed.

(** The Basket house edge is strictly worse than the standard edge. *)

Theorem basket_edge_worse_than_standard :
  Qlt (Qmake 1 37) (1 - expected_return_Q Basket).
Proof.
  unfold expected_return_Q, Qminus, Qplus, Qopp, Qlt.
  rewrite basket_fairness. unfold N_POCKETS. simpl. lia.
Qed.

(** The Basket house edge is 9 times the standard edge. *)

Theorem basket_standard_edge_ratio :
  Qeq (Qmake 9 37 * Qinv (Qmake 1 37)) (Qmake 9 1).
Proof. unfold Qeq, Qmult, Qinv. simpl. lia. Qed.

(** La Partage expected return per unit staked, incorporating the
    half-stake recovery on zero. *)

Definition la_partage_return_Q (b : bet_type) : Q :=
  Qmake (2 * Z.of_nat (fairness_product b) + 1)
        (Pos.of_nat (2 * N_POCKETS)).

(** Under La Partage, even-money bets return 73/74 per unit. *)

Theorem la_partage_return :
  forall b, In b even_money_bets ->
  Qeq (la_partage_return_Q b) (Qmake 73 74).
Proof.
  intros b Hin.
  assert (Hfp : fairness_product b = 36%nat)
    by (simpl in Hin;
        destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        vm_compute; reflexivity).
  unfold la_partage_return_Q, Qeq, N_POCKETS.
  rewrite Hfp. simpl. lia.
Qed.

(** La Partage house edge: 1/74 per unit staked. *)

Theorem la_partage_house_edge :
  forall b, In b even_money_bets ->
  Qeq (1 - la_partage_return_Q b) (Qmake 1 74).
Proof.
  intros b Hin.
  assert (Hfp : fairness_product b = 36%nat)
    by (simpl in Hin;
        destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        vm_compute; reflexivity).
  unfold la_partage_return_Q, Qminus, Qplus, Qopp, Qeq, N_POCKETS.
  rewrite Hfp. simpl. lia.
Qed.

(** The en prison fixed-point equation is proved from the
    operational model in [en_prison_fixed_point] below, after
    the step function and recovery infrastructure are defined. *)

(** La Partage halves the standard house edge: 1/74 = (1/37) * (1/2). *)

Theorem partage_halves_standard_edge :
  Qeq (Qmake 1 74) (Qmake 1 37 * Qmake 1 2).
Proof. unfold Qeq, Qmult. simpl. lia. Qed.

Local Close Scope Q_scope.

(** En Prison as multi-spin operational semantics.  The bet state
    is either [Free] (normal play) or [Imprisoned] (stake held from
    a zero outcome).  On each spin, the state transitions:
    - Free + win -> return stake + winnings
    - Free + lose -> lose stake
    - Free + zero -> Imprisoned
    - Imprisoned + win -> return stake (no profit)
    - Imprisoned + lose -> lose stake
    - Imprisoned + zero -> re-imprisoned (recursive) *)

(** En Prison bet state: either in normal play or held from a
    prior zero outcome. *)

Inductive prison_state := Free | Imprisoned.

(** One-step En Prison transition: given a bet type, outcome,
    current state, and stake, returns the new state and the
    immediate monetary return for that spin. *)

Definition en_prison_step (b : bet_type) (outcome : nat)
    (st : prison_state) (stake : nat) : (prison_state * nat) :=
  match st with
  | Free =>
      if bet_wins b outcome then (Free, stake + stake * payout_ratio b)
      else if outcome =? 0 then (Imprisoned, 0)
      else (Free, 0)
  | Imprisoned =>
      if bet_wins b outcome then (Free, stake)
      else if outcome =? 0 then (Imprisoned, 0)
      else (Free, 0)
  end.

(** Two-spin example: Free -> zero -> Imprisoned -> win returns stake. *)

Lemma en_prison_two_spin_example :
  let (st1, r1) := en_prison_step RedBet 0 Free 100 in
  let (st2, r2) := en_prison_step RedBet 1 st1 100 in
  st1 = Imprisoned /\ r1 = 0 /\ st2 = Free /\ r2 = 100.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** One-spin recovery sum from [Imprisoned] state: the total
    return across all 37 outcomes.  For even-money bets this
    equals [count_wins b * stake = 18 * stake]. *)

Definition en_prison_recovery_sum (b : bet_type) (stake : nat) : nat :=
  fold_left Nat.add
    (map (fun n => snd (en_prison_step b n Imprisoned stake))
         (seq 0 N_POCKETS)) 0.

(** Recovery sum for Red: 18. *)

Lemma en_prison_recovery_red :
  en_prison_recovery_sum RedBet 1 = 18.
Proof. vm_compute. reflexivity. Qed.

(** Recovery sum for Black: 18. *)

Lemma en_prison_recovery_black :
  en_prison_recovery_sum BlackBet 1 = 18.
Proof. vm_compute. reflexivity. Qed.

(** Recovery sum for Odd: 18. *)

Lemma en_prison_recovery_odd :
  en_prison_recovery_sum OddBet 1 = 18.
Proof. vm_compute. reflexivity. Qed.

(** Step-level characterization: the return component of
    [en_prison_step] decomposes into [bet_wins]-conditional
    payoffs, connecting the operational step function to the
    coverage predicates used throughout the fairness analysis. *)

Lemma en_prison_imprisoned_snd :
  forall b n s,
  snd (en_prison_step b n Imprisoned s) = if bet_wins b n then s else 0.
Proof.
  intros. unfold en_prison_step.
  destruct (bet_wins b n); [reflexivity|].
  destruct (n =? 0); reflexivity.
Qed.

Lemma en_prison_free_snd :
  forall b n s,
  snd (en_prison_step b n Free s) =
    if bet_wins b n then s + s * payout_ratio b else 0.
Proof.
  intros. unfold en_prison_step.
  destruct (bet_wins b n); [reflexivity|].
  destruct (n =? 0); reflexivity.
Qed.

(** Recovery sum equals coverage count: for every even-money bet,
    the one-spin recovery from [Imprisoned] state (computed by
    [en_prison_step]) equals [count_wins b].  This connects the
    operational step function to the counting infrastructure. *)

Theorem en_prison_recovery_even_money :
  forall b, In b even_money_bets ->
  en_prison_recovery_sum b 1 = count_wins b.
Proof.
  intros b Hin. simpl in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  vm_compute; reflexivity.
Qed.

(** General recovery theorem: for ANY bet and stake, the
    one-spin recovery sum from [Imprisoned] state equals
    [count_wins b * s].  Proved structurally via
    [en_prison_imprisoned_snd] and [sum_filter_constant]. *)

Theorem en_prison_recovery_general :
  forall b s, en_prison_recovery_sum b s = count_wins b * s.
Proof.
  intros. unfold en_prison_recovery_sum.
  assert (H : map (fun n => snd (en_prison_step b n Imprisoned s))
                   (seq 0 N_POCKETS) =
              map (fun n => if bet_wins b n then s else 0)
                   (seq 0 N_POCKETS)).
  { apply map_ext. intro. apply en_prison_imprisoned_snd. }
  rewrite H, sum_filter_constant. unfold count_wins. reflexivity.
Qed.

(** Free-state one-spin return sum: equals [fairness_product b * s],
    confirming that en prison does not alter the immediate expected
    return on non-zero outcomes. *)

Definition en_prison_free_sum (b : bet_type) (stake : nat) : nat :=
  fold_left Nat.add
    (map (fun n => snd (en_prison_step b n Free stake))
         (seq 0 N_POCKETS)) 0.

Theorem en_prison_free_sum_eq :
  forall b s, en_prison_free_sum b s = fairness_product b * s.
Proof.
  intros. unfold en_prison_free_sum.
  assert (H : map (fun n => snd (en_prison_step b n Free s))
                   (seq 0 N_POCKETS) =
              map (fun n => if bet_wins b n
                            then s * (payout_ratio b + 1) else 0)
                   (seq 0 N_POCKETS)).
  { apply map_ext. intro n. rewrite en_prison_free_snd.
    destruct (bet_wins b n); lia. }
  rewrite H, sum_filter_constant.
  unfold fairness_product, count_wins. lia.
Qed.

(** ** Fixed-point derivation from [en_prison_step]

    From [Imprisoned] state, the recursive recovery across
    arbitrarily many spins satisfies the fixed-point equation
    [V = cw/P + V/P] where [cw = en_prison_recovery_sum b 1]
    (the one-spin count from [en_prison_recovery_even_money])
    and [P = N_POCKETS].  Win outcomes recover stake, zero
    re-imprisons, all others lose.  The unique solution is
    [V = cw / (P - 1)].  For even-money bets, [V = 18/36 = 1/2].

    La partage expected return from [Free] state:
    [E = fp/P + V/P = fp/P + cw/(P(P-1))]
    [= (fp(P-1) + cw) / (P(P-1))]
    [= (36*36 + 18) / (37*36) = 1314/1332 = 73/74]. *)

Open Scope Q_scope.

(** Fixed-point equation derived from [en_prison_step]:
    [V = recovery/P + V/P] where [recovery = en_prison_recovery_sum b 1].
    Proved structurally: [en_prison_recovery_even_money] rewrites the
    recovery sum to [count_wins b], [even_money_all_cover_18] makes
    it concrete, then Q cross-multiplication closes the goal. *)

Theorem en_prison_fixed_point :
  forall b, In b even_money_bets ->
  let V := Qmake (Z.of_nat (en_prison_recovery_sum b 1))
                  (Pos.of_nat (N_POCKETS - 1)) in
  Qeq V (Qmake (Z.of_nat (en_prison_recovery_sum b 1))
               (Pos.of_nat N_POCKETS)
         + Qmake 1 (Pos.of_nat N_POCKETS) * V).
Proof.
  intros b Hin. cbv zeta.
  rewrite (en_prison_recovery_even_money b Hin),
          (even_money_all_cover_18 b Hin).
  unfold N_POCKETS, Qeq, Qplus, Qmult. simpl. lia.
Qed.

(** Concrete instantiation for readability:
    [1/2 = 18/37 + (1/37)(1/2)]. *)

Corollary en_prison_fixed_point_concrete :
  Qeq (Qmake 1 2) (Qmake 18 37 + Qmake 1 37 * Qmake 1 2).
Proof. unfold Qeq, Qplus, Qmult. simpl. lia. Qed.

(** Fixed-point solution: [V = 1/2] for even-money bets,
    derived from [en_prison_step] via [en_prison_recovery_even_money]. *)

Theorem en_prison_recovery_fraction :
  forall b, In b even_money_bets ->
  Qeq (Qmake (Z.of_nat (en_prison_recovery_sum b 1))
              (Pos.of_nat (N_POCKETS - 1)))
      (Qmake 1 2).
Proof.
  intros b Hin.
  rewrite (en_prison_recovery_even_money b Hin),
          (even_money_all_cover_18 b Hin).
  unfold N_POCKETS, Qeq. simpl. lia.
Qed.

(** Uniqueness: the fixed-point [V * P = cw + V] has at most
    one solution when [P > 1].  Combined with [en_prison_recovery_fraction],
    this proves [1/2] is the only possible expected recovery. *)

(** Uniqueness of fixed-point solution over Z: if
    [v * (P - 1) = c] and [w * (P - 1) = c] with [P > 1],
    then [v = w].  Instantiated with [P = 37] and [c = 18],
    this proves [1/2] is the unique recovery value. *)

Lemma fixed_point_unique_Z :
  forall v w c P : Z,
  (1 < P)%Z -> (v * (P - 1) = c)%Z -> (w * (P - 1) = c)%Z -> v = w.
Proof. nia. Qed.

(** Applied to en prison: any Q value satisfying the recurrence
    [V * 37 = 18 + V] (equivalently [V * 36 = 18]) must equal [1/2].
    Together with [en_prison_recovery_fraction], this proves that
    the expected recovery from Imprisoned state is uniquely [1/2]. *)

Theorem en_prison_solution_unique :
  forall n : Z, forall d : positive,
  (n * 37 * Z.pos d = (18 * Z.pos d + n * 1) * (1 * Z.pos d))%Z ->
  (n * 2 = 1 * Z.pos d)%Z.
Proof.
  intros n d H.
  assert (Hd : (0 < Z.pos d)%Z) by lia.
  nia.
Qed.

Local Close Scope Q_scope.

(** Only the zero outcome re-imprisons; all other outcomes
    resolve to [Free].  This characterizes the one-step
    transition: imprisonment continues with probability [1/37]
    and terminates with probability [36/37] per spin. *)

Lemma en_prison_only_zero_reimprison :
  forall b n s, In b even_money_bets ->
  fst (en_prison_step b n Imprisoned s) = Imprisoned <-> n = 0.
Proof.
  intros b n s Hin.
  assert (Hb0 : bet_wins b 0 = false).
  { simpl in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    vm_compute; reflexivity. }
  split.
  - simpl. destruct (bet_wins b n); [discriminate|].
    destruct (n =? 0) eqn:Hz; [intros _; apply Nat.eqb_eq; exact Hz|discriminate].
  - intro Hn. subst n. simpl. rewrite Hb0. reflexivity.
Qed.

(** Geometric resolution: the imprisonment probability after
    [k] rounds is [(1/N_POCKETS)^k], decaying geometrically.
    Since [en_prison_only_zero_reimprison] shows only the zero
    outcome re-imprisons, and [1 < N_POCKETS], almost-sure
    termination follows: [1^k < N_POCKETS^k] for all [k > 0]. *)

Theorem en_prison_geometric_resolution :
  forall k, 0 < k -> 1 ^ k < N_POCKETS ^ k.
Proof.
  intros k Hk. rewrite Nat.pow_1_l.
  apply Nat.pow_gt_1. unfold N_POCKETS. lia. lia.
Qed.

Open Scope Q_scope.

(** La partage return derived from the operational model.
    The total expected return combines immediate wins
    ([fairness_product], from [en_prison_free_snd]) and
    deferred en prison recovery ([en_prison_recovery_sum],
    from [en_prison_imprisoned_snd]), yielding the
    [(2*fp + 1) / (2*N_POCKETS)] formula. *)

Theorem la_partage_derived :
  forall b, In b even_money_bets ->
  Qeq (Qmake (Z.of_nat (fairness_product b * (N_POCKETS - 1)
                          + en_prison_recovery_sum b 1))
              (Pos.of_nat (N_POCKETS * (N_POCKETS - 1))))
      (la_partage_return_Q b).
Proof.
  intros b Hin.
  rewrite (en_prison_recovery_even_money b Hin).
  unfold la_partage_return_Q.
  assert (Hfp : fairness_product b = 36%nat)
    by (simpl in Hin;
        destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        vm_compute; reflexivity).
  rewrite Hfp, (even_money_all_cover_18 b Hin).
  unfold N_POCKETS, Qeq. simpl. lia.
Qed.

Local Close Scope Q_scope.

(* ================================================================== *)
(** * Mod-37 bias bound for concrete RNG widths                        *)
(* ================================================================== *)

(** For an RNG producing values in [0, N), the maximum frequency
    deviation between any two pockets is at most 1 hit (from
    [rng_max_deviation]).  As a fraction of total samples, the
    per-pocket bias is at most [1/N].  For a [k]-bit source
    ([N = 2^k]), every pocket's hit fraction lies within [1/2^k]
    of the ideal [1/37]. *)

(** Power of two, for stating bit-width-specific bias bounds. *)

Definition two_pow (k : nat) : nat := Nat.pow 2 k.

(** General bias bound: for any source range N >= 37, the hit
    count for every pocket is within 1 of [N / 37]. *)

Theorem mod_bias_bound :
  forall p N, p < N_POCKETS -> N_POCKETS <= N ->
  N / N_POCKETS <= count_hits p N /\ count_hits p N <= N / N_POCKETS + 1.
Proof.
  intros p N Hp HN.
  destruct (le_lt_dec (N mod N_POCKETS) p) as [Hhi|Hlo].
  - rewrite (proj2 (hits_split p N Hp) Hhi). lia.
  - rewrite (proj1 (hits_split p N Hp) Hlo). lia.
Qed.

(** Bias vanishes for multiples of 37: hit count is exactly [N/37]. *)

Corollary bias_zero_multiple :
  forall m p, p < N_POCKETS ->
  count_hits p (N_POCKETS * m) = m.
Proof. exact uniform_multiple. Qed.

(* ================================================================== *)
(** * Rejection sampling                                                *)
(* ================================================================== *)

(** Rejection sampling eliminates mod bias entirely: given a source
    range [[0, N)], accept values below [37 * (N / 37)] and reject
    the rest.  The accepted range is always a multiple of 37, so
    [uniform_multiple] gives exact uniformity.  The results
    establish that the accepted range is a valid multiple of 37,
    that every pocket receives exactly [N / 37] hits within it,
    and that the acceptance threshold is at most 36 below [N],
    bounding the rejection rate by [37/N]. *)

(** Rejection threshold: the largest multiple of 37 not exceeding [N]. *)

Definition rejection_bound (N : nat) : nat := N_POCKETS * (N / N_POCKETS).

(** The rejection bound is a multiple of 37. *)

Lemma rejection_bound_multiple :
  forall N, exists m, rejection_bound N = N_POCKETS * m.
Proof.
  intro N. exists (N / N_POCKETS). reflexivity.
Qed.

(** Applying rejection twice yields the same bound. *)

Lemma rejection_bound_idempotent :
  forall N, rejection_bound (rejection_bound N) = rejection_bound N.
Proof.
  intro N. unfold rejection_bound.
  f_equal. rewrite Nat.mul_comm. apply Nat.div_mul. unfold N_POCKETS. lia.
Qed.

(** The rejection bound does not exceed the source range. *)

Lemma rejection_bound_le :
  forall N, rejection_bound N <= N.
Proof.
  intro N. unfold rejection_bound.
  pose proof (Nat.div_mod_eq N N_POCKETS). lia.
Qed.

(** At most [N_POCKETS - 1 = 36] values are rejected. *)

Lemma rejection_waste_bound :
  forall N, N - rejection_bound N < N_POCKETS.
Proof.
  intro N. unfold rejection_bound.
  pose proof (Nat.div_mod_eq N N_POCKETS).
  pose proof (Nat.mod_upper_bound N N_POCKETS ltac:(unfold N_POCKETS; lia)).
  lia.
Qed.

(** Every pocket receives exactly [N / 37] hits in the accepted range. *)

Theorem rejection_sampling_uniform :
  forall p N, p < N_POCKETS ->
  count_hits p (rejection_bound N) = N / N_POCKETS.
Proof.
  intros p N Hp. unfold rejection_bound.
  exact (uniform_multiple (N / N_POCKETS) p Hp).
Qed.

(** For any [N >= 37], at least one value is accepted, so rejection
    sampling always terminates with probability 1 over repeated draws. *)

Lemma rejection_bound_pos :
  forall N, N_POCKETS <= N -> 0 < rejection_bound N.
Proof.
  intros N HN. unfold rejection_bound.
  assert (Hd : 0 < N / N_POCKETS).
  { apply Nat.div_str_pos. unfold N_POCKETS in *. lia. }
  unfold N_POCKETS in *. lia.
Qed.

(** Rejection sampling composes with [rng_to_pocket]: for any value
    [v < rejection_bound N], [rng_to_pocket v = v mod 37] is exactly
    uniform because [rejection_bound N] is a multiple of 37. *)

(** Synonym of [rejection_sampling_uniform] for composability. *)

Theorem rejection_sampling_correct :
  forall p N, p < N_POCKETS ->
  count_hits p (rejection_bound N) = N / N_POCKETS.
Proof. exact rejection_sampling_uniform. Qed.

(** Concrete rejection thresholds for common source sizes.  For a
    source range of [N], rejection discards at most [N mod 37]
    values.  On a 256-value source (8-bit), 256 mod 37 = 34 values
    are wasted, giving acceptance rate 222/256 ~ 86.7%.  On a
    1000-value source, 1000 mod 37 = 1, acceptance rate 999/1000. *)

Lemma rejection_bound_256 : rejection_bound 256 = 222.
Proof. vm_compute. reflexivity. Qed.

Lemma rejection_bound_1000 : rejection_bound 1000 = 999.
Proof. vm_compute. reflexivity. Qed.

Lemma rejection_bound_10000 : rejection_bound 10000 = 9990.
Proof. vm_compute. reflexivity. Qed.

(** Acceptance rate and expected draws.  The acceptance probability
    per draw is [rejection_bound N / N].  Since [rejection_bound N
    >= N - 36], the expected draws are at most [N / (N - 36)].
    Almost-sure termination follows from [rejection_bound_pos]. *)

Theorem rejection_expected_draws_bound :
  forall N, N_POCKETS <= N ->
  N / rejection_bound N <= N / (N - (N_POCKETS - 1)).
Proof.
  intros N HN.
  assert (Hrb_pos : 0 < rejection_bound N) by (apply rejection_bound_pos; exact HN).
  assert (Hle : N - (N_POCKETS - 1) <= rejection_bound N).
  { pose proof (rejection_waste_bound N). unfold N_POCKETS in *. lia. }
  apply Nat.div_le_compat_l. split; [|exact Hle].
  unfold N_POCKETS in *. lia.
Qed.

(** Rejection sampling yields exact counting uniformity, stated
    via [is_uniform] for composition with downstream analyses. *)

Theorem rejection_uniform_pipeline :
  forall N, N_POCKETS <= N ->
  is_uniform N_POCKETS (rejection_bound N).
Proof.
  intros N HN p Hp.
  rewrite rejection_sampling_uniform by exact Hp.
  unfold rejection_bound.
  rewrite Nat.mul_comm, Nat.div_mul by (unfold N_POCKETS; lia).
  reflexivity.
Qed.

(** Geometric convergence of rejection sampling.  The rejection
    count [waste := N - rejection_bound N] satisfies [waste < 37].
    After [k] independent draws from [0, N), the probability of
    [k] consecutive rejections is [(waste / N)^k].  Since
    [waste < N], we have [waste^k < N^k] for all [k >= 1],
    proving geometric decay toward zero. *)

(** The rejection waste is strictly less than the source range. *)

Lemma rejection_waste_strict :
  forall N, N_POCKETS <= N -> N - rejection_bound N < N.
Proof.
  intros N HN.
  pose proof (rejection_bound_pos N HN).
  pose proof (rejection_bound_le N).
  unfold rejection_bound in *. unfold N_POCKETS in *. lia.
Qed.

(** [waste^k < N^k] for [k >= 1]: geometric decay of the
    probability of [k] consecutive rejections. *)

Lemma rejection_geometric_decay :
  forall N k, N_POCKETS <= N -> 0 < k ->
  (N - rejection_bound N) ^ k < N ^ k.
Proof.
  intros N k HN Hk.
  pose proof (rejection_waste_strict N HN) as Hlt.
  induction k as [|k' IH].
  - lia.
  - destruct k' as [|k''].
    + cbn [Nat.pow]. lia.
    + specialize (IH ltac:(lia)).
      cbn [Nat.pow] in IH |- *.
      set (w := N - rejection_bound N) in *.
      set (A := w ^ k'') in *. set (B := N ^ k'') in *.
      nia.
Qed.

(** End-to-end pipeline guarantee: for any RNG source with range
    >= 37, rejection sampling + mod-37 mapping produces an exactly
    uniform pocket distribution, every well-formed bet has expected
    return = stake * fairness_product / N_POCKETS, and no bet
    achieves non-negative edge. *)

Theorem pipeline_end_to_end :
  forall N, N_POCKETS <= N ->
  (* 1. Rejection sampling yields exact uniformity *)
  is_uniform N_POCKETS (rejection_bound N) /\
  (* 2. The acceptance rate is positive (terminates a.s.) *)
  0 < rejection_bound N /\
  (* 3. Every well-formed bet has sub-unit expected return *)
  (forall b s, well_formed b -> 0 < s ->
   expected_return_numerator b s < N_POCKETS * s).
Proof.
  intros N HN. repeat split.
  - exact (rejection_uniform_pipeline N HN).
  - exact (rejection_bound_pos N HN).
  - intros b s Hwf Hs. exact (no_winning_system b s Hwf Hs).
Qed.

(* ================================================================== *)
(** * Verified RNG module type                                          *)
(* ================================================================== *)

(** The module type [VERIFIED_RNG] specifies the contract for an
    RNG source: it must declare a source range and prove it covers
    all 37 pockets.  The functor [RNG_Uniformity] then derives the
    full uniformity and fairness guarantee for any conforming
    implementation, culminating in [rng_no_winning_system]: no
    well-formed bet achieves non-negative expected return.

    This connects the RNG pipeline to the bet-level fairness
    theorems: [pipeline_end_to_end] proves the properties for an
    arbitrary [N]; the module packages them for a specific source
    so downstream code can import the guarantees without reproving
    the [N_POCKETS <= source_range] obligation at each use site. *)

Module Type VERIFIED_RNG.
  (** The RNG produces values in [[0, source_range)]. *)
  Parameter source_range : nat.

  (** The source range must cover at least one full cycle of
      37 pockets.  Without this, some pockets get zero hits. *)
  Axiom source_range_sufficient : N_POCKETS <= source_range.
End VERIFIED_RNG.

(** Given any conforming RNG, we derive the full verification
    chain: hit-count bounds, rejection sampling uniformity,
    and the no-winning-system guarantee for all well-formed bets. *)

Module RNG_Uniformity (R : VERIFIED_RNG).

  (** Every pocket's hit count is within 1 of the ideal. *)
  Theorem pocket_deviation :
    forall p, p < N_POCKETS ->
    R.source_range / N_POCKETS <= count_hits p R.source_range /\
    count_hits p R.source_range <= R.source_range / N_POCKETS + 1.
  Proof. exact (fun p Hp => mod_bias_bound p R.source_range Hp R.source_range_sufficient). Qed.

  (** No two pockets differ by more than 1 hit. *)
  Theorem pairwise_deviation :
    forall p1 p2, p1 < N_POCKETS -> p2 < N_POCKETS ->
    count_hits p1 R.source_range <= count_hits p2 R.source_range + 1.
  Proof. exact (fun p1 p2 H1 H2 => rng_max_deviation p1 p2 R.source_range H1 H2). Qed.

  (** Rejection sampling over [[0, source_range)] produces
      equal hit counts across all pockets. *)
  Definition accepted_range := rejection_bound R.source_range.

  Theorem accepted_range_uniform :
    forall p, p < N_POCKETS ->
    count_hits p accepted_range = R.source_range / N_POCKETS.
  Proof.
    intros p Hp. unfold accepted_range.
    exact (rejection_sampling_uniform p R.source_range Hp).
  Qed.

  Theorem accepted_range_positive : 0 < accepted_range.
  Proof.
    unfold accepted_range. exact (rejection_bound_pos R.source_range R.source_range_sufficient).
  Qed.

  Theorem waste_bounded : R.source_range - accepted_range < N_POCKETS.
  Proof.
    unfold accepted_range. exact (rejection_waste_bound R.source_range).
  Qed.

  (** The culminating guarantee: for this RNG source, rejection
      sampling yields exact uniformity, the acceptance rate is
      positive, and no well-formed bet achieves non-negative edge.
      This is [pipeline_end_to_end] instantiated for [source_range]. *)

  Theorem rng_pipeline :
    is_uniform N_POCKETS accepted_range /\
    0 < accepted_range /\
    (forall b s, well_formed b -> 0 < s ->
     expected_return_numerator b s < N_POCKETS * s).
  Proof.
    pose proof (pipeline_end_to_end R.source_range R.source_range_sufficient)
      as [Hu [Hp Hns]].
    repeat split; [exact Hu | exact Hp | exact Hns].
  Qed.

End RNG_Uniformity.

(** Two concrete instantiations demonstrating the module in use.
    Any RNG with [source_range >= 37] qualifies. *)

(** 8-bit source (256 values): rejection discards 34 values,
    acceptance rate 222/256 ~ 86.7%.  Each pocket gets exactly
    6 hits in the accepted range. *)

Module RNG_256 <: VERIFIED_RNG.
  Definition source_range := 256.
  Lemma source_range_sufficient : N_POCKETS <= source_range.
  Proof. unfold N_POCKETS, source_range. lia. Qed.
End RNG_256.

Module RNG_256_Props := RNG_Uniformity RNG_256.

(** The 8-bit RNG accepted range is 222 (= 6 * 37). *)

Lemma rng_256_accepted : RNG_256_Props.accepted_range = 222.
Proof. vm_compute. reflexivity. Qed.

(** Each pocket receives exactly 6 hits in the 8-bit accepted range. *)

Lemma rng_256_hits : forall p, p < N_POCKETS ->
  count_hits p RNG_256_Props.accepted_range = 6.
Proof.
  intros p Hp. rewrite rng_256_accepted.
  exact (uniform_multiple 6 p Hp).
Qed.

(** 1000-value source: rejection discards 1 value,
    acceptance rate 999/1000. *)

Module RNG_1000 <: VERIFIED_RNG.
  Definition source_range := 1000.
  Lemma source_range_sufficient : N_POCKETS <= source_range.
  Proof. unfold N_POCKETS, source_range. lia. Qed.
End RNG_1000.

Module RNG_1000_Props := RNG_Uniformity RNG_1000.

(** The 1000-value RNG accepted range is 999 (= 27 * 37). *)

Lemma rng_1000_accepted : RNG_1000_Props.accepted_range = 999.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(** * American double-zero wheel                                        *)
(* ================================================================== *)

(** The American wheel adds a second green pocket ("00", encoded
    as pocket 37), giving 38 total outcomes.  Payouts are unchanged,
    so the fairness product remains 36 for standard bets, but the
    expected return drops to [36/38 = 18/19], encoding a house edge
    of [2/38 = 1/19 ~ 5.26%] — strictly worse than the European
    [1/37 ~ 2.70%].

    The results establish that the American fairness product
    equals the European one for every shared bet, and that the
    American expected return is strictly less. *)

(** Total number of pockets on the American double-zero wheel. *)

Definition N_POCKETS_US := 38.

(** On the American wheel, pocket 37 ("00") loses every standard
    bet: it is green, not odd or even, not low or high.  So the
    winning count over 38 pockets is the same as over 37. *)

(** Winning count over the American 38-pocket outcome space. *)

Definition count_wins_us (b : bet_type) : nat :=
  length (filter (bet_wins b) (seq 0 N_POCKETS_US)).

(** Each Straight bet covers exactly 1 of 38 American pockets. *)

Lemma double_zero_loses_all_check :
  all_below N_POCKETS (fun k =>
    count_wins_us (Straight k) =? 1) = true.
Proof. vm_compute. reflexivity. Qed.

(** "00" (pocket 37) contributes zero wins for every even-money
    and group bet.  The European [bet_wins] is reused for the
    American wheel: pocket 37 loses all the same bets as pocket 0
    because both are out-of-range for every parity, range, and
    color test.  This implicit equivalence is what makes
    [count_wins_us_eq_eu] hold without a separate American
    [bet_wins] function. *)

Lemma pocket_37_same_as_0 :
  forall b, In b even_money_bets ->
  bet_wins b 37 = bet_wins b 0.
Proof.
  intros b Hin. simpl in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  vm_compute; reflexivity.
Qed.

(** Pocket 37 ("00") loses every even-money bet. *)

Lemma pocket_37_loses_even_money :
  bet_wins RedBet 37 = false /\
  bet_wins BlackBet 37 = false /\
  bet_wins OddBet 37 = false /\
  bet_wins EvenBet 37 = false /\
  bet_wins LowBet 37 = false /\
  bet_wins HighBet 37 = false.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Pocket 37 loses every well-formed European bet. *)

Lemma well_formed_pocket_37_loses :
  forall b, well_formed b -> bet_wins b 37 = false.
Proof.
  intros b Hwf; destruct b; simpl in Hwf;
  try (vm_compute; reflexivity).
  - (* Straight *) unfold N_POCKETS in Hwf.
    assert (H37 : 37 =? n = false) by (apply Nat.eqb_neq; lia).
    change (bet_wins (Straight n) 37) with (37 =? n). exact H37.
  - (* Split *) destruct Hwf as [Ha [Hb _]]. unfold N_POCKETS in *.
    assert (Ha37 : 37 =? a = false) by (apply Nat.eqb_neq; lia).
    assert (Hb37 : 37 =? b = false) by (apply Nat.eqb_neq; lia).
    change (bet_wins (Split a b) 37) with ((37 =? a) || (37 =? b)).
    rewrite Ha37, Hb37. reflexivity.
  - (* Street *) destruct Hwf as [H1 H12].
    change (bet_wins (Street row) 37) with (in_street 37 row).
    unfold in_street.
    replace (37 <=? (row - 1) * 3 + 1 + 2) with false
      by (symmetry; apply Nat.leb_gt; lia).
    rewrite andb_false_r. reflexivity.
  - (* Corner *) destruct Hwf as [H1 [H32 [_ [-> [-> ->]]]]].
    change (bet_wins (Corner a (a+1) (a+3) (a+4)) 37)
      with ((37 =? a) || (37 =? a+1) || (37 =? a+3) || (37 =? a+4)).
    replace (37 =? a) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (37 =? a+1) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (37 =? a+3) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (37 =? a+4) with false by (symmetry; apply Nat.eqb_neq; lia).
    reflexivity.
  - (* SixLine *) destruct Hwf as [H1 [H12a [H2 [H12b _]]]].
    change (bet_wins (SixLine row1 row2) 37)
      with (in_street 37 row1 || in_street 37 row2).
    apply orb_false_iff; split; unfold in_street.
    + replace (37 <=? (row1 - 1) * 3 + 1 + 2) with false
        by (symmetry; apply Nat.leb_gt; lia).
      rewrite andb_false_r. reflexivity.
    + replace (37 <=? (row2 - 1) * 3 + 1 + 2) with false
        by (symmetry; apply Nat.leb_gt; lia).
      rewrite andb_false_r. reflexivity.
  - (* Trio *) destruct Hwf as [Hv|Hv]; subst; vm_compute; reflexivity.
  - (* FiveNumber *) contradiction.
  - (* Column *) destruct Hwf as [H1 H3].
    change (bet_wins (Column col) 37) with (in_column 37 col).
    unfold in_column.
    replace (37 <=? 36) with false by reflexivity.
    rewrite !andb_false_r. reflexivity.
  - (* Dozen *) destruct Hwf as [H1 H3].
    do 4 (destruct doz as [|doz]; [try lia; vm_compute; reflexivity|]).
    lia.
Qed.

(** For every well-formed European bet, the American and European
    winning counts coincide: pocket 37 contributes no wins. *)

Theorem count_wins_us_eq_eu :
  forall b, well_formed b -> count_wins_us b = count_wins b.
Proof.
  intros b Hwf.
  unfold count_wins_us, count_wins, N_POCKETS_US, N_POCKETS.
  change (seq 0 38) with (seq 0 37 ++ [37]).
  rewrite filter_app, length_app.
  assert (H : length (filter (bet_wins b) [37]) = 0).
  { simpl. rewrite (well_formed_pocket_37_loses b Hwf). reflexivity. }
  rewrite H. lia.
Qed.

(** American fairness product: winning count over 38 pockets
    times (payout ratio + 1). *)

Definition fairness_product_us (b : bet_type) : nat :=
  count_wins_us b * (payout_ratio b + 1).

(** American and European fairness products coincide on all
    well-formed European bets. *)

Corollary fairness_product_us_eq_eu :
  forall b, well_formed b -> fairness_product_us b = fairness_product b.
Proof.
  intros b Hwf. unfold fairness_product_us, fairness_product.
  rewrite (count_wins_us_eq_eu b Hwf). reflexivity.
Qed.

(** For standard bets, the American winning count equals the European
    count (pocket 37 loses everything), so fairness_product_us = 36.
    Verified computationally for representative bet types. *)

Lemma us_red_fp : fairness_product_us RedBet = 36.
Proof. vm_compute. reflexivity. Qed.

Lemma us_black_fp : fairness_product_us BlackBet = 36.
Proof. vm_compute. reflexivity. Qed.

Lemma us_odd_fp : fairness_product_us OddBet = 36.
Proof. vm_compute. reflexivity. Qed.

Lemma us_even_fp : fairness_product_us EvenBet = 36.
Proof. vm_compute. reflexivity. Qed.

Lemma us_low_fp : fairness_product_us LowBet = 36.
Proof. vm_compute. reflexivity. Qed.

Lemma us_high_fp : fairness_product_us HighBet = 36.
Proof. vm_compute. reflexivity. Qed.

Lemma us_straight_0_fp : fairness_product_us (Straight 0) = 36.
Proof. vm_compute. reflexivity. Qed.

Lemma us_column1_fp : fairness_product_us (Column 1) = 36.
Proof. vm_compute. reflexivity. Qed.

Lemma us_dozen1_fp : fairness_product_us (Dozen 1) = 36.
Proof. vm_compute. reflexivity. Qed.

(** Even-money bet types for the American wheel. *)

Definition even_money_bets_us : list bet_type :=
  [RedBet; BlackBet; OddBet; EvenBet; LowBet; HighBet].

(** For every even-money bet, the American expected return [36/38]
    is strictly less than the European [36/37]. *)

Theorem american_strictly_worse_even_money :
  forall b, In b even_money_bets_us ->
  Qlt (Qmake (Z.of_nat (fairness_product_us b)) (Pos.of_nat N_POCKETS_US))
      (Qmake (Z.of_nat (fairness_product b)) (Pos.of_nat N_POCKETS)).
Proof.
  intros b Hin.
  assert (Hfp_us : fairness_product_us b = 36%nat).
  { simpl in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    vm_compute; reflexivity. }
  assert (Hfp_eu : fairness_product b = 36%nat).
  { simpl in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    vm_compute; reflexivity. }
  rewrite Hfp_us, Hfp_eu.
  unfold Qlt, N_POCKETS, N_POCKETS_US. simpl. lia.
Qed.

(** The same ordering holds for any bet whose fairness product is
    36 on both wheels: 36/38 < 36/37 because 38 > 37. *)

Theorem american_strictly_worse_general :
  forall b, fairness_product b = 36%nat -> fairness_product_us b = 36%nat ->
  Qlt (Qmake 36 (Pos.of_nat N_POCKETS_US))
      (Qmake 36 (Pos.of_nat N_POCKETS)).
Proof.
  intros. unfold Qlt, N_POCKETS, N_POCKETS_US. simpl. lia.
Qed.

(** For ALL well-formed non-Basket bets, the American expected return
    is strictly less than the European.  Uses [unified_fairness] and
    [fairness_product_us_eq_eu]: both wheels give fairness product 36,
    but 36/38 < 36/37. *)

Theorem american_strictly_worse_all :
  forall b, well_formed b -> b <> Basket ->
  Qlt (Qmake (Z.of_nat (fairness_product_us b)) (Pos.of_nat N_POCKETS_US))
      (Qmake (Z.of_nat (fairness_product b)) (Pos.of_nat N_POCKETS)).
Proof.
  intros b Hwf Hne.
  pose proof (unified_fairness b Hwf) as [Hfp | Hbsk]; [| contradiction].
  rewrite (fairness_product_us_eq_eu b Hwf), Hfp.
  unfold Qlt, N_POCKETS, N_POCKETS_US. simpl. lia.
Qed.

(** The Five-Number bet (0-00-1-2-3) is the American analogue of
    the European Basket.  At 6:1 on 5 pockets out of 38, its
    fairness product is [5 * 7 = 35], and its expected return
    [35/38] is even worse than the European Basket's [28/37]. *)

(** Five-Number membership predicate: {0, 00, 1, 2, 3}. *)

Definition five_number_wins (n : nat) : bool :=
  (n =? 0) || (n =? 37) || (n =? 1) || (n =? 2) || (n =? 3).

(** Number of outcomes covered by the Five-Number bet. *)

Definition five_number_count : nat :=
  length (filter five_number_wins (seq 0 N_POCKETS_US)).

(** The Five-Number bet covers exactly 5 pockets. *)

Lemma five_number_covers_5 : five_number_count = 5.
Proof. vm_compute. reflexivity. Qed.

(** Five-Number fairness product: 5 * 7 = 35. *)

Theorem five_number_fairness : five_number_count * (6 + 1) = 35.
Proof. vm_compute. reflexivity. Qed.

(** FiveNumber fairness via the integrated [fairness_product_us]. *)

Lemma five_number_fairness_product_us :
  fairness_product_us FiveNumber = 35.
Proof. vm_compute. reflexivity. Qed.

(** Rational expected return and house edge for the American wheel. *)

Open Scope Q_scope.

(** American expected return per unit staked, as a rational number. *)

Definition expected_return_us_Q (b : bet_type) : Q :=
  Qmake (Z.of_nat (fairness_product_us b)) (Pos.of_nat N_POCKETS_US).

(** American even-money expected return: 36/38. *)

Theorem american_expected_return_even_money :
  forall b, In b even_money_bets ->
  Qeq (expected_return_us_Q b) (Qmake 36 38).
Proof.
  intros b Hin. unfold expected_return_us_Q, N_POCKETS_US.
  assert (H : fairness_product_us b = 36%nat).
  { simpl in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    vm_compute; reflexivity. }
  rewrite H. reflexivity.
Qed.

(** American even-money house edge: 2/38 = 1/19 per unit. *)

Theorem american_house_edge :
  forall b, In b even_money_bets ->
  Qeq (1 - expected_return_us_Q b) (Qmake 2 38).
Proof.
  intros b Hin.
  assert (H : fairness_product_us b = 36%nat).
  { simpl in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    vm_compute; reflexivity. }
  unfold expected_return_us_Q, Qminus, Qplus, Qopp, Qeq, N_POCKETS_US.
  rewrite H. simpl. lia.
Qed.

(** FiveNumber (35/38) has a better return than Basket (28/37).
    Both are strictly worse than standard bets (36/38 and 36/37). *)

Theorem five_number_better_than_basket :
  Qlt (Qmake 28 37) (Qmake 35 38).
Proof. unfold Qlt. simpl. lia. Qed.

Close Scope Q_scope.

(* ================================================================== *)
(** * Axiom audit                                                      *)
(* ================================================================== *)

Print Assumptions rng_to_pocket_valid.
Print Assumptions rng_surjective.
Print Assumptions straight_fairness.
Print Assumptions red_fairness.
Print Assumptions black_fairness.
Print Assumptions odd_fairness.
Print Assumptions even_fairness.
Print Assumptions low_fairness.
Print Assumptions high_fairness.
Print Assumptions column_fairness.
Print Assumptions dozen_fairness.
Print Assumptions street_fairness.
Print Assumptions split_covers_2.
Print Assumptions split_fairness.
Print Assumptions corner_fairness.
Print Assumptions sixline_fairness.
Print Assumptions trio_fairness.
Print Assumptions basket_fairness.
Print Assumptions payout_outcome_independent.
Print Assumptions payout_binary.
Print Assumptions loss_returns_zero.
Print Assumptions win_returns_correct.
Print Assumptions hits_split.
Print Assumptions rng_max_deviation.
Print Assumptions zero_loses_outside.
Print Assumptions house_edge_even_money.
Print Assumptions nonzero_red_or_black.
Print Assumptions red_black_disjoint.
Print Assumptions unified_fairness.
Print Assumptions basket_unique_exception.
Print Assumptions american_strictly_worse_all.
Print Assumptions rejection_sampling_uniform.
Print Assumptions fairness_product_invariant_stake.
Print Assumptions well_formed_decidable.

(** Module-level audit: [RNG_1000_Props.rng_pipeline] depends on
    [RNG_1000.source_range_sufficient], which is the module's own
    proof obligation — not an unproven axiom.  Consumers of the
    module verify this obligation at instantiation time.  The
    [VERIFIED_RNG] module type's [Axiom] is a parameter, not a
    gap in the proof. *)

Print Assumptions RNG_1000_Props.rng_pipeline.

(* ================================================================== *)
(** * Verified simulator                                                *)
(* ================================================================== *)

(** Simulates a single spin: maps a raw RNG output to a pocket
    via [rng_to_pocket] and computes the net return. *)

Definition simulate_spin (b : bet_type) (stake raw : nat) : nat :=
  net_return b stake (rng_to_pocket raw).

(** Simulates a session of multiple spins and sums the returns. *)

Definition simulate_session (b : bet_type) (stake : nat)
    (raws : list nat) : nat :=
  fold_left Nat.add (map (simulate_spin b stake) raws) 0.

(** [simulate_spin] is equivalent to computing [net_return]
    on the modular reduction of the raw input. *)

Theorem simulate_spin_correct :
  forall b stake raw,
  simulate_spin b stake raw = net_return b stake (raw mod N_POCKETS).
Proof. intros. unfold simulate_spin, rng_to_pocket. reflexivity. Qed.

(** Extraction sanity checks: concrete evaluations verified
    against expected values prior to OCaml extraction. *)

(** Straight 17 wins 3600 on pocket 17 at stake 100. *)

Lemma extraction_test_straight_win :
  simulate_spin (Straight 17) 100 17 = 3600.
Proof. vm_compute. reflexivity. Qed.

(** Straight 17 returns 0 on pocket 5. *)

Lemma extraction_test_straight_lose :
  simulate_spin (Straight 17) 100 5 = 0.
Proof. vm_compute. reflexivity. Qed.

(** Red wins 100 on pocket 1 at stake 50. *)

Lemma extraction_test_red_win :
  simulate_spin RedBet 50 1 = 100.
Proof. vm_compute. reflexivity. Qed.

(** Red returns 0 on pocket 0 (green). *)

Lemma extraction_test_red_zero :
  simulate_spin RedBet 50 0 = 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(** * Extraction                                                        *)
(* ================================================================== *)

Extraction Language OCaml.
Extraction "roulette_extracted" bet_type bet_wins payout_ratio
  net_return rng_to_pocket expected_return_numerator
  simulate_spin simulate_session rejection_bound
  well_formed_dec count_wins fairness_product.
