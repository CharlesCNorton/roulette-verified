
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

module Nat =
 struct
  (** val add : nat -> nat -> nat **)

  let rec add n m =
    match n with
    | O -> m
    | S p -> S (add p m)

  (** val sub : nat -> nat -> nat **)

  let rec sub n m =
    match n with
    | O -> n
    | S k -> (match m with
              | O -> n
              | S l -> sub k l)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m

  (** val even : nat -> bool **)

  let rec even = function
  | O -> True
  | S n0 -> (match n0 with
             | O -> False
             | S n' -> even n')

  (** val odd : nat -> bool **)

  let odd n =
    negb (even n)

  (** val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod **)

  let rec divmod x y q u =
    match x with
    | O -> Pair (q, u)
    | S x' ->
      (match u with
       | O -> divmod x' y (S q) y
       | S u' -> divmod x' y q u')

  (** val div : nat -> nat -> nat **)

  let div x y = match y with
  | O -> y
  | S y' -> fst (divmod x y' O y')

  (** val modulo : nat -> nat -> nat **)

  let modulo x = function
  | O -> x
  | S y' -> sub y' (snd (divmod x y' O y'))
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, l0) -> Cons ((f a), (map f l0))

(** val seq : nat -> nat -> nat list **)

let rec seq start = function
| O -> Nil
| S len0 -> Cons (start, (seq (S start) len0))

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Nil -> a0
  | Cons (b, l0) -> fold_left f l0 (f a0 b)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| Nil -> Nil
| Cons (x, l0) ->
  (match f x with
   | True -> Cons (x, (filter f l0))
   | False -> filter f l0)

(** val n_POCKETS : nat **)

let n_POCKETS =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))

(** val rng_to_pocket : nat -> nat **)

let rng_to_pocket raw =
  Nat.modulo raw n_POCKETS

type color =
| Green
| Red
| Black

(** val pocket_color_rule : nat -> color **)

let pocket_color_rule n =
  match match Nat.eqb n O with
        | True -> True
        | False ->
          Nat.ltb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))) n with
  | True -> Green
  | False ->
    (match match match Nat.leb (S O) n with
                 | True -> Nat.leb n (S (S (S (S (S (S (S (S (S (S O))))))))))
                 | False -> False with
           | True -> True
           | False ->
             (match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S O))))))))))))))))))) n with
              | True ->
                Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S
                  O))))))))))))))))))))))))))))
              | False -> False) with
     | True -> (match Nat.odd n with
                | True -> Red
                | False -> Black)
     | False -> (match Nat.odd n with
                 | True -> Black
                 | False -> Red))

(** val pocket_color : nat -> color **)

let pocket_color =
  pocket_color_rule

(** val is_red : nat -> bool **)

let is_red n =
  match pocket_color n with
  | Red -> True
  | _ -> False

(** val is_black : nat -> bool **)

let is_black n =
  match pocket_color n with
  | Black -> True
  | _ -> False

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

(** val in_column : nat -> nat -> bool **)

let in_column n col =
  match match match match Nat.leb (S O) col with
                    | True -> Nat.leb col (S (S (S O)))
                    | False -> False with
              | True -> Nat.leb (S O) n
              | False -> False with
        | True ->
          Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))
        | False -> False with
  | True ->
    Nat.eqb (Nat.modulo n (S (S (S O)))) (Nat.modulo col (S (S (S O))))
  | False -> False

(** val in_dozen : nat -> nat -> bool **)

let in_dozen n = function
| O -> False
| S n0 ->
  (match n0 with
   | O ->
     (match Nat.leb (S O) n with
      | True -> Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))
      | False -> False)
   | S n1 ->
     (match n1 with
      | O ->
        (match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))) n with
         | True ->
           Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S O))))))))))))))))))))))))
         | False -> False)
      | S n2 ->
        (match n2 with
         | O ->
           (match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S O))))))))))))))))))))))))) n with
            | True ->
              Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                O))))))))))))))))))))))))))))))))))))
            | False -> False)
         | S _ -> False)))

(** val in_street : nat -> nat -> bool **)

let in_street n row =
  let base = add (mul (sub row (S O)) (S (S (S O)))) (S O) in
  (match match match Nat.leb (S O) row with
               | True ->
                 Nat.leb row (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))
               | False -> False with
         | True -> Nat.leb base n
         | False -> False with
   | True -> Nat.leb n (add base (S (S O)))
   | False -> False)

(** val bet_wins : bet_type -> nat -> bool **)

let bet_wins b n =
  match b with
  | Straight k -> Nat.eqb n k
  | Split (a, b0) ->
    (match Nat.eqb n a with
     | True -> True
     | False -> Nat.eqb n b0)
  | Street row -> in_street n row
  | Corner (a, b0, c, d) ->
    (match match match Nat.eqb n a with
                 | True -> True
                 | False -> Nat.eqb n b0 with
           | True -> True
           | False -> Nat.eqb n c with
     | True -> True
     | False -> Nat.eqb n d)
  | SixLine (r1, r2) ->
    (match in_street n r1 with
     | True -> True
     | False -> in_street n r2)
  | Trio variant ->
    (match variant with
     | O -> False
     | S n0 ->
       (match n0 with
        | O ->
          (match match Nat.eqb n O with
                 | True -> True
                 | False -> Nat.eqb n (S O) with
           | True -> True
           | False -> Nat.eqb n (S (S O)))
        | S n1 ->
          (match n1 with
           | O ->
             (match match Nat.eqb n O with
                    | True -> True
                    | False -> Nat.eqb n (S (S O)) with
              | True -> True
              | False -> Nat.eqb n (S (S (S O))))
           | S _ -> False)))
  | Basket ->
    (match match match Nat.eqb n O with
                 | True -> True
                 | False -> Nat.eqb n (S O) with
           | True -> True
           | False -> Nat.eqb n (S (S O)) with
     | True -> True
     | False -> Nat.eqb n (S (S (S O))))
  | FiveNumber ->
    (match match match match Nat.eqb n O with
                       | True -> True
                       | False ->
                         Nat.eqb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                           (S (S (S (S (S (S
                           O))))))))))))))))))))))))))))))))))))) with
                 | True -> True
                 | False -> Nat.eqb n (S O) with
           | True -> True
           | False -> Nat.eqb n (S (S O)) with
     | True -> True
     | False -> Nat.eqb n (S (S (S O))))
  | Column col -> in_column n col
  | Dozen doz -> in_dozen n doz
  | RedBet -> is_red n
  | BlackBet -> is_black n
  | OddBet ->
    (match match Nat.leb (S O) n with
           | True ->
             Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               O))))))))))))))))))))))))))))))))))))
           | False -> False with
     | True -> Nat.odd n
     | False -> False)
  | EvenBet ->
    (match match Nat.leb (S O) n with
           | True ->
             Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               O))))))))))))))))))))))))))))))))))))
           | False -> False with
     | True -> Nat.even n
     | False -> False)
  | LowBet ->
    (match Nat.leb (S O) n with
     | True ->
       Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))
     | False -> False)
  | HighBet ->
    (match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             O))))))))))))))))))) n with
     | True ->
       Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))))
     | False -> False)

(** val payout_ratio : bet_type -> nat **)

let payout_ratio = function
| Straight _ ->
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))
| Split (_, _) ->
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))
| Street _ -> S (S (S (S (S (S (S (S (S (S (S O))))))))))
| Corner (_, _, _, _) -> S (S (S (S (S (S (S (S O)))))))
| SixLine (_, _) -> S (S (S (S (S O))))
| Trio _ -> S (S (S (S (S (S (S (S (S (S (S O))))))))))
| Basket -> S (S (S (S (S (S O)))))
| FiveNumber -> S (S (S (S (S (S O)))))
| Column _ -> S (S O)
| Dozen _ -> S (S O)
| _ -> S O

(** val net_return : bet_type -> nat -> nat -> nat **)

let net_return b stake outcome =
  match bet_wins b outcome with
  | True -> add stake (mul stake (payout_ratio b))
  | False -> O

(** val count_wins : bet_type -> nat **)

let count_wins b =
  length (filter (bet_wins b) (seq O n_POCKETS))

(** val fairness_product : bet_type -> nat **)

let fairness_product b =
  mul (count_wins b) (add (payout_ratio b) (S O))

(** val table_adjacent_directed : nat -> nat -> bool **)

let table_adjacent_directed a b =
  match match match match Nat.leb (S O) a with
                    | True ->
                      Nat.leb a (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        O)))))))))))))))))))))))))))))))))
                    | False -> False with
              | True -> Nat.eqb b (add a (S (S (S O))))
              | False -> False with
        | True -> True
        | False ->
          (match match match Nat.leb (S O) a with
                       | True ->
                         Nat.leb a (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                           (S (S (S (S O)))))))))))))))))))))))))))))))))))
                       | False -> False with
                 | True -> Nat.eqb b (add a (S O))
                 | False -> False with
           | True -> negb (Nat.eqb (Nat.modulo a (S (S (S O)))) O)
           | False -> False) with
  | True -> True
  | False ->
    (match Nat.eqb a O with
     | True ->
       (match match Nat.eqb b (S O) with
              | True -> True
              | False -> Nat.eqb b (S (S O)) with
        | True -> True
        | False -> Nat.eqb b (S (S (S O))))
     | False -> False)

(** val table_adjacent : nat -> nat -> bool **)

let table_adjacent a b =
  match table_adjacent_directed a b with
  | True -> True
  | False -> table_adjacent_directed b a

(** val well_formed_dec : bet_type -> bool **)

let well_formed_dec = function
| Straight k -> Nat.ltb k n_POCKETS
| Split (a, b0) ->
  (match match Nat.ltb a n_POCKETS with
         | True -> Nat.ltb b0 n_POCKETS
         | False -> False with
   | True -> table_adjacent a b0
   | False -> False)
| Street row ->
  (match Nat.leb (S O) row with
   | True -> Nat.leb row (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))
   | False -> False)
| Corner (a, b0, c, d) ->
  (match match match match match Nat.leb (S O) a with
                           | True ->
                             Nat.leb a (S (S (S (S (S (S (S (S (S (S (S (S (S
                               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                               (S (S (S (S O))))))))))))))))))))))))))))))))
                           | False -> False with
                     | True -> negb (Nat.eqb (Nat.modulo a (S (S (S O)))) O)
                     | False -> False with
               | True -> Nat.eqb b0 (add a (S O))
               | False -> False with
         | True -> Nat.eqb c (add a (S (S (S O))))
         | False -> False with
   | True -> Nat.eqb d (add a (S (S (S (S O)))))
   | False -> False)
| SixLine (r1, r2) ->
  (match match match match Nat.leb (S O) r1 with
                     | True ->
                       Nat.leb r1 (S (S (S (S (S (S (S (S (S (S (S (S
                         O))))))))))))
                     | False -> False with
               | True -> Nat.leb (S O) r2
               | False -> False with
         | True ->
           Nat.leb r2 (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))
         | False -> False with
   | True ->
     (match Nat.eqb r2 (add r1 (S O)) with
      | True -> True
      | False -> Nat.eqb r1 (add r2 (S O)))
   | False -> False)
| Trio v ->
  (match Nat.eqb v (S O) with
   | True -> True
   | False -> Nat.eqb v (S (S O)))
| FiveNumber -> False
| Column col ->
  (match Nat.leb (S O) col with
   | True -> Nat.leb col (S (S (S O)))
   | False -> False)
| Dozen doz ->
  (match Nat.leb (S O) doz with
   | True -> Nat.leb doz (S (S (S O)))
   | False -> False)
| _ -> True

(** val expected_return_numerator : bet_type -> nat -> nat **)

let expected_return_numerator b stake =
  fold_left Nat.add (map (net_return b stake) (seq O n_POCKETS)) O

(** val rejection_bound : nat -> nat **)

let rejection_bound n =
  mul n_POCKETS (Nat.div n n_POCKETS)

(** val simulate_spin : bet_type -> nat -> nat -> nat **)

let simulate_spin b stake raw =
  net_return b stake (rng_to_pocket raw)

(** val simulate_session : bet_type -> nat -> nat list -> nat **)

let simulate_session b stake raws =
  fold_left Nat.add (map (simulate_spin b stake) raws) O
