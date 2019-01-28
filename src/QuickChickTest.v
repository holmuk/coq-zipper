Require Import Auxiliaries.
Require Import Nat List Bool Arith Omega.

From QuickChick Require Import QuickChick.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Require Import Coq.Structures.Equalities.

(**
  Just to be sure, the correctness of some of our definitions and lemmas are
  "proved" with QuickChick
*)

Module NatType <: Typ with Definition t := nat.
Definition t := nat.
End NatType.

Module InserterRemoverOverNat := (NthInserterRemover NatType).
Import InserterRemoverOverNat.

Definition genInput : G (nat * (list nat)) :=
  genPair (choose (0, 100)) (listOf (choose (0, 100))).

Definition nth_remove_length_check n (l : list nat) :=
  ((n <? length l) && ((length (nth_remove n l)) =? (pred (length l))))
  ||
  ((length l <=? n) && ((length (nth_remove n l)) =? (length l))).

Definition nth_insert_length_check n (l: list nat) x :=
  ((n <=? length l) && (length (nth_insert n l x) =? (succ (length l))))
  ||
  ((length l <? n) && ((length (nth_insert n l x)) =? (length l))).

Definition nth_insert_prop n (l : list nat) x :=
  ((n <=? length l) &&
   (0 <? length (filter (fun x' => (x' =? x)) (nth_insert n l x))))
  || (length l <? n).

Definition qc_test_remove_length (nl: prod nat (list nat)) :=
  nth_remove_length_check (fst nl) (snd nl).
Definition qc_test_insert_length (nl: prod nat (list nat)) :=
  nth_insert_length_check (fst nl) (snd nl).
Definition qc_test_insert_prop (nl: prod nat (list nat)) :=
  nth_insert_prop (fst nl) (snd nl).

QuickChick (forAll genInput qc_test_remove_length).
QuickChick (forAll genInput qc_test_insert_length).
QuickChick (forAll genInput qc_test_insert_prop).
