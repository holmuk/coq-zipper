Require Import TreeZipper.

Require Import Nat List Bool Arith Omega.
From QuickChick Require Import QuickChick.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.

(* QuickCheck of lists over nat *)

Require Import Coq.Structures.Equalities.

Module NatType <: Typ with Definition t := nat.
Definition t := nat.
End NatType.

Module Nn := (NthRemover NatType).
Import Nn.

Definition nth_remove_length_check n (l : list nat) :=
  orb
  (andb (andb (0 <=? n) (n <? length l))
  ((length (nth_remove n l)) =? (pred (length l))))
  (andb (length l <=? n)
  ((length (nth_remove n l)) =? (length l))).

QuickChick nth_remove_length_check.

