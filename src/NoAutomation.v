(* It's for a person who thinks we shouldn't use
  the Coq automation process.
*)

Require Import Auxiliaries.
Require Import Nat List Bool Arith Omega.
Import ListNotations.

Require Import Coq.Structures.Equalities.

Parameter A: Type.

Module AType <: Typ with Definition t := A.
Definition t := A.
End AType.

Module NARemover := (NthInserterRemover AType).
Import NARemover.

Lemma nth_remove_overflow: forall n l,
  n >= length l <->
  nth_remove n l = l.
Proof.
  induction n; destruct l; intros; split; intros.
  - reflexivity. (* 1 *)
  - apply le_n. (* 2 *)
  - inversion H. (* 3 *)
  - apply not_lt. unfold not. intros. (* 4 *)
    apply f_equal with (f:=@length A) in H. simpl in H.
    induction (length l).
    + inversion H.
    + inversion H. apply IHn in H2.
      apply H2.
  - reflexivity. (* 5 *)
  - apply le_0_n. (* 6 *)
  - simpl in *. apply le_S_n in H. apply IHn in H. (* 7 *)
    rewrite H. reflexivity.
  - inversion H. apply IHn in H1. (* 8 *)
    apply f_equal with (B := list A) (f:=@tl A) in H. simpl in H.
    rewrite <- H in H1.
    apply le_n_S. apply H1.
Qed.

Lemma nth_remove_overflow2: forall n l,
  n >= length l <->
  nth_remove n l = l.
Proof.
  induction n; destruct l; intros; simpl in *; intuition.
  - easy.
  - apply f_equal with (B := nat) (f:=@length A) in H. simpl in H.
    intuition.
  - assert (e: n >= length l) by omega; apply (IHn _) in e; rewrite e.
    auto.
  - inversion H as [H']; rewrite H'; apply IHn in H'. omega.
Qed.