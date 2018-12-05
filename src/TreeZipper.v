(* Just a realization of an arbitrary tree Zipper to taste the background *)

Require Import Nat List Bool Arith Omega.
From QuickChick Require Import QuickChick.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Require Import Coq.Structures.Equalities.

Module NthRemover (Import T : Typ).

Definition A := T.t.

Fixpoint nth_remove n l : list A :=
  match n, l with
  | _, [] => []
  | 0, h::t => t
  | S n', h::t => h :: nth_remove n' t
  end.

Lemma nth_remove_works: forall n l,
  0 <= n < length l ->
  length (nth_remove n l) = (length l) - 1.
Proof.
  intros.
  generalize dependent n; induction l; intros. simpl in *.
  - destruct n; auto.
  - simpl in *. rewrite <- minus_n_O in *.
    destruct n; simpl in *; auto.
    assert (e: 0 <= n < length l) by omega; apply IHl in e; rewrite e.
    omega.
Qed.

Lemma nth_remove_representation: forall n (l: list A),
  0 <= n < length l ->
  exists x lh lt, Some x = nth_error l n /\
    l = lh ++ x::lt /\ nth_remove n l = lh ++ lt.
Proof.
  intros.
  generalize dependent n; induction l; intros; simpl in *.
  - assert (Absurd: 0 < 0) by omega; inversion Absurd.
  - destruct n; simpl in *. exists a; exists []; exists l. intuition.
    assert (e: 0 <= n < length l) by omega; apply IHl in e; destruct e as [q0 [q1 [q3 ]]].
    intuition. rewrite H4. exists q0. exists (a::q1). exists q3. intuition.
    rewrite H0. intuition.
Qed.

Lemma nth_remove_overflow: forall n l,
  n >= length l <->
  nth_remove n l = l.
Proof.
  induction n; destruct l; intros; simpl in *; intuition.
  - inversion H.
  - apply f_equal with (B := nat) (f:=@length A) in H. simpl in H.
    intuition.
  - assert (e: n >= length l) by omega; apply (IHn _) in e; rewrite e.
    auto.
  - inversion H as [H']; rewrite H'; apply IHn in H'. omega.
Qed.

End NthRemover.

Module NthInserter (Import T : Typ).

Definition A := T.t.

Fixpoint nth_insert n l x : list A :=
  match n, l with
  | _, [] => []
  | 0, _ => x::l
  | S n', h::t => h::(nth_insert n' t x)
  end.

Lemma nth_insert_length: forall n l x,
  0 <= n < length l ->
  length (nth_insert n l x) = S (length l).
Proof.
  intros.
  generalize dependent n; induction l; intros; simpl in *.
  - intuition.
  - destruct n; simpl in *; auto.
    assert (e: 0 <= n < length l) by omega; apply IHl in e; rewrite e.
    omega.
Qed.

Lemma nth_insert_representation: forall n (l: list A) x,
  0 <= n < length l ->
  Some x = nth_error (nth_insert n l x) n /\
  exists lh lt, nth_insert n l x = lh ++ x::lt /\ l = lh ++ lt.
Proof.
  intros.
  generalize dependent n; induction l; intros; simpl in *.
  - assert (Absurd: 0 < 0) by omega; inversion Absurd.
  - destruct n; simpl in *. split; [auto | exists []; exists (a::l)]; intuition.
    assert (e: 0 <= n < length l) by omega; apply IHl in e; destruct e as [q0 [q1 [q3 ]]].
    intuition. rewrite H. exists (a::q1); exists q3. rewrite H3. intuition.
Qed.

Lemma nth_insert_overflow: forall n l x,
  n >= length l <->
  nth_insert n l x = l.
Proof.
  induction n; destruct l; intros; simpl in *; intuition.
  - inversion H.
  - apply f_equal with (B := nat) (f:=@length A) in H. simpl in H.
    intuition.
  - assert (e: n >= length l) by omega; apply (IHn _ x) in e; rewrite e.
    auto.
  - inversion H as [H']; rewrite H'; apply IHn in H'. omega.
Qed.

End NthInserter.

Module TreeZipper.

Parameter A : Type.

Inductive Tree : Type :=
  | BT_nil: Tree
  | BT_tr:  A -> list Tree -> Tree.

Inductive Context : Type :=
  | BT_move: nat -> A -> list Tree -> Context.

Definition ZipperTree :=
  prod Tree (list Context).

Definition TreeToZipper (T: Tree) : ZipperTree :=
  pair T [].

Definition Direction := nat.

Module AType <: Typ with Definition t := Tree.
Definition t := Tree.
End AType.

Module NAremover := (NthRemover AType).
Module NAinserter := (NthInserter AType).
Import NAremover.
Import NAinserter.

Definition MoveTop (Z: ZipperTree) :=
  match (snd Z) with
  | [] => Z
  | h::t => match h with
    | BT_move n a l =>
      pair (BT_tr a (nth_insert n l (fst Z))) t
    end
  end.

End TreeZipper.
