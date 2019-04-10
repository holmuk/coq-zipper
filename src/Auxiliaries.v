
(**
  Various auxiliary things
*)

Require Import Nat Bool Arith Omega.
Require Import Coq.Structures.Equalities.
Require Import Coq.Arith.Wf_nat.

(** * Insert and Remove
  To describe some operations we need we have to define what is to "insert" or to
  "remove" an element at nth position to or from the list.
  The existing Coq functions use Option A as a return type, but we want to keep
  things as simple as possible. So our functions "work" even when incorrect values
  are passed in.
*)

Require Import List.
Import ListNotations.
Module NthInserterRemover (Import T : Typ).

Definition A := T.t.

(**
  It works as we want when n < length l
  See lemmas below
*)

Fixpoint nth_remove n l : list A :=
  match n, l with
  | _, [] => []
  | 0, h::t => t
  | S n', h::t => h :: nth_remove n' t
  end.

Lemma nth_remove_length: forall n (l: list A),
  n < length l ->
  length (nth_remove n l) = (length l) - 1.
Proof.
  intros. generalize dependent n.
  induction l; intros; simpl in *; destruct n; intuition.
  assert (e: n < length l) by omega. apply IHl in e. simpl. rewrite e.
  omega.
Qed.

Lemma nth_remove_representation: forall n (l: list A),
  n < length l ->
  exists x lh lt, Some x = nth_error l n /\
    l = lh ++ x::lt /\ nth_remove n l = lh ++ lt
    /\ length lh = n /\ length lt = (length l) - n - 1.
Proof.
  intros.
  generalize dependent n; induction l; intros; simpl in *.
  - easy.
  - destruct n; simpl in *. exists a, [], l; intuition.
    assert (e: n < length l) by omega; apply IHl in e; destruct e as [q0 [q1 [q3 ]]].
    intuition. exists q0, (a::q1), q3. rewrite H1, H2, H0. rewrite <- H3.
    ssimpl_list. intuition.
Qed.

Lemma nth_remove_overflow: forall n l,
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

(**
  It works as we want when n <= length l
  See lemmas below
*)

Fixpoint nth_insert n l x : list A :=
  match n, l with
  | 0, _ => x::l
  | _, [] => []
  | S n', h::t => h::(nth_insert n' t x)
  end.

Lemma nth_insert_length: forall n l x,
  n <= length l ->
  length (nth_insert n l x) = S (length l).
Proof.
  intros.
  generalize dependent n; induction l; intros; simpl in *.
  - inversion H. intuition.
  - destruct n; auto.
    simpl.
    assert (e: n <= length l) by omega; apply IHl in e; rewrite e.
    reflexivity.
Qed.

Lemma nth_insert_representation: forall n (l: list A) x,
  n <= length l ->
  Some x = nth_error (nth_insert n l x) n /\
  exists lh lt, nth_insert n l x = lh ++ x::lt /\ l = lh ++ lt
    /\ length lh = n /\ length lt = (length l) - n.
Proof.
  intros.
  generalize dependent n; induction l; intros; simpl in *.
  - inversion H. simpl. split; [auto | exists [], []]. intuition.
  - destruct n; simpl in *. split; [auto | exists [], (a::l)]; intuition.
    assert (e: n <= length l) by omega; apply IHl in e; destruct e as [q0 [q1 [q3 ]]].
    intuition. exists (a::q1), q3; simpl. rewrite H1, H4, H0. auto.
Qed.

Lemma nth_insert_overflow: forall n l x,
  n > length l <->
  nth_insert n l x = l.
Proof.
  induction n; destruct l; intros; simpl in *; intuition; try easy.
  - apply f_equal with (B := nat) (f:=@length A) in H. simpl in H.
    intuition.
  - assert (e: n > length l) by omega; apply (IHn _ x) in e; rewrite e.
    auto.
  - inversion H as [H']; rewrite H'; apply IHn in H'. omega.
Qed.

Lemma nth_insert_app: forall l1 l2 x,
  nth_insert (length l1) (l1 ++ l2) x = l1 ++ x::l2.
Proof.
  intros. induction l1; auto.
  simpl; rewrite IHl1; auto.
Qed.

(**
  A link between nth_insert and nth_remove functions
*)

Lemma nth_insert_remove: forall n l x,
  n < length l ->
  Some x = nth_error l n ->
  (nth_insert n (nth_remove n l) x) = l.
Proof.
  intros.
  remember H as H' eqn: Heq; clear Heq.
  assert (n <= length (nth_remove n l)).
    apply nth_remove_length in H; rewrite H; omega.
  apply nth_insert_representation with (x:=x) in H1. firstorder.
  apply nth_remove_representation in H. firstorder.
  rewrite H3 in H7. rewrite <- H0 in H. inversion H. rewrite H2, H6. subst.
  apply f_equal with (f := fun l => (nth_insert (length x0) l x)) in H7.
  rewrite <- H8 in H7 at 2.
  repeat rewrite nth_insert_app in H7.
  auto.
Qed.

End NthInserterRemover.
