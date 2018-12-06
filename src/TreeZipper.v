(* Just a realization of an arbitrary tree Zipper to taste the background *)

Require Import Nat List Bool Arith Omega.
From QuickChick Require Import QuickChick.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Require Import Coq.Structures.Equalities.

Module NthInserterRemover (Import T : Typ).

Definition A := T.t.

Fixpoint nth_remove n l : list A :=
  match n, l with
  | _, [] => []
  | 0, h::t => t
  | S n', h::t => h :: nth_remove n' t
  end.

Lemma nth_remove_length: forall n l,
  n < length l ->
  length (nth_remove n l) = (length l) - 1.
Proof.
  intros.
  generalize dependent n; induction l; intros. simpl in *.
  - destruct n; auto.
  - simpl in *. rewrite <- minus_n_O in *.
    destruct n; simpl in *; auto.
    assert (e: n < length l) by omega; apply IHl in e; rewrite e.
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
  - inversion H.
  - destruct n; simpl in *. exists a; exists []; exists l. intuition.
    assert (e: n < length l) by omega; apply IHl in e; destruct e as [q0 [q1 [q3 ]]].
    intuition. exists q0, (a::q1), q3. rewrite H1, H2, H0. rewrite <- H3.
    ssimpl_list. intuition.
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
  - inversion H. simpl. intuition.
  - destruct n; simpl in *; auto.
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
  induction n; destruct l; intros; simpl in *; intuition.
  - inversion H.
  - inversion H.
  - inversion H.
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

Module TreeZipper.

Parameter A : Type.

Inductive Tree : Type :=
  | T_nil: Tree
  | T_tr:  A -> list Tree -> Tree.

Inductive Context : Type :=
  | T_move: nat -> A -> list Tree -> Context.

Definition ZipperTree :=
  prod Tree (list Context).

Definition TreeToZipper (T: Tree) : ZipperTree :=
  pair T [].

Definition Direction := nat.

Module AType <: Typ with Definition t := Tree.
Definition t := Tree.
End AType.

Module NAremover := (NthInserterRemover AType).
Import NAremover.

Definition MoveTop (Z: ZipperTree) :=
  match (snd Z) with
  | [] => Z
  | h::t => match h with
    | T_move n a l =>
      pair (T_tr a (nth_insert n l (fst Z))) t
    end
  end.

Definition MoveDown (D: Direction) (Z: ZipperTree) : ZipperTree :=
  match (fst Z) with
  | T_nil => Z
  | T_tr a l =>
    match (nth_error l D) with
    | None => Z
    | Some T => pair T ((T_move D a (nth_remove D l))::(snd Z))
    end
  end.

Definition NodesOf (T: Tree) : list Tree :=
  match T with
  | T_nil => []
  | T_tr _ l => l
  end.

Definition CorrectMoveDownConditions (D: Direction) (Z: ZipperTree) :=
  D < length (NodesOf (fst Z)).

Definition CorrectMoveTopConditions (Z: ZipperTree) :=
  (snd Z) <> [].

Hint Unfold CorrectMoveTopConditions CorrectMoveDownConditions : t_unfold.
Hint Unfold MoveTop MoveDown TreeToZipper ZipperTree NodesOf : t_unfold.

Lemma MoveTopDown: forall D Z,
  CorrectMoveDownConditions D Z ->
  MoveTop (MoveDown D Z) = Z.
Proof.
  autounfold with t_unfold in *; destruct Z as (t, l), t, l; simpl; intros.
  - inversion H.
  - inversion H.
  - remember H as H' eqn:Ge; clear Ge.
    apply nth_error_Some in H. destruct (nth_error l0 D) eqn:R.
    simpl. rewrite nth_insert_remove; auto.
  - contradiction.
  - remember H as H' eqn:Ge; clear Ge.
    apply nth_error_Some in H. destruct (nth_error l0 D) eqn:R.
    simpl. rewrite nth_insert_remove; auto.
  - destruct c; simpl. exfalso. apply H; auto.
Qed.

End TreeZipper.
