(* Just a realization of an arbitrary tree Zipper to taste the background *)


(** * Tree Zipper
  Just for fun
*)

Require Import Nat List Bool Arith Omega.
Import ListNotations.

Require Import Coq.Structures.Equalities.
Require Import Auxiliaries.

Module TreeZipper (Import T: Typ).

(*Parameter A : Type.
*)

Definition A := T.t.

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

Definition MoveTopAction (T: Tree) (Zop: Context) : Tree :=
  match Zop with
  | T_move n a l =>
    T_tr a (nth_insert n l T)
  end.

Definition MoveTop (Z: ZipperTree) :=
  match (snd Z) with
  | [] => Z
  | h::t => match h with
    | T_move n a l =>
      pair (MoveTopAction (fst Z) h) t
      (* pair (T_tr a (nth_insert n l (fst Z))) t *)
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
Hint Unfold MoveTop MoveDown MoveTopAction TreeToZipper ZipperTree NodesOf : t_unfold.

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

Definition Modify (Z: ZipperTree) (f: Tree -> Tree) : ZipperTree :=
  pair (f (fst Z)) (snd Z).

Definition ZipperToTree (Z: ZipperTree) : Tree :=
  fold_left MoveTopAction (snd Z) (fst Z).

Hint Unfold Modify ZipperToTree : t_unfold.

Lemma ZipToTreeIdentity: forall T,
  ZipperToTree (TreeToZipper T) = T.
Proof.
  auto.
Qed.

Lemma MoveTop_TreeInvariance: forall Z,
  ZipperToTree Z = ZipperToTree (MoveTop Z).
Proof.
  destruct Z as (t, l), l as [|h]; [|destruct h]; simpl in *; auto.
Qed.

Lemma MoveDown_TreeInvariance: forall D Z,
  CorrectMoveDownConditions D Z ->
  ZipperToTree (MoveDown D Z) = ZipperToTree Z.
Proof.
  autounfold with t_unfold in *; destruct Z as (t, l), t, l;
    simpl; auto; intros.
  - remember H as H' eqn:Ge; clear Ge.
    apply nth_error_Some in H. destruct (nth_error l0 D) eqn:R; simpl; auto.
    rewrite nth_insert_remove; auto.
  - remember H as H' eqn:Ge; clear Ge.
    apply nth_error_Some in H. destruct (nth_error l0 D) eqn:R; simpl; auto.
    rewrite nth_insert_remove; auto.
Qed.

Lemma Modify_Identity: forall Z,
  Modify Z (fun t => t) = Z.
Proof.
  destruct Z; auto.
Qed.

Lemma Context_Modify: forall Z f,
  f (fst Z) = fst (Modify Z f).
Proof.
  auto.
Qed.

(* Property *)

Lemma MoveTopActionNotNil: forall T Zop,
  MoveTopAction T Zop <> T_nil.
Proof.
  destruct T, Zop; unfold not; intro; discriminate.
Qed.

Lemma ZipperToTreeNotNil: forall l t,
  t <> T_nil \/ l <> [] ->
  ZipperToTree (t, l) <> T_nil.
Proof.
  unfold ZipperToTree; simpl. intro;
  induction l using (induction_ltof1 _ (@length _)).
  unfold ltof in H. intros. induction l.
  - simpl; intuition.
  - destruct a; simpl. apply H; auto. left. unfold not; discriminate.
Qed.

Inductive IsSubtreeOf: Tree -> Tree -> Prop :=
  | ISO_refl: forall T,
    IsSubtreeOf T T
  | ISO_subtree: forall T l a,
    In T l -> IsSubtreeOf T (T_tr a l)
  | ISO_trans: forall T T' T'',
    IsSubtreeOf T T'-> IsSubtreeOf T' T'' ->
    IsSubtreeOf T T''.

Add Relation (Tree) (@IsSubtreeOf)
  reflexivity proved by (@ISO_refl)
  transitivity proved by (@ISO_trans)
as ISO_relation.

Hint Constructors IsSubtreeOf.

Definition CorrectMoveTopActionConditions Zop : Prop :=
  match Zop with
  | T_move n a l =>
    n <= length l
  end.

Definition CorrectZipperToTreeConditions (Z : ZipperTree) : Prop :=
  forall t, In t (snd Z) -> match t with | T_move n a l => n <= length l end.

Hint Unfold CorrectZipperToTreeConditions CorrectMoveTopActionConditions : t_unfold.

Lemma ZipperSubtree: forall tr l,
  CorrectZipperToTreeConditions (tr, l) ->
  IsSubtreeOf tr (ZipperToTree (tr, l)).
Proof.
  intros; generalize dependent tr.
  induction l. intros; auto. intros.
  remember H as H' eqn:He; clear He.
  unfold CorrectZipperToTreeConditions in *.
  - specialize H with a. simpl in H.
    destruct a; unfold ZipperToTree in *; simpl in *.
    transitivity (T_tr a (nth_insert n l0 tr)); auto.
    assert (n <= length l0) by auto.
    apply nth_insert_representation with (x:=tr) in H; firstorder. rewrite H1.
    constructor. auto with datatypes.
  - apply IHl. intros. apply H'; auto.
Qed.

Inductive PropertyOverTree : (Tree -> Prop) -> Tree -> Prop :=
  | P_nil: forall (P: Tree -> Prop),
    P T_nil -> PropertyOverTree P T_nil
  | P_tree: forall (P: Tree -> Prop) T,
    P T -> (forall T', IsSubtreeOf T' T -> P T') ->
    PropertyOverTree P T.

Hint Constructors PropertyOverTree.

Lemma ZipperPreserveProperty: forall P T,
  PropertyOverTree P T ->
  (forall Z, CorrectZipperToTreeConditions Z ->
    ZipperToTree Z = T -> PropertyOverTree P (fst Z)).
Proof.
  induction 1; intros.
  - assert (e: Z = (T_nil, [])).
      destruct Z as (t, l), t, l; auto; apply ZipperToTreeNotNil in H1.
      all: firstorder; try discriminate.
    rewrite e in *; simpl in *. auto.
  - destruct T.
    assert (e: Z = (T_nil, [])).
      destruct Z as (t, l), t, l; auto; apply ZipperToTreeNotNil in H2.
      all: firstorder; try discriminate.
    rewrite e in *; simpl in *. auto.
  - constructor.
    assert (e: IsSubtreeOf (fst Z) (ZipperToTree Z)).
      destruct Z; apply ZipperSubtree; auto.
    rewrite H2 in e. apply H0 in e; auto.
  - assert (e: IsSubtreeOf (fst Z) (ZipperToTree Z)).
      destruct Z; apply ZipperSubtree; auto.
    rewrite H2 in e.
    intros. apply H0. transitivity (fst Z); auto.
Qed.

End TreeZipper.
