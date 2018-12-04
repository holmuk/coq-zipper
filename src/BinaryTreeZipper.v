(* Just a realization of binary tree Zipper to taste the background *)

Require Import Nat List Bool Arith.
Import ListNotations.

Module BinaryTreeZipper.

Parameter A : Type.

Inductive BinaryTree : Type :=
  | BT_nil: BinaryTree
  | BT_tr:  A -> BinaryTree -> BinaryTree -> BinaryTree.

Inductive Context : Type :=
  | BT_TL: A -> BinaryTree -> Context
  | BT_TR: A -> BinaryTree -> Context.

Definition ZipperTree :=
  prod BinaryTree (list Context).

Definition BinaryTreeToZipper (BT: BinaryTree) : ZipperTree :=
  pair BT [].

Inductive Direction : Type :=
  | D_L: Direction
  | D_R: Direction.

Definition MoveDown (D: Direction) (Z: ZipperTree) : ZipperTree :=
  match (fst Z), D with
  | BT_nil, _ => Z
  | (BT_tr x L R), D_L => (L, (BT_TL x R)::(snd Z))
  | (BT_tr x L R), D_R => (R, (BT_TR x L)::(snd Z))
  end.

Definition MoveTopAction (T: BinaryTree) (Zop: Context) : BinaryTree :=
  match Zop with
  | BT_TL x T' => BT_tr x T T'
  | BT_TR x T' => BT_tr x T' T
  end.

Definition MoveTop (Z: ZipperTree) : ZipperTree :=
  match (snd Z) with
  | [] => Z
  | h::t => pair (MoveTopAction (fst Z) h) t
  end.

Definition Modify (Z: ZipperTree) (f: BinaryTree -> BinaryTree) : ZipperTree :=
  pair (f (fst Z)) (snd Z).

Definition ZipperToBinaryTree (Z: ZipperTree) : BinaryTree :=
  fold_left MoveTopAction (snd Z) (fst Z).

Hint Unfold ZipperTree ZipperToBinaryTree BinaryTreeToZipper : ziptree_unfold.
Hint Unfold MoveTop MoveDown MoveTopAction Modify : ziptree_unfold.

(* Now is lemma's time! *)

Lemma ZipToTreeIdentity: forall T,
  ZipperToBinaryTree (BinaryTreeToZipper T) = T.
Proof.
  auto.
Qed.

Lemma MoveTop_TreeInvariance: forall Z,
  ZipperToBinaryTree Z = ZipperToBinaryTree (MoveTop Z).
Proof.
  destruct Z as (t, l); induction l; auto.
Qed.

Lemma ModeDown_TreeInvariance: forall D Z,
  ZipperToBinaryTree (MoveDown D Z) = ZipperToBinaryTree Z.
Proof.
  destruct Z as (t, l), D; induction t; auto.
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

(* Navigation lemmas *)

Lemma MoveTopDown: forall D Z,
  (fst Z) <> BT_nil ->
  MoveTop (MoveDown D Z) = Z.
Proof.
  destruct Z as (t, l), D, t; intuition.
Qed.

Definition BinaryTree_Subtree BT (D: Direction) :=
  match BT, D with
  | BT_nil, _ => BT
  | (BT_tr x L R), D_L => L
  | (BT_tr x L R), D_R => R
  end.

Hint Unfold BinaryTree_Subtree : ziptree_unfold.

Lemma MoveDown_Subtree_Eq: forall Z D,
  BinaryTree_Subtree (fst Z) D = fst (MoveDown D Z).
Proof.
  destruct Z as (t, l), D, t; auto.
Qed.

End BinaryTreeZipper.
