(* Just a realization of binary tree Zipper to taste the background *)

Require Import Nat List Bool Arith.
Require Import Coq.Sets.Ensembles.
Import ListNotations.

Section BinaryTreeZipper.

Variable A : Type.

Inductive BinaryTree : Type :=
  | BT_nil: BinaryTree
  | BT_tr:  A -> BinaryTree -> BinaryTree -> BinaryTree.

Inductive ContextBinaryTree : Type :=
  | BT_TL: A -> BinaryTree -> ContextBinaryTree
  | BT_TR: A -> BinaryTree -> ContextBinaryTree.

Definition ZipperTree :=
  prod BinaryTree (list ContextBinaryTree).

Fixpoint In_order_traverse (BT: BinaryTree) (f: A -> A) : list A :=
  match BT with
  | BT_nil => nil
  | BT_tr x t1 t2 =>
    (In_order_traverse t1 f) ++ [f x] ++ (In_order_traverse t2 f)
  end.

Definition BT_get_list (BT: BinaryTree) := In_order_traverse BT
  (fun x:A => x).

Definition TreeUpAction (T: BinaryTree) (Zop: ContextBinaryTree) : BinaryTree :=
  match Zop with
  | BT_TL x T' => BT_tr x T T'
  | BT_TR x T' => BT_tr x T' T
  end.

Inductive Direction : Type :=
  | D_L: Direction
  | D_R: Direction.

Definition TreeDown (D: Direction) (Z: ZipperTree) : ZipperTree :=
  match (fst Z), D with
  | BT_nil, _ => Z
  | (BT_tr x L R), D_L => (L, (BT_TL x R)::(snd Z))
  | (BT_tr x L R), D_R => (R, (BT_TR x L)::(snd Z))
  end.

Definition TreeUp (Z: ZipperTree) : ZipperTree :=
  match (snd Z) with
  | [] => Z
  | h::t => pair (TreeUpAction (fst Z) h) t
  end.

Definition UnzipTree (Z: ZipperTree) : BinaryTree :=
  fold_left TreeUpAction (snd Z) (fst Z).

Lemma TreeUpInvariance: forall Z,
  UnzipTree (TreeUp Z) = UnzipTree Z.
Proof.
  intros. destruct Z. induction l; unfold UnzipTree; reflexivity.
Qed.

Lemma TreeDownInvariance: forall D Z,
  UnzipTree (TreeDown D Z) = UnzipTree Z.
Proof.
  intros. destruct Z, D;
  induction b; simpl; auto.
Qed.

Hint Unfold TreeUp.

Lemma TreeUpDown: forall D Z,
  (fst Z) <> BT_nil -> 
  TreeUp (TreeDown D Z) = Z.
Proof.
  intros. unfold TreeDown; destruct Z, D.
  all: destruct b; simpl in *; try contradiction.
  all: auto.
Qed.

End BinaryTreeZipper.

Example Get_list_nat_one: forall (x: nat),
  BT_get_list nat (BT_tr nat x (BT_nil nat) (BT_nil nat)) = [x].
Proof.
  auto.
Qed.



