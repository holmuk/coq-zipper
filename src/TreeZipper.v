(* Just a realization of an arbitrary tree Zipper to taste the background *)

Require Import Nat List Bool Arith.
Import ListNotations.

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

End TreeZipper.
