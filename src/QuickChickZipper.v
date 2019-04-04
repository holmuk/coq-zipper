Require Import Auxiliaries.
Require Import TreeZipper.
Require Import Nat Bool Arith Omega.

Require Import String.
Require Import List.

From QuickChick Require Import QuickChick.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Require Import Coq.Structures.Equalities.

Module NatType <: Typ with Definition t := nat.
Definition t := nat.
End NatType.

Module TreeZipperOverNat := (TreeZipper.TreeZipperDef NatType).
Import TreeZipperOverNat.

Instance showTree `{_ : Show } : Show (Tree) :=
  {| show :=
      let fix aux t := match t with
        | T_nil => " nil "
        | T_tr x l =>
        let fix printl x' l' := match l' with
          | [] => "{" ++ show x' ++ "}"
          | a::li' => (aux a) ++ (printl x' li')
          end in "<" ++ printl x l ++ ">"
      end in aux
  |}.

Instance showContext `{_ : Show } : Show (Context) :=
  {| show :=
      (fun t => match t with
        | T_move n x l =>
          "cntx {" ++ show n ++ "} {" ++ show x ++ "} {" ++ show l ++ "}"
        end)
  |}.

Fixpoint genTreeSized (sz: nat) (g: G A) : G (Tree) :=
  match sz with
  | 0 => returnGen T_nil
  | S sz' =>
    freq [ (1, returnGen T_nil) ;
      (sz, bindGen g (fun x =>
           bindGen (@listOf (Tree) (genTreeSized sz' g)) (fun l =>
         returnGen (T_tr x l)))) ]
  end.

Definition genTreeList (g: G nat) (gT: G Tree) : G (list Tree) :=
  sized (fun n => bindGen g (fun k => vectorOf k gT)).

(*Definition genTree (g: G A) : G (Tree) :=
  sized (fun n => bindGen (choose (0, n)) (fun k => genTreeSized k g)).
*)

Definition genTree (g: G nat) (gA: G A) : G (Tree) :=
  bindGen g (fun n => genTreeSized n g).

Fixpoint treeTraverse (T: Tree) : list nat :=
  match T with
  | T_nil => []
  | T_tr x l =>
    [x] ++ concat (map (treeTraverse) l)
  end.

Fixpoint tree_cnt (T: Tree) : nat :=
  match T with
  | T_nil => 0
  | T_tr x l =>
    1 + fold_right (fun x => fun y => x + y) 0 (map tree_cnt l)
  end.

Definition genContext (g: G nat) (g' : G A) (gT: G Tree) : G (Context) :=
  bindGen g (fun x =>
    bindGen g (fun y =>
      bindGen g' (fun a =>
        bindGen (genTreeList g gT) (fun lt =>
          returnGen (T_move ((max x y) - 1 - (min x y)) a lt))))).

Definition genContextList (g: G nat) (gC : G Context) : G (list Context) :=
    sized (fun n => bindGen g (fun k => vectorOf k gC)).

Definition genZipper (g: G nat) (gA : G A) : G (ZipperTree) :=
  bindGen (genTree g gA) (fun t =>
    bindGen (genContextList g (genContext g gA (genTree g gA))) (fun lC =>
      returnGen (t, lC))).

Definition qc_cnt_traverse (T: Tree) :=
  beq_nat (tree_cnt T) (List.length (treeTraverse T)).

Definition eq_tree (T T': Tree) : bool :=
  let lT := (treeTraverse T) in let lT' := (treeTraverse T') in
  (beq_nat (length lT) (length lT')) &&
  forallb (fun p => beq_nat (fst p) (snd p)) (combine lT lT').

Definition qc_ziptotree_id (T: Tree) :=
  eq_tree (ZipperToTree (TreeToZipper T)) T.

QuickChick (forAll (genTree (choose (0, 5)) (choose (0, 5))) qc_cnt_traverse).
QuickChick (forAll (genTree (choose (0, 5)) (choose (0, 5))) qc_ziptotree_id).

