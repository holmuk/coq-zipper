Require Extraction.
Require Import TreeZipper.
Require Import ZArith.
Require Import Coq.Structures.Equalities.

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellZInt.

Local Open Scope Z_scope.

Module HaskellExtraction.

Module ZType <: Typ with Definition t := Z.
Definition t := Z.
End ZType.

Module ZTree := (TreeZipperDef ZType).
Import ZTree.

Extraction Language Haskell.

Extract Inductive Tree => "tree" [ "t_nil" "t_tree" ].
Extract Inductive Context => "cntx" [ "move" ].

Extraction Inline fst snd.

End HaskellExtraction.

Extraction "Tree.hs" HaskellExtraction.