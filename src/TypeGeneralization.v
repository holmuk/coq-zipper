(**
 What makes real sense is to try to generalize the Zipper over inductive types.
 Firstly we need to specify what a type is and clarify our intuitive definitions.
 This section is to provide such a "specification".
 See [McBride2001].
*)

Require Import Nat List Bool Arith.
Import ListNotations.

Notation Name := nat.
Definition NameList := list Name.

Fixpoint Restriction (Sigma: NameList) (x: Name) : NameList :=
  match Sigma with
  | [] => []
  | h::t => match compare h x with
    | Eq => t
    | _ => Restriction t x
    end
  end.

Inductive NameSequence : NameList -> Prop :=
  | NS_nil: NameSequence []
  | NS_app: forall S x,
    NameSequence S -> ~ (In x S) -> NameSequence (x::S).

Inductive RegularType : Type :=
  | Zero: RegularType
  | One: RegularType
  | FreeVar: Name -> RegularType
  | Sum: RegularType -> RegularType -> RegularType
  | Prod: RegularType -> RegularType -> RegularType
  | Fun: Name -> RegularType -> RegularType
  | Subs: Name -> RegularType -> RegularType -> RegularType.

Definition TypeEnvironment := list (prod Name RegularType).

Fixpoint TypeRestriction (Gamma: TypeEnvironment) (x: Name) : TypeEnvironment :=
  match Gamma with
  | [] => []
  | h::t => match compare (fst h) x with
    | Eq => t
    | _ => TypeRestriction t x
    end
  end.

Fixpoint TypeProjection (Gamma: TypeEnvironment) (x: Name) : RegularType :=
  match Gamma with
  | [] => Zero
  | h::t => match compare (fst h) x with
    | Eq => snd h
    | _ => TypeProjection t x
    end
  end.

Inductive Data : Type :=
  | D_nil: Data
  | D_pair: Data -> Data -> Data
  | D_inl: Data -> Data
  | D_inr: Data -> Data
  | D_con: Data -> Data.

(* Need to check *)
Inductive DataIsOfType: TypeEnvironment -> RegularType -> Data -> Prop :=
  | DT_nil: forall G,
    DataIsOfType G One D_nil
  | DT_con: forall G F x t,
    DataIsOfType G (Subs x (Fun x F) F) t ->
    DataIsOfType G (Fun x F) (D_con t)
  | DT_inl: forall G R L d,
    DataIsOfType G L d ->
    DataIsOfType G (Sum L R) (D_inl d)
  | DT_inr: forall G R L d,
    DataIsOfType G R d ->
    DataIsOfType G (Sum L R) (D_inr d)
  | DT_prod: forall G R L r l,
    DataIsOfType G R r -> DataIsOfType G L l ->
    DataIsOfType G (Prod L R) (D_pair l r)
  | DT_subst: forall G F x S d,
    DataIsOfType ((x, S)::G) F d ->
    DataIsOfType G (Subs x S F) d
  | DT_restr_proj: forall G x t,
    DataIsOfType (TypeRestriction G x) (TypeProjection G x) t ->
    DataIsOfType G (FreeVar x) t.

Section Examples1.

Definition myNat : RegularType :=
  (Fun 1 (Sum One (FreeVar 1) )).

Definition myZero : Data :=
  D_con (D_inl D_nil).

Definition mySuc (d: Data) : Data :=
  D_con (D_inr d).

Definition myBool : RegularType :=
  (Sum One One).

Definition myTrue : Data :=
  (D_inl D_nil).

Definition myFalse : Data :=
  (D_inr D_nil).

Hint Constructors DataIsOfType.

Lemma myTrue_is_myBool : forall G,
  DataIsOfType G myBool myTrue.
Proof.
  unfold myTrue, myBool.
  auto.
Qed.

Lemma myZero_is_myNat : forall G,
  DataIsOfType G myNat myZero.
Proof.
  unfold myNat, myZero. intros.
  auto.
Qed.

Lemma myZero_is_not_myBool: forall G,
  ~ DataIsOfType G myBool myZero.
Proof.
  unfold not, myBool, myZero. intros.
  inversion H.
Qed.

End Examples1.
