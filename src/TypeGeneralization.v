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

Lemma NS_Restriction: forall N x,
  NameSequence N ->
  NameSequence (Restriction N x).
Proof.
  intros.
  induction N; auto.
  inversion H; subst. simpl.
  destruct (a ?= x); simpl; auto.
Qed.

Inductive RegularType : Type :=
  | Zero: RegularType
  | One: RegularType
  | FreeVar: Name -> RegularType
  | Sum: RegularType -> RegularType -> RegularType
  | Prod: RegularType -> RegularType -> RegularType
  | Fun: Name -> RegularType -> RegularType
  | Subs: Name -> RegularType -> RegularType -> RegularType
  | Underscore: Name -> RegularType -> RegularType.

Inductive OfRegularType : NameList -> RegularType -> Prop :=
  | RT_Name: forall N x,
    NameSequence N ->
    OfRegularType N (FreeVar x)
  | RT_Zero: forall N,
    NameSequence N ->
    OfRegularType N (Zero)
  | RT_One: forall N,
    NameSequence N ->
    OfRegularType N (One)
  | RT_Sum: forall N S T,
    NameSequence N ->
    OfRegularType N S -> OfRegularType N T ->
    OfRegularType N (Sum S T)
  | RT_Prod: forall N S T,
    NameSequence N ->
    OfRegularType N S -> OfRegularType N T ->
    OfRegularType N (Prod S T)
  | RT_Fun: forall N x F,
    NameSequence N ->
    OfRegularType (x::N) F ->
    OfRegularType N (Fun x F)
  | RT_Subs: forall N F S x,
    NameSequence N ->
    OfRegularType (x::N) F ->
    OfRegularType N S ->
    OfRegularType N (Subs x S F)
  | RT_Underscore: forall N T x,
    NameSequence N ->
    OfRegularType N T ->
    OfRegularType (x::N) (Underscore x T).

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

Inductive OfTypeEnvironment : NameList -> TypeEnvironment -> Prop :=
  | TE_nil:
    OfTypeEnvironment [] []
  | TE_cons: forall x G Sigma S,
    NameSequence (x::Sigma) ->
    OfTypeEnvironment Sigma G ->
    OfRegularType Sigma S ->
    OfTypeEnvironment (x::Sigma) ((x, S)::G)
  | TE_proj: forall x Sigma G,
    In x Sigma ->
    OfTypeEnvironment Sigma G ->
    OfTypeEnvironment (Restriction Sigma x) (TypeRestriction G x).

Hint Constructors NameSequence.

Lemma NS_OfTypeEnvironment: forall G N,
  OfTypeEnvironment N G ->
  NameSequence N.
Proof.
  induction G; intros; auto.
  inversion H. auto. 
  inversion H; subst; auto.
Admitted.

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
  | DT_inl: forall Sigma G R L d,
    OfRegularType Sigma L -> OfRegularType Sigma R ->
    DataIsOfType G L d ->
    DataIsOfType G (Sum L R) (D_inl d)
  | DT_inr: forall Sigma G R L d,
    OfRegularType Sigma L -> OfRegularType Sigma R ->
    DataIsOfType G R d ->
    DataIsOfType G (Sum L R) (D_inr d)
  | DT_prod: forall Sigma G R L r l,
    OfRegularType Sigma L -> OfRegularType Sigma R ->
    DataIsOfType G R r -> DataIsOfType G L l ->
    DataIsOfType G (Prod L R) (D_pair l r)
  | DT_subst: forall Sigma G F x S d,
    OfRegularType Sigma F ->
    DataIsOfType ((x, S)::G) F d ->
    DataIsOfType G (Subs x S F) d
  | DT_restr_proj: forall G x t,
    DataIsOfType (TypeRestriction G x) (TypeProjection G x) t ->
    DataIsOfType G (FreeVar x) t
  | DT_underscore: forall Sigma G T S x d,
    OfRegularType Sigma T ->
    DataIsOfType G T d ->
    DataIsOfType ((x, S)::G) (Underscore x T) d.

Hint Constructors OfRegularType OfTypeEnvironment DataIsOfType.

Lemma DT_Tproj: forall Sigma G x,
    In x Sigma ->
    OfTypeEnvironment Sigma G ->
    OfRegularType (Restriction Sigma x) (TypeProjection G x).
Proof.
  intros. destruct Sigma, G; simpl.
  - inversion H.
  - inversion H.
  - 


Hint Constructors DataIsOfType.

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

Hint Unfold myTrue myFalse myBool myNat myZero : ex1.

Lemma myTrue_is_myBool : forall G,
  DataIsOfType G myBool myTrue.
Proof.
  autounfold with ex1. auto.
Qed.

Lemma myZero_is_myNat : forall G,
  DataIsOfType G myNat myZero.
Proof.
  autounfold with ex1. auto.
Qed.

Lemma myZero_is_not_myBool: forall G,
  ~ DataIsOfType G myBool myZero.
Proof.
  unfold not. intros.
  inversion H.
Qed.

End Examples1.

Section ListExample.

Definition myList (T: RegularType) : RegularType :=
  (Fun 1 (Sum One (Prod (Underscore 1 T) (FreeVar 1)))).

Definition myNil (T: RegularType) : Data :=
  (D_con (D_inl D_nil)).

Definition myCons (T: RegularType) (x xs: Data) : Data :=
  (D_con (D_inr (D_pair x xs))).

Hint Unfold myList myNil myCons : ex2.

Lemma myList_cons_one: forall G x,
  DataIsOfType G myNat x ->
  DataIsOfType G (myList myNat) (myCons myNat (myNil myNat) x).
Proof.
  autounfold with ex2. intros.
  repeat constructor.
  destruct x; simpl; try inversion H.
  subst.

End ListExample.


