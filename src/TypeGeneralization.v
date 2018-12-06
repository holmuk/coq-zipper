(**
 What makes real sense is to try to generalize the Zipper over inductive types.
 Firstly we need to specify what a type is and clarify our intuitive definitions.
 This section is to provide such a "specification".
 See [McBride2001].
*)

Require Import Nat List Bool Arith Logic Decidable.
Import ListNotations.

Module GeneralizedType.

Parameter NameType: Type.
Parameter Name_decidability: forall x (y: NameType),
  decidable (x=y).
Parameter Name_dec: forall x (y: NameType), {x = y} + {x <> y}.

Notation Name := NameType.
Notation "x ?= y" := (Name_dec x y).

Definition NameList := list Name.

Fixpoint Restriction (Sigma: NameList) (x: Name) : NameList :=
  match Sigma with
  | [] => []
  | h::t => if Name_dec x h then t else Restriction t x
  end.

Notation NameSequence := NoDup.

Ltac ndestruct :=
  let E := fresh in
  match goal with
  | H: context[?x ?= ?y] |- _ =>
    destruct (x ?= y)
  | |- context[?x ?= ?y] =>
    destruct (x ?= y)
  end; subst.

Lemma NS_Restriction: forall N x,
  NameSequence N ->
  NameSequence (Restriction N x).
Proof.
  intros.
  induction N; auto.
  inversion H; subst; simpl.
  ndestruct; auto.
Qed.

Lemma Restriction_repr: forall Sigma x L,
  L <> [] ->
  Restriction Sigma x = L ->
  exists L', Sigma = L' ++ (x::L).
Proof.
  induction Sigma; intros; simpl in H0.
  - contradict H; auto.
  - ndestruct; simpl.
    exists []. auto.
    remember (Restriction Sigma x) eqn:E; symmetry in E.
    apply IHSigma in E; auto. destruct E.
    exists (a::x0). rewrite H0. auto.
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

Definition TypeEnvironment := list (prod Name RegularType).
Definition AttachedNames (G: TypeEnvironment) :=
  map (fun x => (fst x)) G.

Fixpoint TypeRestriction (Gamma: TypeEnvironment) (x: Name) : TypeEnvironment :=
  match Gamma with
  | [] => []
  | h::t => if Name_dec x (fst h) then t else TypeRestriction t x
  end.

Fixpoint TypeProjection (Gamma: TypeEnvironment) (x: Name) : RegularType :=
  match Gamma with
  | [] => Zero
  | h::t => if Name_dec x (fst h) then (snd h) else TypeProjection t x
  end.

Lemma Restriction_TypeRestriction: forall G x,
  AttachedNames (TypeRestriction G x) =
  Restriction (AttachedNames G) x.
Proof.
  induction G; intros; auto.
  simpl. ndestruct; auto.
Qed.

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
    OfRegularType (x::N) (Underscore x T)
  | RT_TypeEnvironment: forall G x,
    let Sigma := AttachedNames G in
    NameSequence Sigma ->
    In x Sigma ->
    OfTypeEnvironment G ->
    OfRegularType (Restriction Sigma x) (TypeProjection G x)
    
    with

  OfTypeEnvironment : TypeEnvironment -> Prop :=
  | TE_nil:
    OfTypeEnvironment []
  | TE_cons: forall x G S,
    let Sigma := AttachedNames G in
    NameSequence (x::Sigma) ->
    OfTypeEnvironment G ->
    OfRegularType Sigma S ->
    OfTypeEnvironment ((x, S)::G)
  | TE_proj: forall x G,
    let Sigma := AttachedNames G in
    NameSequence Sigma ->
    In x Sigma ->
    OfTypeEnvironment G ->
    OfTypeEnvironment (TypeRestriction G x).

Hint Constructors NameSequence OfRegularType OfTypeEnvironment.

Lemma NS_AttachedNames: forall G,
  OfTypeEnvironment G ->
  NameSequence (AttachedNames G).
Proof.
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
    OfTypeEnvironment G ->
    DataIsOfType G One D_nil
  | DT_con: forall G F x t,
    OfTypeEnvironment G ->
    DataIsOfType G (Subs x (Fun x F) F) t ->
    DataIsOfType G (Fun x F) (D_con t)
  | DT_inl: forall G R L d,
    let Sigma := AttachedNames G in
    OfTypeEnvironment G ->
    OfRegularType Sigma L -> OfRegularType Sigma R ->
    DataIsOfType G L d ->
    DataIsOfType G (Sum L R) (D_inl d)
  | DT_inr: forall G R L d,
    let Sigma := AttachedNames G in
    OfTypeEnvironment G ->
    OfRegularType Sigma L -> OfRegularType Sigma R ->
    DataIsOfType G R d ->
    DataIsOfType G (Sum L R) (D_inr d)
  | DT_prod: forall G R L r l,
    let Sigma := AttachedNames G in
    OfTypeEnvironment G ->
    OfRegularType Sigma L -> OfRegularType Sigma R ->
    DataIsOfType G R r -> DataIsOfType G L l ->
    DataIsOfType G (Prod L R) (D_pair l r)
  | DT_subst: forall G F x S d,
    let Sigma := AttachedNames G in
    OfTypeEnvironment G ->
    OfRegularType Sigma F ->
    DataIsOfType ((x, S)::G) F d ->
    DataIsOfType G (Subs x S F) d
  | DT_restr_proj: forall G x t,
    OfTypeEnvironment G ->
    DataIsOfType (TypeRestriction G x) (TypeProjection G x) t ->
    DataIsOfType G (FreeVar x) t
  | DT_underscore: forall G T S x d,
    let Sigma := AttachedNames G in
    OfTypeEnvironment G ->
    OfRegularType Sigma T ->
    DataIsOfType G T d ->
    DataIsOfType ((x, S)::G) (Underscore x T) d.

Hint Constructors OfRegularType OfTypeEnvironment DataIsOfType.
Hint Resolve NS_AttachedNames.

Section Examples1.

Variable x: NameType.

Definition myNat : RegularType :=
  (Fun x (Sum One (FreeVar x) )).

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
  OfTypeEnvironment G ->
  DataIsOfType G myBool myTrue.
Proof.
  autounfold with ex1. intros.
  repeat constructor; auto.
Qed.

Lemma myZero_is_myNat : forall G,
  ~ In x (AttachedNames G) ->
  OfTypeEnvironment G ->
  DataIsOfType G myNat myZero.
Proof.
  autounfold with ex1. intros.
  repeat constructor; auto.
Qed.

Lemma myZero_is_not_myBool: forall G,
  ~ DataIsOfType G myBool myZero.
Proof.
  unfold not. intros.
  inversion H.
Qed.

End Examples1.

Section ListExample.

Variable x: NameType.
Variable y: NameType.

Definition myList (T: RegularType) : RegularType :=
  (Fun x (Sum One (Prod T (FreeVar x)))).

Definition myNil : Data :=
  (D_con (D_inl D_nil)).

Definition myCons (xf xs: Data) : Data :=
  (D_con (D_inr (D_pair xf xs))).

Hint Unfold myList myNil myCons : ex2.

Ltac unfold_local :=
  repeat match goal with
  | x := _ : ?A |- _ => progress unfold x in *; clear x
  end; simpl in *.

Lemma myNat_is_myList: forall y,
  x <> y ->
  DataIsOfType [] (myList (myNat y)) (myNil).
Proof.
  intros.
  repeat constructor; simpl; intuition.
Qed.

Lemma cons_myZero_myNil_is_myList: forall y,
  x <> y ->
  DataIsOfType [] (myList (myNat y)) (myCons (myZero) myNil).
Proof.
  intros.
  repeat constructor; simpl; intuition.
  ndestruct; repeat constructor; simpl; intuition.
Qed.

Definition myTwo : Data := mySuc (mySuc myZero).

Fixpoint construct_myNat (n: nat) : Data :=
  match n with
  | 0 => myZero
  | S n' => mySuc (construct_myNat n')
  end.

Lemma cons_myTwo_myNil_is_myList: forall y,
  x <> y ->
  DataIsOfType [] (myList (myNat y)) (myCons (myTwo) myNil).
Proof.
  intros.
  repeat constructor; simpl; intuition.
  ndestruct; repeat constructor; simpl; intuition.
  ndestruct; repeat constructor; simpl; intuition.
  ndestruct; repeat constructor; simpl; intuition.
Qed.

Lemma myTwo_is_myNat:
  DataIsOfType [] (myNat y) myTwo.
Proof.
  intros.
  repeat constructor; auto.
  unfold mySuc, myZero, TypeProjection.
  ndestruct; repeat constructor; unfold_local; auto.
  all: ndestruct; simpl; auto.
  all: repeat constructor; auto; try contradiction.
Qed.

Lemma const_is_myNat: forall n,
  DataIsOfType [] (myNat y) (construct_myNat n).
Proof.
  induction n; intros.
  - apply myZero_is_myNat; intuition.
  - simpl.
    unfold mySuc. repeat constructor; auto.
    simpl. ndestruct; auto.
    contradiction.
Qed.

Ltac dataDerive :=
  (match goal with
  |H: DataIsOfType _ _ _ |- _ => inversion H as []; subst; unfold_local
  end).

Lemma mfm: forall n,
  DataIsOfType [] (myNat y) n ->
  DataIsOfType [] (myNat y) (mySuc n).
Proof.
  intros.
  repeat constructor; intuition.
  do 4 dataDerive; try ndestruct; intuition.
Qed.

Ltac absurd_inversion :=
  match goal with
  | H: ?x = ?y |- _ => match type of x with
    | RegularType => match type of y with | t => inversion H | _ => idtac end
    | _ => idtac
    end
  end.

Lemma myList_cons_one: forall xs,
  x <> y ->
  DataIsOfType [] (myNat y) xs ->
  DataIsOfType [] (myList (myNat y)) (myCons xs myNil).
Proof.
  Admitted.

End ListExample.

End GeneralizedType.


