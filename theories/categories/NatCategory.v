/- Discrete categories on [n] objects -/
Require Import Category.Core DiscreteCategory IndiscreteCategory.
Require Import Types.unit Trunc Types.Sum Types.Empty.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Module Export Core.
  /- [Fin n] types, or [CardinalityRepresentative] -/
  /- We use [Empty] for [0] and [unit] for [1] so that we get nice judgmental behavior with opposites -/
  Fixpoint CardinalityRepresentative (n : nat) : Type1 :=
    match n with
      | 0 => Empty
      | 1 => unit
      | S n' => (CardinalityRepresentative n' + unit)%type
    end.

  Coercion CardinalityRepresentative : nat >-> Type1.

  /- [Fin n] is an hSet -/
  definition trunc_cardinality_representative [instance] (n : nat)
  : IsHSet (CardinalityRepresentative n).
  Proof.
    induction n; [ typeclasses eauto |].
    induction n; [ typeclasses eauto |].
    intros [x|x] [y|y];
      typeclasses eauto.
  Qed.

  /- Define the categories [n] -/
  definition nat_category (n : nat) :=
    match n with
      | 0 => indiscrete_category 0
      | 1 => indiscrete_category 1
      | S (S n') => discrete_category (S (S n'))
    end.

  Coercion nat_category : nat >-> PreCategory.

  Module Export NatCategoryCoreNotations.
    Notation "1" := (nat_category 1) : category_scope.
  End NatCategoryCoreNotations.

  Typeclasses Transparent nat_category.
  Hint Unfold nat_category.
  Arguments nat_category / .
End Core.

Module Notations.
  Include Core.NatCategoryCoreNotations.
End Notations.
