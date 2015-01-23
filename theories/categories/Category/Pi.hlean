/- Dependent Product Category -/
Require Import Category.Core Category.Strict.
Require Import Types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

/- definition of [∀], or [∏], for categories -/
section pi
  Context [H : funext].
  Variable A : Type.
  Variable P : A → PreCategory.

  definition pi : PreCategory.
    refine (@Build_PreCategory
              (Πa : A, P a)
              (λs d, Πa : A, morphism (P a) (s a) (d a))
              (λx, λa, identity (x a))
              (λs d d' m2 m1, λa, m2 a ∘ m1 a)
              _
              _
              _
              _);
    abstract (
        repeat (intro || apply path_forall);
        auto with morphism
      ).
  Defined.
End pi.

Local Notation "'forall'  x .. y , P" := (Πx, .. (Πy, P) ..)
  (at level 200, x binder, y binder, right associativity).
Local Notation "'forall'  x .. y , P" := (Πx, .. (Πy, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
Local Notation "'forall'  x .. y , P" := (pi (λx, .. (pi (λy, P)) .. ))
  (at level 200, x binder, y binder, right associativity) : category_scope.

/- The product of strict categories is strict -/
Global Instance isstrict_category_pi
       [H : funext]
       {Πa : A, IsStrictCategory (P a)}
: IsStrictCategory (Πa, P a).
Proof.
  typeclasses eauto.
Qed.

Module Export CategoryPiNotations.
  Notation "'forall'  x .. y , P" := (Πx, .. (Πy, P) ..)
                                       (at level 200, x binder, y binder, right associativity).
  Notation "'forall'  x .. y , P" := (Πx, .. (Πy, P) ..)
                                       (at level 200, x binder, y binder, right associativity) : type_scope.
  Notation "'forall'  x .. y , P" := (pi (λx, .. (pi (λy, P)) .. ))
                                       (at level 200, x binder, y binder, right associativity) : category_scope.
End CategoryPiNotations.
