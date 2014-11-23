/- Functoriality of functor category construction -/
Require Import Category.Core Functor.Core FunctorCategory.Core Functor.Pointwise.Core Functor.Pointwise.Properties Category.Dual Category.Prod Cat.Core ExponentialLaws.Law4.Functors.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

/- [(_ → _)] is a functor [catᵒᵖ × cat → cat] -/
section functor
  Context [H : Funext].

  Variable P : PreCategory → Type.
  Context [H : ΠC, is_hprop (P C)].
  Context {HF : ΠC D, P C → P D → IsHSet (Functor C D)}.

  Local Notation cat := (sub_pre_cat P HF).

  Hypothesis has_functor_categories : ΠC D : cat, P (C.1 → D.1).

  definition functor_uncurried
  : object ((cat⁻¹op × cat) → cat) :=
       Eval cbv zeta in
        let object_of := (λCD, (((pr1 CD).1 → (pr2 CD).1);
                                     has_functor_categories (pr1 CD) (pr2 CD)))
        in Build_Functor
             (cat⁻¹op × cat) cat
             object_of
             (λCD C'D' FG, pointwise (pr1 FG) (pr2 FG))
             (λ_ _ _ _ _, Functor.Pointwise.Properties.composition_of _ _ _ _)
             (λ_, Functor.Pointwise.Properties.identity_of _ _).

  definition functor : object (cat⁻¹op → (cat → cat)) :=
       ExponentialLaws.Law4.Functors.inverse _ _ _ functor_uncurried.
End functor.
