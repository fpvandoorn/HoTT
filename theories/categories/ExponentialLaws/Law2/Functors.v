/- Exponential functors between products and sums in exponents -/
Require Import Category.Core Functor.Core FunctorCategory.Core Functor.Identity NaturalTransformation.Core NaturalTransformation.Paths Functor.Composition.Core Category.Sum Category.Prod Functor.Sum Functor.Prod.Core NaturalTransformation.Sum Functor.Pointwise.Core NaturalTransformation.Paths.
Require Import InitialTerminalCategory.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

Local Notation fst_type := Coq.Init.Datatypes.pr1.
Local Notation snd_type := Coq.Init.Datatypes.snd.
Local Notation pair_type := Coq.Init.Datatypes.pair.

section law2
  Context [H : Funext].
  Variable D : PreCategory.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.

  /- [yⁿ⁺ᵐ → yⁿ × yᵐ] -/
  definition functor
  : Functor (C1 + C2 → D) ((C1 → D) × (C2 → D)) :=
       pointwise (inl C1 C2) 1
       × pointwise (inr C1 C2) 1.

  /- [yⁿ × yᵐ → yⁿ⁺ᵐ] -/
  definition inverse
  : Functor ((C1 → D) × (C2 → D)) (C1 + C2 → D).
  /-begin
    refine (Build_Functor
              ((C1 → D) × (C2 → D)) (C1 + C2 → D)
              (λFG, pr1 FG + pr2 FG)%functor
              (λ_ _ m, fst_type m + snd_type m)%natural_transformation
              _
              _);
    simpl in *;
    abstract (
        repeat (intros [?|?] || intros [? ?]);
        simpl in *;
          apply path_natural_transformation; intros [?|?];
        reflexivity
      ).
  end-/
End law2.
