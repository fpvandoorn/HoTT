/- Product Category -/
Require Import Category.Core Category.Strict.
Require Import Types.Prod.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

/- definition of [*] for categories -/
section prod
  Variable C : PreCategory.
  Variable D : PreCategory.

  definition prod : PreCategory.
    refine (@Build_PreCategory
              (C × D)%type
              (λs d, (morphism C (pr1 s) (pr1 d)
                           × morphism D (pr2 s) (pr2 d))%type)
              (λx, (identity (pr1 x), identity (pr2 x)))
              (λs d d' m2 m1, (pr1 m2 ∘ pr1 m1, pr2 m2 ∘ pr2 m1))
              _
              _
              _
              _);
    abstract (
        repeat (simpl || intros [] || intro);
        try f_ap; auto with morphism
      ).
  Defined.
End prod.

Local Infix "*" := prod : category_scope.

/- The product of strict categories is strict -/
Global Instance isstrict_category_product
       [H : IsStrictCategory C, IsStrictCategory D]
: IsStrictCategory (C × D).
Proof.
  typeclasses eauto.
Qed.

Module Export CategoryProdNotations.
  Infix "*" := prod : category_scope.
End CategoryProdNotations.
