/- Functors involving product categories -/
Require Import Category.Core Functor.Core Category.Prod Functor.Composition.Core.
Require Import Functor.Paths.
Require Import Types.Prod.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation fst_type := fst.
Local Notation snd_type := snd.
Local Notation pair_type := pair.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.

/- First and second projections from a product precategory -/
section proj
  Context {C : PreCategory}.
  Context {D : PreCategory}.

  definition fst : Functor (C × D) C :=
       Build_Functor (C × D) C
                     (@fst _ _)
                     (λ_ _, @fst _ _)
                     (λ_ _ _ _ _, idpath)
                     (λ_, idpath).

  definition snd : Functor (C × D) D :=
       Build_Functor (C × D) D
                     (@snd _ _)
                     (λ_ _, @snd _ _)
                     (λ_ _ _ _ _, idpath)
                     (λ_, idpath).
End proj.

/- Product of two functors from the same domain -/
section prod
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable D' : PreCategory.

  definition prod (F : Functor C D) (F' : Functor C D')
  : Functor C (D × D') :=
       Build_Functor
         C (D × D')
         (λc, (F c, F' c))
         (λs d m, (F _1 m, F' _1 m))
         (λ_ _ _ _ _, path_prod' (composition_of F _ _ _ _ _)
                                      (composition_of F' _ _ _ _ _))
         (λ_, path_prod' (identity_of F _) (identity_of F' _)).
End prod.

Local Infix "*" := prod : functor_scope.

/- Pairing of two functors -/
section pair
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable C' : PreCategory.
  Variable D' : PreCategory.
  Variable F : Functor C D.
  Variable F' : Functor C' D'.

  Local Open Scope functor_scope.

  definition pair : Functor (C × C') (D × D') :=
       (F ∘ fst) × (F' ∘ snd).
End pair.

Local Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : functor_scope.

/- Partially applied functors out of a product precategory -/
section induced
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Variable F : Functor (C × D) E.

  Local Open Scope core_scope.

  Local Ltac t :=
    simpl; intros;
    repeat (rewrite <- ?composition_of, <- ?identity_of, ?left_identity, ?right_identity; simpl);
    trivial.

  /- Note: This is just the currying exponential law. -/
  /- TODO: Come up with a better name for this? -/
  definition induced_fst (d : D) : Functor C E.
  /-begin
    refine (Build_Functor
              C E
              (λc, F (c, d))
              (λ_ _ m, @morphism_of _ _ F (_, _) (_, _) (m, identity d))
              _
              _);
    abstract t.
  end-/

  definition induced_snd (c : C) : Functor D E.
  /-begin
    refine (Build_Functor
              D E
              (λd, F (c, d))
              (λ_ _ m, @morphism_of _ _ F (_, _) (_, _) (identity c, m))
              _
              _);
    abstract t.
  end-/
End induced.

Module Export FunctorProdCoreNotations.
  Infix "*" := prod : functor_scope.
  Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : functor_scope.
End FunctorProdCoreNotations.
