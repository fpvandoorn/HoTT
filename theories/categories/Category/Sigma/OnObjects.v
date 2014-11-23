/- ∑-categories on objects - a generalization of subcategories -/
Require Import Types.unit.
Require Import Category.Core Functor.Core Category.Sigma.Core.
Require Functor.Composition.Core Functor.Identity.
Require Import Functor.Paths.
Import Functor.Identity.FunctorIdentityNotations.
Import Functor.Composition.Core.FunctorCompositionCoreNotations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation sigT_type := Coq.Init.Specif.sigT.
Local Notation pr1_type := Overture.dpr1.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.

section sigT_obj
  Variable A : PreCategory.
  Variable Pobj : A → Type.

  /- definition of [sigT_obj]-precategory -/
  definition sigT_obj : PreCategory :=
       @Build_PreCategory
         (sigT_type Pobj)
         (λs d, morphism A (pr1_type s) (pr1_type d))
         (λx, @identity A (pr1_type x))
         (λs d d' m1 m2, m1 ∘ m2)%morphism
         (λ_ _ _ _, associativity A _ _ _ _)
         (λ_ _, left_identity A _ _)
         (λ_ _, right_identity A _ _)
         _.

  /- First projection functor -/
  definition pr1_obj : Functor sigT_obj A :=
       Build_Functor
         sigT_obj A
         (@pr1_type _ _)
         (λs d m, m)
         (λ_ _ _ _ _, idpath)
         (λ_, idpath).

  definition sigT_obj_as_sigT : PreCategory :=
       @sig A Pobj (λ_ _ _, unit) _ (λ_, star) (λ_ _ _ _ _ _ _, star).

  definition sigT_functor_obj : Functor sigT_obj_as_sigT sigT_obj :=
       Build_Functor sigT_obj_as_sigT sigT_obj
                     (λx, x)
                     (λ_ _, @pr1_type _ _)
                     (λ_ _ _ _ _, idpath)
                     (λ_, idpath).

  definition sigT_functor_obj_inv : Functor sigT_obj sigT_obj_as_sigT :=
       Build_Functor sigT_obj sigT_obj_as_sigT
                     (λx, x)
                     (λ_ _ m, existT _ m star)
                     (λ_ _ _ _ _, idpath)
                     (λ_, idpath).

  Local Open Scope functor_scope.

  Lemma sigT_obj_eq [H : Funext]
  : sigT_functor_obj ∘ sigT_functor_obj_inv ≈ 1
    /\ sigT_functor_obj_inv ∘ sigT_functor_obj ≈ 1.
  Proof.
    split; path_functor; trivial.
    repeat (intros [] || intro || apply path_forall).
    reflexivity.
  Qed.

  definition sigT_obj_compat : pr1_obj ∘ sigT_functor_obj ≈ dpr1 :=
       idpath.
End sigT_obj.

Arguments pr1_obj {A Pobj}.
