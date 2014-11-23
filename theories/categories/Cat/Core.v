/- Cat, the precategory of strict categories -/
Require Import Category.Core Category.Objects InitialTerminalCategory.Core InitialTerminalCategory.Functors Functor.Core Category.Strict Category.Univalent Functor.Paths.
Require Import Functor.Identity Functor.Composition.Core Functor.Composition.Laws.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

section sub_pre_cat
  Context [H : Funext].

  /- We use a slight generalization; we look at a full 1-precategory
      of the 2-precategory Cat, such that all types of functors are
      hSets.  It might be possible to prove that this doesn't buy you
      anything, because it's probably the case that [IsHSet (Functor C
      C) → IsStrictCategory C]. -/

  Variable P : PreCategory → Type.
  Context {HF : ΠC D, P C → P D → IsHSet (Functor C D)}.

  /- There is a precategory of precategories which satisfy the proposition P -/

  definition sub_pre_cat : PreCategory :=
       @Build_PreCategory
         { C : PreCategory | P C }
         (λC D, Functor C.1 D.1)
         (λC, identity C.1)
         (λ_ _ _ F G, F ∘ G)
         (λ_ _ _ _ _ _ _, associativity _ _ _)
         (λ_ _ _, left_identity _)
         (λ_ _ _, right_identity _)
         (λs d, HF s.2 d.2).
End sub_pre_cat.

Arguments sub_pre_cat {_} P {_}, {_} P _.

definition strict_cat [H : Funext] : PreCategory :=
     sub_pre_cat (λC, IsStrictCategory C).

(*definition Cat [H : Funext] : PreCategory.
  refine (@sub_pre_cat _ (λC, IsCategory C) _).
  *)

/- The initial and terminal categories are initial and terminal objects in cat -/
section objects
  Context [H : Funext].

  Variable P : PreCategory → Type.
  Context [H : ΠC, is_hprop (P C)].
  Context {HF : ΠC D, P C → P D → IsHSet (Functor C D)}.

  definition is_terminal_object__is_terminal_category
        `(IsTerminalCategory one)
        (HT : P one)
  : IsTerminalObject (sub_pre_cat P HF) ⟨one, HT⟩.
  /-begin
    typeclasses eauto.
  end-/

  definition is_initial_object__is_initial_category
        `(IsInitialCategory zero)
        (HI : P zero)
  : IsInitialObject (sub_pre_cat P HF) ⟨zero, HI⟩.
  /-begin
    typeclasses eauto.
  end-/
End objects.
