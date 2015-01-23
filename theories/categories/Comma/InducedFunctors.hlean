/- Induced functors between comma categories -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual.
Require Import Category.Prod.
Require Import NaturalTransformation.Identity.
Require Import FunctorCategory.Core Cat.Core.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors.
Require Import Comma.Core Comma.Projection.
Require Import Types.Prod HoTT.Tactics Types.unit.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.
Local Open Scope category_scope.

/- Morphisms in [(A → C)ᵒᵖ × (B → C)] from [(s₀, s₁)] to [(d₀, d₁)] induce functors [(s₀ / s₁) → (d₀ / d₁)] -/
section comma_category_induced_functor
  Context [H : funext].
  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.

  definition comma_category_induced_functor_object_of s d
             (m : morphism ((A → C)⁻¹op × (B → C)) s d)
             (x : pr1 s / pr2 s)
  : (pr1 d / pr2 d) :=
       CommaCategory.Build_object
         (pr1 d) (pr2 d)
         (CommaCategory.a x)
         (CommaCategory.b x)
         ((pr2 m) (CommaCategory.b x) ∘ CommaCategory.f x ∘ (pr1 m) (CommaCategory.a x)).

  definition comma_category_induced_functor_object_of_identity s x
  : comma_category_induced_functor_object_of (Category.Core.identity s) x
    = x.
  /-begin
    let x1 := match goal with |- ?x1 = ?x2 => constr:(x1) end in
    let x2 := match goal with |- ?x1 = ?x2 => constr:(x2) end in
    apply (CommaCategory.path_object' x1 x2 refl idpath).
    simpl.
    abstract (rewrite ?left_identity, ?right_identity; reflexivity).
  end-/

  definition comma_category_induced_functor_object_of_compose s d d'
             (m : morphism ((A → C)⁻¹op × (B → C)) d d')
             (m' : morphism ((A → C)⁻¹op × (B → C)) s d)
             x
  : comma_category_induced_functor_object_of (m ∘ m') x
    = comma_category_induced_functor_object_of
        m
        (comma_category_induced_functor_object_of m' x).
  /-begin
    let x1 := match goal with |- ?x1 = ?x2 => constr:(x1) end in
    let x2 := match goal with |- ?x1 = ?x2 => constr:(x2) end in
    apply (CommaCategory.path_object' x1 x2 refl idpath).
    abstract (
        destruct m', m, x;
        simpl in *;
          rewrite !associativity;
        reflexivity
      ).
  end-/

  definition comma_category_induced_functor_morphism_of s d m s0 d0
             (m0 : morphism (pr1 s / pr2 s) s0 d0)
  : morphism (pr1 d / pr2 d)
             (@comma_category_induced_functor_object_of s d m s0)
             (@comma_category_induced_functor_object_of s d m d0).
  /-begin
    simpl.
    let s := match goal with |- CommaCategory.morphism ?s ?d => constr:(s) end in
    let d := match goal with |- CommaCategory.morphism ?s ?d => constr:(d) end in
    refine (CommaCategory.Build_morphism s d (CommaCategory.g m0) (CommaCategory.h m0) _);
      simpl in *; clear.
    abstract (
        destruct_head prod;
        destruct_head CommaCategory.morphism;
        destruct_head CommaCategory.object;
        simpl in *;
          repeat (try_associativity_quick (rewrite <- !commutes || (progress f_ap)));
        repeat (try_associativity_quick (rewrite !commutes || (progress f_ap)));
        assumption
      ). /- 3.495 s -/
  end-/

  definition comma_category_induced_functor s d
             (m : morphism ((A → C)⁻¹op × (B → C)) s d)
  : Functor (pr1 s / pr2 s) (pr1 d / pr2 d).
  /-begin
    refine (Build_Functor (pr1 s / pr2 s) (pr1 d / pr2 d)
                          (@comma_category_induced_functor_object_of s d m)
                          (@comma_category_induced_functor_morphism_of s d m)
                          _
                          _
           );
    abstract (
        intros; apply CommaCategory.path_morphism; reflexivity
      ).
  end-/
End comma_category_induced_functor.

/- Morphisms in [C] from [a] to [a'] induce functors [(C / a) → (C / a')] -/
section slice_category_induced_functor
  Context [H : funext].
  Variable C : PreCategory.

  section slice_coslice
    Variable D : PreCategory.

    /- TODO(JasonGross): See if this can be recast as an exponential law functor about how [1 → Cat] is isomorphic to [Cat], or something -/
    definition slice_category_induced_functor_nt s d (m : morphism D s d)
    : NaturalTransformation !s !d.
    /-begin
      exists (λ_ : unit, m);
      simpl; intros; clear;
      abstract (autorewrite with category; reflexivity).
    end-/

    Variable F : Functor C D.
    Variable a : D.

    section slice
      definition slice_category_induced_functor F' a'
                 (m : morphism D a a')
                 (T : NaturalTransformation F' F)
      : Functor (F / a) (F' / a') :=
           comma_category_induced_functor
             (s := (F, !a))
             (d := (F', !a'))
             (T, @slice_category_induced_functor_nt a a' m).

      definition slice_category_nt_induced_functor F' T :=
           @slice_category_induced_functor F' a 1 T.
      definition slice_category_morphism_induced_functor a' m :=
           @slice_category_induced_functor F a' m 1.
    End slice.

    section coslice
      definition coslice_category_induced_functor F' a'
                 (m : morphism D a' a)
                 (T : NaturalTransformation F F')
      : Functor (a / F) (a' / F') :=
           comma_category_induced_functor
             (s := (!a, F))
             (d := (!a', F'))
             (@slice_category_induced_functor_nt a' a m, T).

      definition coslice_category_nt_induced_functor F' T :=
           @coslice_category_induced_functor F' a 1 T.
      definition coslice_category_morphism_induced_functor a' m :=
           @coslice_category_induced_functor F a' m 1.
    End coslice.
  End slice_coslice.

  definition slice_category_over_induced_functor a a' (m : morphism C a a')
  : Functor (C / a) (C / a') :=
       Eval hnf in slice_category_morphism_induced_functor _ _ _ m.
  definition coslice_category_over_induced_functor a a' (m : morphism C a' a)
  : Functor (a \ C) (a' \ C) :=
       Eval hnf in coslice_category_morphism_induced_functor _ _ _ m.
End slice_category_induced_functor.

/- Functors [A → A'] functors [(cat / A) → (cat / A')] -/
section cat_over_induced_functor
  Context [H : funext].
  Variable P : PreCategory → Type.
  Context {H0 : ΠC D, P C → P D → IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P H0).

  definition cat_over_induced_functor a a' (m : morphism cat a a')
  : Functor (cat / a) (cat / a') :=
       slice_category_over_induced_functor cat a a' m.

  definition over_cat_induced_functor a a' (m : morphism cat a' a)
  : Functor (a \ cat) (a' \ cat) :=
       coslice_category_over_induced_functor cat a a' m.
End cat_over_induced_functor.
