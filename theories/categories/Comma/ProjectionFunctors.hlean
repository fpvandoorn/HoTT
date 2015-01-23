/- Functoriality of the comma category construction with projection functors -/
Require Import Category.Core Functor.Core.
Require Import Category.Prod Functor.Prod.Core.
Require Import Category.Dual Functor.Dual.
Require Import Functor.Composition.Core Functor.Identity.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors NatCategory.
Require Import FunctorCategory.Core.
Require Import Cat.Core.
Require Import Functor.Paths.
Require Import Comma.Core Comma.InducedFunctors Comma.Projection.
Require ProductLaws ExponentialLaws.Law1.Functors ExponentialLaws.Law4.Functors.
Require Import Types.Prod Types.ΠPathGroupoids HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

/- Functor from [(A → C)ᵒᵖ × (B → C)] to [cat / (A × B)] -/
/- It sends [S : A → C ← B : T] to the category [(S / T)] and its projection functor to [A × B]. -/
section comma
  Context [H : funext].

  Variable P : PreCategory → Type.
  Context {HF : ΠC D, P C → P D → IsHSet (Functor C D)}.

  Local Notation Cat := (@sub_pre_cat _ P HF).

  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.

  Hypothesis PAB : P (A × B).
  Hypothesis P_comma : Π(S : Functor A C) (T : Functor B C),
                         P (S / T).

  Local Open Scope morphism_scope.

  definition comma_category_projection_functor_object_of
             (ST : object ((A → C)⁻¹op × (B → C)))
  : Cat / !(⟨A × B, PAB⟩ : Cat).
  /-begin
    exists (Datatypes.pr1 ST / Datatypes.snd ST; P_comma _ _) (center _).
    exact (comma_category_projection (Datatypes.pr1 ST) (Datatypes.snd ST)).
  end-/

  definition comma_category_projection_functor_morphism_of
             s d (m : morphism ((A → C)⁻¹op × (B → C)) s d)
  : morphism (Cat / !(⟨A × B, PAB⟩ : Cat))
             (comma_category_projection_functor_object_of s)
             (comma_category_projection_functor_object_of d).
  /-begin
    hnf.
    refine (CommaCategory.Build_morphism
              (comma_category_projection_functor_object_of s)
              (comma_category_projection_functor_object_of d)
              (comma_category_induced_functor m)
              (center _)
              _).
    simpl.
    destruct_head_hnf Datatypes.prod.
    path_functor.
  end-/

  Local Ltac comma_laws_t :=
    repeat (apply path_pi || intro);
    simpl;
    rewrite !transport_pi_constant;
    transport_path_pi_hammer;
    simpl;
    destruct_head Datatypes.prod;
    simpl in *;
    apply CommaCategory.path_morphism;
    simpl;
    repeat match goal with
             | [ |- context[?f _ _ _ _ _ _ _ (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport
                                   _ P _ _ _ p
                                   (λ_, f _ _ _ _ _ _ _)
                                   z)
             | [ |- context[transport (λy, ?f (?fa _ _ _ _ _ y) ?x)] ]
               => rewrite (λa b, @transport_compose _ _ a b (λy, f y x) (fa _ _ _ _ _))
             | [ |- context[transport (λy, ?f ?x (?fa _ _ _ _ _ y))] ]
               => rewrite (λa b, @transport_compose _ _ a b (λy, f x y) (fa _ _ _ _ _))
           end;
    unfold comma_category_induced_functor_object_of_identity;
    unfold comma_category_induced_functor_object_of_compose;
    simpl;
    rewrite ?CommaCategory.ap_a_path_object', ?CommaCategory.ap_b_path_object';
    try reflexivity.

  definition comma_category_projection_functor_identity_of x
  : comma_category_projection_functor_morphism_of (Category.Core.identity x)
    = 1.
  /-begin
    apply CommaCategory.path_morphism; simpl; [ | reflexivity ].
    path_functor.
    exists (path_pi _ _ (comma_category_induced_functor_object_of_identity _)).
    comma_laws_t.
  Qed.

  definition comma_category_projection_functor_composition_of s d d' m m'
  : comma_category_projection_functor_morphism_of
      (@Category.Core.compose _ s d d' m' m)
    = (comma_category_projection_functor_morphism_of m')
        ∘ (comma_category_projection_functor_morphism_of m).
  Proof.
    apply CommaCategory.path_morphism; simpl; [ | reflexivity ].
    path_functor.
    simpl.
    exists (path_pi _ _ (comma_category_induced_functor_object_of_compose m' m)).
    comma_laws_t.
  Qed.

  definition comma_category_projection_functor
  : Functor ((A → C)⁻¹op × (B → C))
            (Cat / !(⟨A × B, PAB⟩ : Cat)) :=
       Build_Functor ((A → C)⁻¹op × (B → C))
                     (Cat / !(⟨A × B, PAB⟩ : Cat))
                     comma_category_projection_functor_object_of
                     comma_category_projection_functor_morphism_of
                     comma_category_projection_functor_composition_of
                     comma_category_projection_functor_identity_of.
End comma.

section slice_category_projection_functor
  Context [H : funext].

  Variable P : PreCategory → Type.
  Context {HF : ΠC D, P C → P D → IsHSet (Functor C D)}.

  Local Notation Cat := (@sub_pre_cat _ P HF).

  Variable C : PreCategory.
  Variable D : PreCategory.

  Hypothesis P1C : P (1 × C).
  Hypothesis PC1 : P (C × 1).
  Hypothesis PC : P C.
  Hypothesis P_comma : Π(S : Functor C D) (T : Functor 1 D), P (S / T).
  Hypothesis P_comma' : Π(S : Functor 1 D) (T : Functor C D), P (S / T).

  Local Open Scope functor_scope.
  Local Open Scope category_scope.

  Local Notation inv D := (@ExponentialLaws.Law1.Functors.inverse _ terminal_category _ _ _ D).

  /- Functor [(C → D)ᵒᵖ → D → (cat / C)] -/
  definition slice_category_projection_functor
  : object (((C → D)⁻¹op) → (D → (Cat / (⟨C, PC⟩ : Cat)))).
  Proof.
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ ∘ (Functor.Identity.identity (C → D)⁻¹op,
                 inv D)).
    refine (_ ∘ @comma_category_projection_functor _ P HF C 1 D PC1 P_comma).
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor _).
  end-/

  definition coslice_category_projection_functor
  : object ((C → D)⁻¹op → (D → (Cat / (⟨C, PC⟩ : Cat)))).
  /-begin
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ ∘ (Functor.Identity.identity (C → D)⁻¹op,
                 inv D)).
    refine (_ ∘ @comma_category_projection_functor _ P HF C 1 D PC1 P_comma).
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor _).
  end-/

  /- Functor [(C → D) → Dᵒᵖ → (cat / C)] -/
  definition slice_category_projection_functor'
  : object ((C → D) → (D⁻¹op → (Cat / (⟨C, PC⟩ : Cat)))).
  /-begin
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ ∘ (Functor.Identity.identity (C → D),
                 (inv D)⁻¹op)).
    refine (_ ∘ ProductLaws.Swap.functor _ _).
    refine (_ ∘ @comma_category_projection_functor _ P HF 1 C D P1C P_comma').
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor' _).
  end-/

  definition coslice_category_projection_functor'
  : object ((C → D) → (D⁻¹op → (Cat / (⟨C, PC⟩ : Cat)))).
  /-begin
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ ∘ (Functor.Identity.identity (C → D),
                 (inv D)⁻¹op)).
    refine (_ ∘ ProductLaws.Swap.functor _ _).
    refine (_ ∘ @comma_category_projection_functor _ P HF 1 C D P1C P_comma').
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor' _).
  end-/
End slice_category_projection_functor.
