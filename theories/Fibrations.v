/- Basic facts about fibrations -/

Require Import HoTT.Basics Types.Sigma Types.Paths.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

/- Homotopy fibers -/

/- Paths in homotopy fibers can be constructed using [path_sigma] and [transport_paths_Fl]. -/

definition path_hfiber {A B : Type} {f : A → B} {y : B}
  {x1 x2 : hfiber f y} (q : x1.1 ≈ x2.1) (r : x1.2 ≈ ap f q ⬝ x2.2)
: x1 ≈ x2.
/-begin
  refine (path_sigma _ _ _ q _).
  refine (transport_paths_Fl _ _ ⬝ _).
  apply moveR_Vp, r.
end-/

/- Homotopic maps have equivalent fibers. -/

definition equiv_hfiber_homotopic
           {A B : Type} (f g : A → B) (h : f == g) (b : B)
: hfiber f b ≃ hfiber g b.
/-begin
  refine (BuildEquiv _ _ (λfx, (fx.1 ; (h fx.1)⁻¹ ⬝ fx.2)) _).
  refine (isequiv_adjointify _ (λgx, (gx.1 ; (h gx.1) ⬝ gx.2)) _ _);
    intros [a p]; simpl.
  - apply ap, concat_V_pp.
  - apply ap, concat_p_Vp.
end-/

/- Replacing a map with a fibration -/

definition equiv_fibration_replacement  {B C} (f:C ->B):
  C ≃ Σy:B, hfiber f y.
/-begin
  refine (BuildEquiv _ _ _ (BuildIsEquiv
               C Σy:B, Σx:C, f x ≈ y
               (λc, (f c; ⟨c, idpath⟩))
               (λc, c.2.1)
               _
               (λc, idpath)
               _)).
  - repeat (intros [] || intro); reflexivity.
  - reflexivity.
end-/

definition hfiber_fibration {X} (x : X) (P:X->Type):
    P x ≃ @hfiber (sigT P) X dpr1 x.
/-begin
  refine (BuildEquiv _ _ _ (BuildIsEquiv
               (P x) Σz : sigT P, z.1 ≈ x 
               (λPx, (⟨x, Px⟩; idpath))
               (λPx, transport P Px.2 Px.1.2)
               _
               (λPx, idpath)
               _)).
  - repeat (intros [] || intro); reflexivity.
  - reflexivity.
end-/

/- Exercise 4.4: The unstable octahedral axiom. -/

section UnstableOctahedral

  Context {A B C} (f : A → B) (g : B → C).

  definition hfiber_compose_map (b : B)
  : hfiber (g ∘ f) (g b) → hfiber g (g b) :=
       λx, ⟨f x.1 , x.2⟩.

  definition hfiber_hfiber_compose_map (b : B)
  : hfiber (hfiber_compose_map b) ⟨b,1⟩ ≃ hfiber f b.
  /-begin
    unfold hfiber, hfiber_compose_map.
    refine (equiv_compose' _ (equiv_inverse (equiv_sigma_assoc _ _))).
    refine (equiv_functor_sigma' (equiv_idmap _) _); intros a; simpl.
    transitivity (Σp : g (f a) ≈ g b, Σq : f a ≈ b, transport (λy, g y ≈ g b) q p ≈ 1).
    - refine (equiv_functor_sigma' (equiv_idmap _)
                (λp, equiv_inverse (equiv_path_sigma _ _ _))).
    - refine (equiv_compose' _ (equiv_sigma_symm _)).
      apply equiv_sigma_contr; intros p.
      destruct p; simpl; exact _.
  end-/

  definition hfiber_compose (c : C)
  : hfiber (g ∘ f) c ≃ Σw : hfiber g c, hfiber f w.1 .
  /-begin
    unfold hfiber, compose.
    refine (equiv_compose' (equiv_sigma_assoc
              (λx, g x ≈ c) (λw, Σx : A, f x ≈ w.1)) _).
    refine (equiv_compose' (equiv_functor_sigma' (equiv_idmap B)
             (λb, equiv_sigma_symm (λa p, f a ≈ b))) _).
    refine (equiv_compose' (equiv_sigma_symm _) _).
    refine (equiv_functor_sigma' (equiv_idmap A) _); intros a.
    refine (equiv_compose' (equiv_functor_sigma' (equiv_idmap B)
              (λb, equiv_sigma_symm0 _ _)) _); simpl.
    refine (equiv_compose' (equiv_inverse (equiv_sigma_assoc (λb, f a ≈ b) (λw, g w.1 ≈ c))) _).
    symmetry.
    refine (@equiv_contr_sigma _ (λw, g w.1 ≈ c)
             /- Unfortunately, we appear to have to give this argument explicitly so that Coq finds the correct instance. -/
             (contr_basedpaths (f a))).
  end-/

End UnstableOctahedral.

/- Fibers of [functor_sigma] -/

definition hfiber_functor_sigma {A B} (P : A → Type) (Q : B → Type)
           (f : A → B) (g : Πa, P a → Q (f a))
           (b : B) (v : Q b)
: (hfiber (functor_sigma f g) ⟨b, v⟩) ≃
  Σw : hfiber f b, hfiber (g w.1) ((w.2)⁻¹ ▹ v).
/-begin
  unfold hfiber, functor_sigma.
  equiv_via (Σx : sigT P, Σp : f x.1 ≈ b, p ▹ (g x.1 x.2) ≈ v).
  { refine (equiv_functor_sigma' (equiv_idmap _)
             (λx, equiv_inverse (equiv_path_sigma Q _ _))). }
  refine (equiv_compose' _ (equiv_inverse (equiv_sigma_assoc P _))).
  equiv_via ({a:A & Σq:f a ≈ b, Σp : P a, q ▹ (g a p) ≈ v}).
  { refine (equiv_functor_sigma' (equiv_idmap _) (λa, _)); simpl.
    refine (equiv_sigma_symm _). }
  refine (equiv_compose' _
           (equiv_sigma_assoc (λa, f a ≈ b)
             (λw, Σp : P w.1, w.2 ▹ (g w.1 p) ≈ v))).
  refine (equiv_functor_sigma' (equiv_idmap _) _);
    intros [a p]; simpl.
  refine (equiv_functor_sigma' (equiv_idmap _) _);
    intros u; simpl.
  apply equiv_moveL_transport_V.
end-/

/- Theorem 4.7.6 -/
definition hfiber_functor_sigma_idmap {A} (P Q : A → Type)
           (g : Πa, P a → Q a)
           (b : A) (v : Q b)
: (hfiber (functor_sigma idmap g) ⟨b, v⟩) ≃
   hfiber (g b) v.
/-begin
  refine (equiv_compose' _ (hfiber_functor_sigma P Q idmap g b v)).
  refine (@equiv_contr_sigma _
           (λw, hfiber (g w.1) (transport Q (w.2)⁻¹ v))
           /- Unfortunately, we appear to have to give this argument explicitly so that Coq finds the correct instance. -/
           (contr_basedpaths' b)).
end-/
