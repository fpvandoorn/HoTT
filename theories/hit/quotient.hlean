/- -*- mode: coq; mode: visual-line -*-  -/
Require Import HoTT.Basics.
Require Import Types.Universe Types.Arrow Types.Sigma.
Require Import HSet HProp UnivalenceImpliesfunext TruncType.
Require Import hit.epi hit.Truncations hit.Connectedness.

Open Local Scope path_scope.
Open Local Scope equiv_scope.

/- Quotient of a Type by an hprop-valued relation

We aim to model:
<<
Inductive quotient : Type :=
   | class_of : A → quotient
   | related_classes_eq : Πx y, (R x y), class_of x = class_of y
   | quotient_set : IsHSet quotient
>>
-/

/- This development should be further connected with the sections in the book; see below.-\

Module Export Quotient.

  section Domain

    Context {A : Type} (R:relation A) {sR: is_mere_relation _ R}.

    /- We choose to let the definition of quotient depend on the proof that [R] is a set-relations.  Alternatively, we could have defined it for all relations and only develop the theory for set-relations.  The former seems more natural.

We do not require [R] to be an equivalence relation, but implicitly consider its transitive-reflexive closure. -/


    /- Note: If we wanted to be really accurate, we'd need to put [@quotient A R sr] in the max [U_{sup(i, j)}] of the universes of [A : U_i] and [R : A → A → U_j].  But this requires some hacky code, at the moment, and the only thing we gain is avoiding making use of an implicit hpropositional resizing "axiom". -/

    /- This definition has a parameter [sR] that shadows the ambient one in the Context in order to ensure that it actually ends up depending on everything in the Context when the section is closed, since its definition doesn't actually refer to any of them.  -/
    Private Inductive quotient {sR: is_mere_relation _ R} : Type :=
    | class_of : A → quotient.

    /- The path constructors. -/
    Axiom related_classes_eq
    : Π{x y : A}, R x y ->
                        class_of x = class_of y.

    Axiom quotient_set : IsHSet (@quotient sR).
    Global Existing Instance quotient_set.

    definition quotient_ind (P : (@quotient sR) → Type) {sP : Πx, IsHSet (P x)}
               (dclass : Πx, P (class_of x))
               (dequiv : (Πx y (H : R x y), (related_classes_eq H) ▹ (dclass x) = dclass y))
    : Πq, P q :=
         λq, match q with class_of a => λ_ _, dclass a end sP dequiv.

    definition quotient_ind_compute {P sP} dclass dequiv x
    : @quotient_ind P sP dclass dequiv (class_of x) = dclass x.
    /-begin
      reflexivity.
    end-/

    /- Again equality of paths needs to be postulated -/
    Axiom quotient_ind_compute_path
    : ΠP sP dclass dequiv,
      Πx y (H : R x y),
        apD (@quotient_ind P sP dclass dequiv) (related_classes_eq H)
        = dequiv x y H.

  End Domain.

End Quotient.

section Equiv

  Context [H : Univalence].

  Context {A : Type} (R : relation A) {sR: is_mere_relation _ R}
          {Htrans : Transitive R} {Hsymm : Symmetric R}.

  definition quotient_path2 : Π{x y : quotient R} (p q : x=y), p=q.
  /-begin
    apply @set_path2. apply _.
  end-/

  definition in_class : quotient R → A → hProp.
  /-begin
    refine (quotient_ind R (λ_, A → hProp) (λa b, BuildhProp (R a b)) _).
    intros. eapply concat;[apply transport_const|].
    apply path_forall. intro z. apply path_hprop; simpl.
    apply @equiv_iff_hprop; eauto.
  end-/

  Context {Hrefl : Reflexive R}.

  definition in_class_pr : Πx y, (in_class (class_of R x) y : Type) = R x y.
  /-begin
    reflexivity.
  end-/

  definition quotient_ind_prop (P : quotient R → hProp):
    Πdclass : Πx, P (class_of R x),
    Πq, P q.
  /-begin
    intros. apply (quotient_ind R P dclass).
    intros. apply path_ishprop.
  end-/

  definition class_of_repr : Πq x, in_class q x → q = class_of R x.
  /-begin
    apply (quotient_ind R
                        (λq : quotient R, Πx, in_class q x → q = class_of _ x)
                        (λx y H, related_classes_eq R H)).
    intros.
    apply path_forall. intro z.
    apply path_forall;intro H'.
    apply quotient_path2.
  end-/

  definition classes_eq_related : Πx y,
                               class_of R x = class_of R y → R x y.
  /-begin
    intros x y H'.
    pattern (R x y).
    eapply transport. apply in_class_pr.
    pattern (class_of R x). apply (transport _ (H'⁻¹)).
    apply Hrefl.
  end-/

  /- Thm 10.1.8 -/
  definition sets_exact : Πx y, (class_of R x = class_of R y) ≃ R x y.
    intros ??. apply equiv_iff_hprop.
    apply classes_eq_related.
    apply related_classes_eq.
  Defined.

  definition quotient_rec {B : Type} {sB : IsHSet B}
             (dclass : (Πx : A, B))
             (dequiv : (Πx y, R x y → dclass x = dclass y))
  : quotient R → B.
  /-begin
    apply (quotient_ind R (λ_ : quotient _, B)) with dclass.
    intros ?? H'. destruct (related_classes_eq R H'). by apply dequiv.
  end-/

  definition quotient_rec2 {B : hSet} {dclass : (A → A → B)}:
    Πdequiv : (Πx x', R x x' → Πy y',  R y y' ->
                                                          dclass x y = dclass x' y'),
      quotient R → quotient R → B.
  /-begin
    intro.
    assert (dequiv0 : Πx x0 y : A, R x0 y → dclass x x0 = dclass x y)
      by (intros ? ? ? Hx; apply dequiv;[apply Hrefl|done]).
    refine (quotient_rec
              (λx, quotient_rec (dclass x) (dequiv0 x)) _).
    intros x x' Hx.
    apply path_forall. red.
    assert (dequiv1 : Πy : A,
                        quotient_rec (dclass x) (dequiv0 x) (class_of _ y) =
                        quotient_rec (dclass x') (dequiv0 x') (class_of _ y))
      by ⟨intros, by apply dequiv⟩.
    refine (quotient_ind R (λq,
                              quotient_rec (dclass x) (dequiv0 x) q =
                              quotient_rec (dclass x') (dequiv0 x') q) dequiv1 _).
    intros. apply path_ishprop.
  end-/

  definition quotient_ind_prop' : ΠP : quotient R → Type,
                                  Π(Hprop' : Πx, is_hprop (P (class_of _ x))),
                                    (Πx, P (class_of _ x)) → Πy, P y.
  /-begin
    intros ? ? dclass. apply quotient_ind with dclass.
    - refine (quotient_ind R (λx, IsHSet (P x)) _ _); try exact _.
      intros; apply path_ishprop.
    - intros. apply Hprop'.
  end-/

  /- From Ch6 -/
  definition quotient_surjective: IsSurjection (class_of R).
  /-begin
    apply BuildIsSurjection.
    apply (quotient_ind_prop (λy, merely (hfiber (class_of R) y))); try exact _.
    intro x. apply tr. by exists x.
  end-/

  /- From Ch10 -/
  definition quotient_ump' (B:hSet): (quotient R → B) ->
                                     (sigT (λf : A-> B, (Πa a0:A, R a a0 → f a =f a0))).
    intro f. exists (compose f (class_of R) ).
    intros. unfold compose. f_ap. by apply related_classes_eq.
  Defined.

  definition quotient_ump'' (B:hSet): (sigT (λf : A-> B, (Πa a0:A, R a a0 → f a =f a0)))
                                      → quotient R → B.
    intros [f H'].
    apply (quotient_rec _ H').
  Defined.

  definition quotient_ump (B:hSet): (quotient R → B) ≃
                                                   (sigT (λf : A-> B, (Πa a0:A, R a a0 → f a =f a0))).
  /-begin
    refine (equiv_adjointify (quotient_ump' B) (quotient_ump'' B) _ _).
    intros [f Hf].
    - by apply equiv_path_sigma_hprop.
    - intros f.
      apply path_forall.
      red. apply quotient_ind_prop';[apply _|reflexivity].
  end-/

  /- Missing

  The equivalence with VVquotient [A//R].

  This should lead to the unnamed theorem:

  10.1.10. Equivalence relations are effective and there is an equivalence [A/R≃A//R]. -/

  (**
  The theory of canonical quotients is developed by C.Cohen:
  http://perso.crans.org/cohen/work/quotients/
 *)

End Equiv.

section Kernel

  /- Quotients of kernels of maps to sets give a surjection/mono factorization. -/

  Context {fs : funext}.

  /- A function we want to factor. -/
  Context {A B : Type} [H : IsHSet B] (f : A → B).

  /- A mere relation equivalent to its kernel. -/
  Context (R : relation A) {sR : is_mere_relation _ R}.
  Context (is_ker : Πx y, f x = f y ≃ R x y).

  definition quotient_kernel_factor
  : exists (C : Type) (e : A → C) (m : C → B),
      IsHSet C × IsSurjection e × IsEmbedding m × (f = m ∘ e).
  /-begin
    pose (C := quotient R).
    /- We put this explicitly in the context so that typeclass resolution will pick it up. -/
    assert (IsHSet C) by ⟨unfold C, apply _⟩.
    exists C.
    pose (e := class_of R).
    exists e.
    transparent assert (m : (C → B)).
    { apply quotient_ind with f; try exact _.
      intros x y H. transitivity (f x).
      - apply transport_const.
      - exact ((is_ker x y) ⁻¹ H). }
    exists m.
    split. split. split.
    - assumption.
    - apply quotient_surjective.
    - intro u.
      apply hprop_allpath.
      assert (H : Π(x y : C) (p : m x = u) (p' : m y = u), x = y).
      { refine (quotient_ind R _ _ _). intro a.
        refine (quotient_ind R _ _ _). intros a' p p'; fold e in p, p'.
        + apply related_classes_eq.
          refine (is_ker a a' _).
          change (m (e a) = m (e a')).
          exact (p ⬝ p'⁻¹).
        + intros; apply path_ishprop.
        + intros; apply path_ishprop. }
      intros [x p] [y p'].
      apply path_sigma_hprop; simpl.
      exact (H x y p p').
    - reflexivity.
  end-/

End Kernel.
