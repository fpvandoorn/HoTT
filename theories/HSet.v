/- -*- mode: coq; mode: visual-line -*-  -/
/- H-Sets -/

Require Import HoTT.Basics.
Require Import Types.Paths Types.Sigma Types.Empty Types.Record Types.unit Types.Arrow HProp.

Local Open Scope equiv_scope.
Local Open Scope path_scope.

/- A type is a set if and only if it satisfies Axiom K. -/

definition axiomK A := Π(x : A) (p : x ≈ x), p ≈ idpath x.

definition axiomK_hset {A} : IsHSet A → axiomK A.
/-begin
  intros H x p.
  apply (H x x p (idpath x)).
end-/

definition hset_axiomK {A} [H : axiomK A] : IsHSet A.
/-begin
  intros x y H.
  apply @hprop_allpath.
  intros p q.
  by induction p.
end-/

section AssumeFunext
Context [H : Funext].

definition equiv_hset_axiomK {A} : IsHSet A ≃ axiomK A.
/-begin
  apply (equiv_adjointify (@axiomK_hset A) (@hset_axiomK A)).
  - intros K. by_extensionality x. by_extensionality x'.
    cut (Contr (x=x)). intro. eapply path_contr.
    exists 1. intros. symmetry; apply K.
  - intro K. by_extensionality x. by_extensionality x'.
    eapply path_ishprop.
end-/

definition axiomK_isprop [instance] A : is_hprop (axiomK A) | 0.
/-begin
  apply (trunc_equiv _ equiv_hset_axiomK).
end-/

definition set_path2 {A} [H : IsHSet A] {x y : A} (p q : x ≈ y):
  p ≈ q.
/-begin
  induction q.
  apply axiomK_hset; assumption.
end-/

/- Recall that axiom K says that any self-path is homotopic to the
   identity path.  In particular, the identity path is homotopic to
   itself.  The following lemma says that the endo-homotopy of the
   identity path thus specified is in fact (homotopic to) its identity
   homotopy (whew!).  -/
/- TODO: What was the purpose of this lemma?  Do we need it at all?  It's actually fairly trivial. -/
definition axiomK_idpath {A} (x : A) (K : axiomK A) :
  K x (idpath x) ≈ idpath (idpath x).
/-begin
  pose (T1A := @trunc_succ _ A (@hset_axiomK A K)).
  exact (@set_path2 (x=x) (T1A x x) _ _ _ _).
end-/

End AssumeFunext.

/- We prove that if [R] is a reflexive mere relation on [X] implying identity, then [X] is an hSet, and hence [R x y] is equivalent to [x ≈ y]. -/
definition isset_hrel_subpaths
      {X R}
      [H : Reflexive X R]
      [H : Πx y, is_hprop (R x y)]
      (f : Πx y, R x y → x ≈ y)
: IsHSet X.
/-begin
  apply @hset_axiomK.
  intros x p.
  refine (_ ⬝ concat_Vp (f x x (transport (R x) p⁻¹ (reflexivity _)))).
  apply moveL_Vp.
  refine ((transport_paths_r _ _)⁻¹ ⬝ _).
  refine ((transport_arrow _ _ _)⁻¹ ⬝ _).
  refine ((ap10 (apD (f x) p) (@reflexivity X R _ x)) ⬝ _).
  apply ap.
  apply path_ishprop.
end-/

Global Instance isequiv_hrel_subpaths
       X R
       [H : Reflexive X R]
       [H : Πx y, is_hprop (R x y)]
       (f : Πx y, R x y → x ≈ y)
       x y
: IsEquiv (f x y) | 10000.
/-begin
  pose proof (isset_hrel_subpaths f).
  refine (isequiv_adjointify
            (f x y)
            (λp, transport (R x) p (reflexivity x))
            _
            _);
  intro;
  apply path_ishprop.
end-/

/- We will now prove that for sets, monos and injections are equivalent.-\
definition ismono {X Y} (f : X → Y) :=
     Π(Z : hSet),
     Πg h : Z → X, f ∘ g ≈ f ∘ h → g ≈ h.

definition isinj {X Y} (f : X → Y) :=
     Πx0 x1 : X,
       f x0 ≈ f x1 → x0 ≈ x1.

definition isinj_embedding {A B : Type} (m : A → B) : IsEmbedding m → isinj m.
/-begin
  intros ise x y p.
  pose (ise (m y)).
  assert (q : ⟨x,p⟩ ≈ ⟨y,1⟩ :> hfiber m (m y)) by apply path_ishprop.
  exact (ap dpr1 q).
end-/

definition isinj_ismono [H : Funext] {X Y} (f : X → Y) : isinj f → ismono f.
Proof.
  intros ? ? ? ? H'.
  apply path_forall.
  apply ap10 in H'.
  hnf in *; unfold compose in *.
  eauto.
Qed.

definition ismono_isinj {X Y} (f : X → Y)
           (H : ismono f)
: isinj f :=
     λx0 x1 H',
       ap10 (H (BuildhSet unit)
               (λ_, x0)
               (λ_, x1)
               (ap (λx, unit_name x) H'))
            star.

definition ismono_isequiv [H : Funext] X Y (f : X → Y) [H : IsEquiv _ _ f]
: ismono f.
Proof.
  intros ? g h H'.
  apply ap10 in H'.
  apply path_forall.
  intro x.
  transitivity (f⁻¹ (f (g x))).
  - by rewrite eissect.
  - transitivity (f⁻¹ (f (h x))).
    × apply ap. apply H'.
    × by rewrite eissect.
Qed.
