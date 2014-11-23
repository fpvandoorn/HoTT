/- -*- mode: coq; mode: visual-line -*- -/
Require Import HoTT.Basics.
Require Import Types.Paths Types.ΠTypes.Sigma Types.Arrow Types.Universe Types.unit Types.Sum.
Require Import HSet TruncType.
Require Import hit.Truncations.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

/- Homotopy Pushouts -/

(*
Record Span :=
  { A : Type; B : Type; C : Type;
    f : C → A;
    g : C → B }.

Record Cocone (S : Span) (D : Type) :=
  { i : A S → D;
    j : B S → D;
    h : Πc, i (f S c) ≈ j (g S c) }.
*)

Module Export Pushout.

Private Inductive pushout {A B C : Type} (f : A → B) (g : A → C) : Type :=
| push : B + C → pushout f g.

Arguments push {A B C f g} a.

definition pushl {A B C} {f : A → B} {g : A → C} (a : A) : pushout f g := push (inl (f a)).
definition pushr {A B C} {f : A → B} {g : A → C} (a : A) : pushout f g := push (inr (g a)).

Axiom pp : Π{A B C f g} (a:A), @pushl A B C f g a ≈ pushr a.

definition pushout_ind {A B C} (f : A → B) (g : A → C) (P : pushout f g → Type)
  (push' : Πa : B + C, P (push a))
  (pp' : Πa : A, (@pp A B C f g a) ▹ (push' (inl (f a))) ≈ push' (inr (g a)))
  : Πw, P w :=
     λw, match w with push a => λ_, push' a end pp'.

Axiom pushout_ind_beta_pp
  : Π{A B C f g} (P : @pushout A B C f g → Type)
  (push' : Πa : B + C, P (push a))
  (pp' : Πa : A, (@pp A B C f g a) ▹ (push' (inl (f a))) ≈ push' (inr (g a)))
  (a : A),
  apD (pushout_ind f g P push' pp') (pp a) ≈ pp' a.

End Pushout.

/- The non-dependent eliminator -/

definition pushout_rec {A B C} {f : A → B} {g : A → C} (P : Type)
  (push' : B + C → P)
  (pp' : Πa : A, push' (inl (f a)) ≈ push' (inr (g a)))
  : @pushout A B C f g → P :=
     pushout_ind f g (λ_, P) push' (λa, transport_const _ _ ⬝ pp' a).

definition pushout_rec_beta_pp {A B C f g} (P : Type)
  (push' : B + C → P)
  (pp' : Πa : A, push' (inl (f a)) ≈ push' (inr (g a)))
  (a : A)
  : ap (pushout_rec P push' pp') (pp a) ≈ pp' a.
/-begin
  unfold pushout_rec.
  eapply (cancelL (transport_const (pp a) _)).
  refine ((apD_const (@pushout_ind A B C f g (λ_, P) push' _) (pp a))⁻¹ ⬝ _).
  refine (pushout_ind_beta_pp (λ_, P) _ _ _).
end-/

/- Cones of hsets -/

section SetCone
  Context {A B : hSet} (f : A → B).

  definition setcone := Trunc 0 (pushout f (const star)).

  definition istrunc_setcone [instance] : IsHSet setcone := _.

  definition setcone_point : setcone := tr (push (inr star)).
End SetCone.
