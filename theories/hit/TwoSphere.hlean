/- -*- mode: coq; mode: visual-line -*- -/

/- Theorems about the 2-sphere [S⁻¹2]. -/

Require Import HoTT.Basics HSet.
Require Import Types.Paths Types.ΠTypes.Arrow Types.Universe Types.Empty Types.unit.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

/- definition of the 2-sphere. -/

Module Export TwoSphere.

Private Inductive S2 : Type0 :=
| base : S2.

Axiom surf : refl base = refl base.

definition S2_ind (P : S2 → Type) (b : P base) (l : transport2 P surf b = refl b)
  : Π(x:S2), P x :=
     λx, match x with base => λ_, b end l.

Axiom S2_ind_beta_loop
  : Π(P : S2 → Type) (b : P base) (l : transport2 P surf b = refl b),
      apD02 (S2_ind P b l) surf = l⁻¹ ⬝ (concat_p1 _)⁻¹.

End TwoSphere.

/- The non-dependent eliminator -/

definition S2_rec (P : Type) (b : P) (l : refl b = refl b)
  : S2 → P :=
     S2_ind (λ_, P) b ((concat_p1 _)⁻¹ ⬝ (transport2_const surf b)⁻¹ ⬝ l).

/- TODO: Write the non-dependent eliminator.  It's probably something like
<<
definition S1_rec_beta_loop (P : Type) (b : P) (l : refl b = refl b)
: ap02 (S2_rec P b l) surf = l⁻¹ ⬝ (concat_p1 _)⁻¹.
Proof.
  unfold S2_rec.
  refine (cancelL (transport2_const surf b)⁻¹ _ _ _).
  refine (cancelL ((concat_p1 (transport2 (λ_ : S2, P) surf b))⁻¹) _ _ _).
...
>>
-/
