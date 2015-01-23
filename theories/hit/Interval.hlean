/- -*- mode: coq; mode: visual-line -*- -/

/- Theorems about the homotopical interval. -/

Require Import HoTT.Basics.
Require Import Types.Sigma Types.ΠTypes.Paths.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Module Export Interval.

Private Inductive interval : Type1 :=
  | zero : interval
  | one : interval.

Axiom seg : zero = one.

definition interval_ind (P : interval → Type)
  (a : P zero) (b : P one) (p : seg ▹ a = b)
  : Πx:interval, P x :=
     λx, (match x return _ → P x with
                | zero => λ_, a
                | one  => λ_, b
              end) p.

Axiom interval_ind_beta_seg : Π(P : interval → Type)
  (a : P zero) (b : P one) (p : seg ▹ a = b),
  apD (interval_ind P a b p) seg = p.

End Interval.

/-  Should fail:
definition test (P : interval → Type) (a : P zero) (b : P one)
      (p p' : seg ▹ a = b) :
    interval_ind P a b p = interval_ind P a b p'.
reflexivity.
-/


definition interval_rec (P : Type) (a b : P) (p : a = b)
  : interval → P :=
     interval_ind (λ_, P) a b (transport_const _ _ ⬝ p).

definition interval_rec_beta_seg (P : Type) (a b : P) (p : a = b)
  : ap (interval_rec P a b p) seg = p.
/-begin
  refine (cancelL (transport_const seg a) _ _ _).
  refine ((apD_const (interval_ind (λ_, P) a b _) seg)⁻¹ ⬝ _).
  refine (interval_ind_beta_seg (λ_, P) _ _ _).
end-/

/- The interval is contractible. -/

definition contr_interval [instance] : is_contr interval | 0.
/-begin
  exists zero.
  refine (interval_ind _ 1 seg _).
  refine (transport_paths_r _ _ ⬝ concat_1p _).
end-/
