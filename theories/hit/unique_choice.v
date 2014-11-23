Require Import HoTT.Basics hit.Truncations HProp.

definition atmost1 X:=(Πx1 x2:X, (x1 ≈ x2)).
definition atmost1P {X} (P:X->Type):=
    (Πx1 x2:X, P x1 → P x2 → (x1 ≈ x2)).
definition hunique {X} (P:X->Type):=(hexists P) × (atmost1P P).

Lemma atmost {X} {P : X → Type}:
  (Πx, is_hprop (P x)) → (atmost1P P) → atmost1 (sigT  P).
intros H H0 [x p] [y q].
specialize (H0 x y p q).
induction H0.
assert (H0: (p =q)) by apply path_ishprop.
now induction H0.
Qed.

Lemma iota {X} (P:X-> Type):
  (Πx, is_hprop (P x)) → (hunique P) → sigT P.
Proof.
intros H1 [H H0].
apply (@Trunc_rec -1 (sigT P) );auto.
by apply hprop_allpath, atmost.
Qed.

Lemma unique_choice {X Y} (R:X->Y->Type) :
 (Πx y, is_hprop (R x y)) → (Πx, (hunique (R x)))
   → Σf : X → Y, Πx, (R x (f x)).
intros X0 X1.
exists (λx:X, (dpr1 (iota _ (X0 x) (X1 x)))).
intro x. apply (dpr2 (iota _ (X0 x) (X1 x))).
Qed.
