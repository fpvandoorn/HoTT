/- -*- mode: coq; mode: visual-line -*- -/
Require Import HoTT.Basics.
Require Import Types.Sigma Types.Forall.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

/- Null homotopies of maps -/
section NullHomotopy
Context [H : Funext].

/- Geometrically, a nullhomotopy of a map [f : X → Y] is an extension of [f] to a map [Cone X → Y].  One might more simply call it e.g. [Constant f], but that is a little ambiguous: it could also reasonably mean e.g. a factorisation of [f] through [ Trunc -1 X ].  (Should the unique map [0 → Y] be constant in one way, or in [Y]-many ways?) -/

definition NullHomotopy {X Y : Type} (f : X → Y) :=
     Σy : Y, Πx:X, f x ≈ y.

definition istrunc_nullhomotopy {n : trunc_index}
  {X Y : Type} (f : X → Y) [H : is_trunc n Y]
  : is_trunc n (NullHomotopy f).
/-begin
  apply @trunc_sigma; auto.
  intros y. apply (@trunc_Π_).
  intros x. apply trunc_succ.
end-/

End NullHomotopy.
