/- -*- mode: coq; mode: visual-line -*- -/

/- Theorems about the homotopical interval. -/

Require Import HoTT.Basics.
Require Import hit.Interval.

/- From an interval type, we can prove function extensionality. -/

definition funext_type_from_interval : funext_type :=
     Weakfunext_implies_funext (Naivefunext_implies_Weakfunext
    (λA P f g p,
      let h := λ(x:interval) (a:A),
        interval_rec _ (f a) (g a) (p a) x
        in ap h seg)).
/- As justified by the above proof, we may assume [funext] given the interval. -/
definition funext_from_interval [instance] : funext.
Admitted.
