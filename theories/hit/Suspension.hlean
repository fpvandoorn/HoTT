/- -*- mode: coq; mode: visual-line -*- -/

/- The suspension of a type -/

Require Import HoTT.Basics Types.Paths NullHomotopy.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

/- definition of suspension. -/

Module Export Suspension.

/- We play games to ensure that [Susp X] does not live in a lower universe than [X] -/
section hack_my_types
Let U := Type.
Private Inductive Susp (X : U) : U :=
  | North : Susp X
  | South : Susp X.
End hack_my_types.

Global Arguments North {X}.
Global Arguments South {X}.

Axiom merid : Π(X : Type) (x : X), North = South :> Susp X.
Global Arguments merid {X} x.

definition Susp_ind {X : Type} (P : Susp X → Type)
  (H_N : P North) (H_S : P South)
  (H_merid : Πx:X, (merid x) ▹ H_N = H_S)
: Π(y:Susp X), P y :=
   λy, (match y return (_ → P y)
     with North => (λ_, H_N) | South => (λ_, H_S) end) H_merid.

Axiom Susp_comp_merid : Π{X : Type} (P : Susp X → Type)
  (H_N : P North) (H_S : P South)
  (H_merid : Πx:X, (merid x) ▹ H_N = H_S)
  (x:X),
apD (Susp_ind P H_N H_S H_merid) (merid x) = H_merid x.

End Suspension.

/- Non-dependent eliminator. -/

definition Susp_rec {X Y : Type}
  (H_N H_S : Y) (H_merid : X → H_N = H_S)
: Susp X → Y.
/-begin
  apply (Susp_ind (λ_, Y) H_N H_S).
  intros x. exact (transport_const _ _ ⬝ H_merid x).
end-/

definition Susp_comp_nd_merid {X Y : Type}
  {H_N H_S : Y} {H_merid : X → H_N = H_S} (x:X)
: ap (Susp_rec H_N H_S H_merid) (merid x) = H_merid x.
/-begin
  apply (cancelL (transport_const (merid x) H_N)).
  transitivity (apD (Susp_rec H_N H_S H_merid) (merid x)).
  apply symmetry. refine (apD_const (Susp_rec H_N H_S H_merid) _).
  refine (Susp_comp_merid (λ_ : Susp X, Y) _ _ _ _).
end-/

/- Eta-rule. -/

/- The eta-rule for suspension states that any function out of a suspension is equal to one defined by [Susp_ind] in the obvious way. We give it first in a weak form, producing just a pointwise equality, and then turn this into an actual equality using [funext]. -/
definition Susp_eta_homot {X : Type} {P : Susp X → Type} (f : Πy, P y)
  : f ∼ Susp_ind P (f North) (f South) (λx, apD f (merid x)).
/-begin
  unfold pointwise_paths. refine (Susp_ind _ 1 1 _).
  intros x.
  refine (transport_paths_FlFr_D
    (g := Susp_ind P (f North) (f South) (λx : X, apD f (merid x)))
    _ _ ⬝ _); simpl.
  apply moveR_pM. apply (concat (concat_p1 _)), (concatR (concat_1p _)⁻¹).
  apply ap, inverse. refine (Susp_comp_merid _ _ _ _ _).
end-/

definition Susp_eta [H : funext]
  {X : Type} {P : Susp X → Type} (f : Πy, P y)
  : f = Susp_ind P (f North) (f South) (λx, apD f (merid x)) :=
   path_pi _ _ (Susp_eta_homot f).

/- Nullhomotopies of maps out of suspensions -/

definition nullhomot_susp_from_paths {X Z: Type} (f : Susp X → Z)
  (n : NullHomotopy (λx, ap f (merid x)))
: NullHomotopy f.
/-begin
  exists (f North).
  refine (Susp_ind _ 1 n.1⁻¹ _); intros x.
  refine (transport_paths_Fl _ _ ⬝ _).
  apply (concat (concat_p1 _)), ap. apply n.2.
end-/

definition nullhomot_paths_from_susp {X Z: Type} (H_N H_S : Z) (f : X → H_N = H_S)
  (n : NullHomotopy (Susp_rec H_N H_S f))
: NullHomotopy f.
/-begin
  exists (n.2 North ⬝ (n.2 South)⁻¹).
  intro x. apply moveL_pV.
  transitivity (ap (Susp_rec H_N H_S f) (merid x) ⬝ n.2 South).
  apply whiskerR, inverse, Susp_comp_nd_merid.
  refine (concat_Ap n.2 (merid x) ⬝ _).
  apply (concatR (concat_p1 _)), whiskerL. apply ap_const.
end-/

/- Pointedness of [Susp] and path spaces thereof -/
/- We arbitrarily choose [North] to be the point. -/
definition ispointed_susp [instance] {X : Type} : IsPointed (Susp X) | 0 :=
     North.

definition ispointed_path_susp [instance] [H : IsPointed X] : IsPointed (North = South :> Susp X) | 0 :=
     merid (point X).

definition ispointed_path_susp' [instance] [H : IsPointed X] : IsPointed (South = North :> Susp X) | 0 :=
     (merid (point X))⁻¹.
