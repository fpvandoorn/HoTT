/- -*- mode: coq; mode: visual-line -*- -/

/- The spheres, in all dimensions. -/

Require Import HoTT.Basics.
Require Import Types.Sigma Types.ΠTypes.Paths Types.bool.
Require Import HProp NullHomotopy.
Require Import hit.Suspension hit.Circle.
Local Open Scope trunc_scope.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

/- Definition, by iterated suspension. -/

/- To match the usual indexing for spheres, we have to pad the sequence with a dummy term [Sphere -2]. -/
Fixpoint Sphere (n : trunc_index) :=
     match n return Type with
       | -2 => Empty
       | -1 => Empty
       | n'.+1 => Susp (Sphere n')
     end.

/- Explicit equivalences in low dimensions  -/

definition Sph0_to_Bool : (Sphere 0) → bool.
/-begin
  simpl. apply (Susp_rec tt ff). intros [].
end-/

definition isequiv_Sph0_to_Bool [instance] : is_equiv (Sph0_to_Bool) | 0.
/-begin
  apply isequiv_adjointify with (λb : bool, if b then North else South).
  intros [ | ]; exact 1.
  unfold Sect. refine (Susp_ind _ 1 1 _). intros [].
end-/

definition Sph1_to_S1 : (Sphere (nat_to_trunc_index 1)) → S1.
/-begin
  apply (Susp_rec base base).
  exact (λx, if (Sph0_to_Bool x) then loop else 1).
end-/

definition S1_to_Sph1 : S1 → (Sphere (nat_to_trunc_index 1)).
/-begin
  apply (S1_rec _ North). exact (merid North ⬝ (merid South)⁻¹).
end-/

definition isequiv_Sph1_to_S1 : is_equiv (Sph1_to_S1).
/-begin
  apply isequiv_adjointify with S1_to_Sph1.
    refine (S1_ind _ 1 _).
    refine ((transport_paths_FFlr _ _) ⬝ _).
    unfold S1_to_Sph1; rewrite S1_rec_beta_loop.
    rewrite ap_pp, ap_V.
    unfold Sph1_to_S1. simpl. rewrite 2 Susp_comp_nd_merid. simpl.
    hott_simpl.
  refine (Susp_ind (λx, S1_to_Sph1 (Sph1_to_S1 x) = x)
    1 (merid South) _); intros x.
  refine ((transport_paths_FFlr _ _) ⬝ _).
  unfold Sph1_to_S1; rewrite (Susp_comp_nd_merid x).
  revert x. change (Susp Empty) with (Sphere 0).
  apply (equiv_ind (Sph0_to_Bool ⁻¹)); intros x.
  case x; simpl.
    2: apply concat_1p.
  unfold S1_to_Sph1; rewrite S1_rec_beta_loop.
  refine (whiskerR (concat_p1 _) _ ⬝ _).
  apply moveR_Vp. hott_simpl.
end-/

/- Truncatedness via spheres  -/

/- We show here that a type is n-truncated if and only if every map from the (n+1)-sphere into it is null-homotopic.  (One direction of this is of course the assertion that the (n+1)-sphere is n-connected.) -/

/- TODO: re-type these lemmas in terms of truncation. -/

Fixpoint allnullhomot_trunc {n : trunc_index} {X : Type} [H : is_trunc n X]
  (f : Sphere n.+1 → X) {struct n}
: NullHomotopy f.
/-begin
  destruct n as [ | n'].
  - simpl in *. exists (center X). intros [ ].
  - apply nullhomot_susp_from_paths.
    apply allnullhomot_trunc; auto with typeclass_instances.
end-/

Fixpoint trunc_allnullhomot {n : trunc_index} {X : Type}
  (HX : Π(f : Sphere n.+2 → X), NullHomotopy f) {struct n}
: is_trunc n.+1 X.
/-begin
  destruct n as [ | n'].
  /- n = -2 -/ apply hprop_allpath.
    intros x0 x1. set (f := (λb, if (Sph0_to_Bool b) then x0 else x1)).
    set (n := HX f). exact (n.2 North ⬝ (n.2 South)⁻¹).
  /- n ≥ -1 -/ intros x0 x1.
    apply (trunc_allnullhomot n').
    intro f. apply nullhomot_paths_from_susp, HX.
end-/
