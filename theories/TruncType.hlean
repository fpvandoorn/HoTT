/- -*- mode: coq; mode: visual-line -*-  -/
/- Universes of truncated types. -/

Require Import HoTT.Basics HoTT.Types.
Require Import HProp UnivalenceImpliesfunext.
Local Open Scope equiv_scope.

Generalizable Variables A B n f.

/- Universes of truncated types

Now that we have the univalence axiom (from [types/Universe]), we study further the universes [TruncType] of truncated types (including [hProp] and [hSet]) that were defined in [Basics/Trunc].  -/

/- Paths in [TruncType] -/

section TruncType
Context [H : Univalence].

definition issig_trunctype {n : trunc_index}
  : ΣX : Type, is_trunc n X  ≃ TruncType n.
/-begin
  issig (@BuildTruncType n) (@trunctype_type n) (@istrunc_trunctype_type n).
end-/

definition isequiv_ap_trunctype [instance] {n : trunc_index} (A B : n-Type)
: is_equiv (@ap _ _ (@trunctype_type n) A B).
/-begin
  /- It seems to be easier to construct its inverse directly as an equivalence. -/
  transparent assert (e : ((A = B :> Type) ≃ (A = B :> n-Type))).
  { equiv_via ((issig_trunctype ⁻¹ A) = (issig_trunctype ⁻¹ B)).
    - simpl. apply (equiv_path_sigma_hprop
                      (trunctype_type A; istrunc_trunctype_type A)
                      (trunctype_type B; istrunc_trunctype_type B)).
    - apply symmetry. apply equiv_ap. refine _. }
  /- Apparently writing [equiv_inverse e] here instead of [e⁻¹] is much faster. -/
  refine (isequiv_homotopic (equiv_inverse e) _).
  intros p; destruct p; reflexivity.
end-/

definition equiv_path_trunctype {n : trunc_index} (A B : TruncType n)
  : (A ≃ B) ≃ (A = B :> TruncType n).
/-begin
  equiv_via (A = B :> Type).
  - apply equiv_path_universe.
  - exact (equiv_inverse (equiv.mk _ _ (@ap _ _ (@trunctype_type n) A B) _)).
end-/

definition path_trunctype {n : trunc_index} {A B : TruncType n}
  : A ≃ B → (A = B :> TruncType n) :=
   equiv_path_trunctype A B.

Global Instance isequiv_path_trunctype
       {n : trunc_index} {A B : TruncType n}
: is_equiv (@path_trunctype n A B).
/-begin
  exact _.
end-/

definition path_hset {A B} := @path_trunctype 0 A B.
definition path_hprop {A B} := @path_trunctype -1 A B.

definition istrunc_trunctype [instance] {n : trunc_index}
  : is_trunc n.+1 (TruncType n) | 0.
/-begin
  intros A B.
  refine (trunc_equiv _ (equiv_path_trunctype A B)).
  case n as [ | n'].
  - apply contr_equiv_contr_contr. /- The reason is different in this case. -/
  - apply istrunc_equiv.
end-/

definition isset_hProp [instance] : IsHSet hProp.
/-begin
  exact _.
end-/

definition Sn_trunctype: [instance] Πn, is_trunc n.+1 (sigT (IsTrunc n)) |0.
/-begin
  intro n.
  apply (trunc_equiv' _ (equiv_inverse issig_trunctype)).
end-/

/- Some standard inhabitants -/

definition Unit_hp : hProp := (BuildhProp unit).
definition False_hp : hProp := (BuildhProp Empty).
definition Negation_hp [H : funext] (hprop : hProp) : hProp := BuildhProp (~hprop).
/- We could continue with products etc -/

/- The canonical map from bool to hProp -/
definition is_true (b : bool) : hProp :=
     if b then Unit_hp else False_hp.

/- Facts about HProps using univalence -/

definition trunc_path_IsHProp [instance] X Y [H : is_hprop Y]
: is_hprop (X = Y).
/-begin
  apply hprop_allpath.
  intros pf1 pf2.
  apply (equiv_inj (equiv_path X Y)).
  apply path_equiv, path_arrow.
  intros x; by apply path_ishprop.
Qed.

definition path_iff_ishprop_uncurried [H : is_hprop A, is_hprop B]
: (A <-> B) → A = B :> Type :=
     @path_universe_uncurried _ A B ∘ equiv_iff_hprop_uncurried.

definition path_iff_hprop_uncurried {A B : hProp}
: (A <-> B) → A = B :> hProp :=
     (@path_hprop A B) ∘ (@equiv_iff_hprop_uncurried A _ B _).

definition isequiv_path_iff_ishprop_uncurried [instance] [H : is_hprop A, is_hprop B]
: is_equiv (@path_iff_ishprop_uncurried A _ B _).
Proof.
  exact _.
end-/

definition isequiv_path_iff_hprop_uncurried [instance] {A B : hProp}
: is_equiv (@path_iff_hprop_uncurried A B).
/-begin
  exact _.
end-/

definition path_iff_ishprop [H : is_hprop A, is_hprop B]
: (A → B) → (B → A) → A = B :> Type :=
     λf g, path_iff_ishprop_uncurried (f,g).

definition path_iff_hprop {A B : hProp}
: (A → B) → (B → A) → A = B :> hProp :=
     λf g, path_iff_hprop_uncurried (f,g).

End TruncType.
