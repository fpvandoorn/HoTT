/- -*- mode: coq; mode: visual-line -*- -/
/- Theorems about the universe, including the Univalence Axiom. -/

Require Import HoTT.Basics.
Require Import Types.Sigma Types.Arrow Types.Paths Types.Equiv.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables A B f.

/- Paths -/

definition isequiv_path [instance] {A B : Type} (p : A = B)
  : is_equiv (transport (λX:Type, X) p) | 0 :=
     is_equiv.mk _ _ _ (transport (λX:Type, X) p⁻¹)
  (transport_pV idmap p)
  (transport_Vp idmap p)
  (λa, match p in _ = C return
              (transport_pp idmap p⁻¹ p (transport idmap p a))⁻¹ @
                 transport2 idmap (concat_Vp p) (transport idmap p a) =
              ap (transport idmap p) ((transport_pp idmap p p⁻¹ a) ⁻¹ @
                transport2 idmap (concat_pV p) a) with refl => 1 end).

definition equiv_path (A B : Type) (p : A = B) : A ≃ B :=
     equiv.mk _ _ (transport (λX:Type, X) p) _.

definition equiv_path_V [H : funext] (A B : Type) (p : A = B) :
  equiv_path B A (p⁻¹) = equiv_inverse (equiv_path A B p).
/-begin
  destruct p. simpl. unfold equiv_path, equiv_inverse. simpl. apply ap.
  refine (@path_ishprop _ (hprop_isequiv _) _ _).
end-/

/- See the note by [funext] in Overture.v -/
Class Univalence.
Axiom isequiv_equiv_path : Π[H : Univalence] (A B : Type), is_equiv (equiv_path A B).

section Univalence
Context [H : Univalence].

definition path_universe_uncurried {A B : Type} (f : A ≃ B) : A = B :=
     (equiv_path A B)⁻¹ f.

definition path_universe {A B : Type} (f : A → B) {feq : is_equiv f} : (A = B) :=
     path_universe_uncurried (equiv.mk _ _ f feq).

definition eta_path_universe {A B : Type} (p : A = B)
  : path_universe (equiv_path A B p) = p :=
     sect (equiv_path A B) p.

definition isequiv_path_universe {A B : Type}
  : is_equiv (@path_universe_uncurried A B) :=
    _.

definition equiv_path_universe (A B : Type) : (A ≃ B) ≃ (A = B) :=
     equiv.mk _ _ (@path_universe_uncurried A B) isequiv_path_universe.

definition path_universe_V_uncurried [H : funext] {A B : Type} (f : A ≃ B)
  : path_universe_uncurried (equiv_inverse f) = (path_universe_uncurried f)⁻¹.
/-begin
  revert f. equiv_intro ((equiv_path_universe A B)⁻¹) p. simpl.
  transitivity (p⁻¹).
    2: exact (inverse2 (retr (equiv_path_universe A B) p)⁻¹).
  unfold compose. transitivity (path_universe_uncurried (equiv_path B A p⁻¹)).
    by refine (ap _ (equiv_path_V A B p)⁻¹).
  by refine (sect (equiv_path B A) p⁻¹).
end-/

definition path_universe_V [H : funext] `(f : A → B) [H : is_equiv A B f]
  : path_universe (f⁻¹) = (path_universe f)⁻¹ :=
     path_universe_V_uncurried (equiv.mk A B f _).

/- Transport -/

/- There are two ways we could define [transport_path_universe]: we could give an explicit definition, or we could reduce it to paths by [equiv_ind] and give an explicit definition there.  The two should be equivalent, but we choose the second for now as it makes the currently needed coherence lemmas easier to prove. -/
definition transport_path_universe_uncurried
           {A B : Type} (f : A ≃ B) (z : A)
  : transport (λX:Type, X) (path_universe f) z = f z.
/-begin
  revert f.  equiv_intro (equiv_path A B) p.
  exact (ap (λs, transport idmap s z) (sect _ p)).
end-/

definition transport_path_universe
           {A B : Type} (f : A → B) {feq : is_equiv f} (z : A)
  : transport (λX:Type, X) (path_universe f) z = f z :=
     transport_path_universe_uncurried (equiv.mk A B f feq) z.
/- Alternatively, [ap10 (ap equiv_fun (retr (equiv_path A B) (equiv.mk _ _ f feq))) z]. -/

definition transport_path_universe_equiv_path
           {A B : Type} (p : A = B) (z : A)
  : transport_path_universe (equiv_path A B p) z =
    (ap (λs, transport idmap s z) (sect _ p)) :=
     equiv_ind_comp _ _ _.

/- This somewhat fancier version is useful when working with HITs. -/
definition transport_path_universe'
  {A : Type} (P : A → Type) {x y : A} (p : x = y)
  (f : P x ≃ P y) (q : ap P p = path_universe f) (u : P x)
  : transport P p u = f u :=
     transport_compose idmap P p u
   ⬝ ap10 (ap (transport idmap) q) u
   ⬝ transport_path_universe f u.

/- And a version for transporting backwards. -/

definition transport_path_universe_V_uncurried [H : funext]
           {A B : Type} (f : A ≃ B) (z : B)
  : transport (λX:Type, X) (path_universe f)⁻¹ z = f⁻¹ z.
/-begin
  revert f. equiv_intro (equiv_path A B) p.
  exact (ap (λs, transport idmap s z) (inverse2 (sect _ p))).
end-/

definition transport_path_universe_V [H : funext]
           {A B : Type} (f : A → B) {feq : is_equiv f} (z : B)
  : transport (λX:Type, X) (path_universe f)⁻¹ z = f⁻¹ z :=
     transport_path_universe_V_uncurried (equiv.mk _ _ f feq) z.
/- Alternatively, [(transport2 idmap (path_universe_V f) z)⁻¹ ⬝ (transport_path_universe (f⁻¹) z)]. -/

definition transport_path_universe_V_equiv_path [H : funext]
           {A B : Type} (p : A = B) (z : B)
  : transport_path_universe_V (equiv_path A B p) z =
    ap (λs, transport idmap s z) (inverse2 (sect _ p)) :=
     equiv_ind_comp _ _ _.

/- And some coherence for it. -/

definition transport_path_universe_Vp_uncurried [H : funext]
           {A B : Type} (f : A ≃ B) (z : A)
: ap (transport idmap (path_universe f)⁻¹) (transport_path_universe f z)
  ⬝ transport_path_universe_V f (f z)
  ⬝ sect f z
  = transport_Vp idmap (path_universe f) z.
/-begin
  pattern f.
  refine (equiv_ind (equiv_path A B) _ _ _); intros p.
  /- Something slightly sneaky happens here: by definition of [equiv_path], [sect (equiv_path A B p)] is judgmentally equal to [transport_Vp idmap p].  Thus, we can apply [ap_transport_Vp]. -/
  refine (_ ⬝ ap_transport_Vp p (path_universe (equiv_path A B p))
            (sect (equiv_path A B) p) z).
  apply whiskerR. apply concat2.
  - apply ap. apply transport_path_universe_equiv_path.
  - apply transport_path_universe_V_equiv_path.
end-/

definition transport_path_universe_Vp [H : funext]
           {A B : Type} (f : A → B) {feq : is_equiv f} (z : A)
: ap (transport idmap (path_universe f)⁻¹) (transport_path_universe f z)
  ⬝ transport_path_universe_V f (f z)
  ⬝ sect f z
  = transport_Vp idmap (path_universe f) z :=
   transport_path_universe_Vp_uncurried (equiv.mk A B f feq) z.


/- Equivalence induction -/

/- Paulin-Mohring style -/
definition equiv_induction {U : Type} (P : ΠV, U ≃ V → Type) :
  (P U (equiv_idmap U)) → (ΠV (w : U ≃ V), P V w).
/-begin
  intros H0 V w.
  apply (equiv_ind (equiv_path U V)).
  exact (paths_ind U (λY p, P Y (equiv_path U Y p)) H0 V).
end-/

definition equiv_induction_comp {U : Type} (P : ΠV, U ≃ V → Type)
  (didmap : P U (equiv_idmap U))
  : equiv_induction P didmap U (equiv_idmap U) = didmap :=
     (equiv_ind_comp (P U) _ 1).

/- Martin-Lof style -/
definition equiv_induction' (P : ΠU V, U ≃ V → Type) :
  (ΠT, P T T (equiv_idmap T)) → (ΠU V (w : U ≃ V), P U V w).
/-begin
  intros H0 U V w.
  apply (equiv_ind (equiv_path U V)).
  exact (paths_ind' (λX Y p, P X Y (equiv_path X Y p)) H0 U V).
end-/

definition equiv_induction'_comp (P : ΠU V, U ≃ V → Type)
  (didmap : ΠT, P T T (equiv_idmap T)) (U : Type)
  : equiv_induction' P didmap U U (equiv_idmap U) = didmap U :=
     (equiv_ind_comp (P U U) _ 1).

End Univalence.
