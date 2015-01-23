/- -*- mode: coq; mode: visual-line -*-  -/
/- Connectedness -/

Require Import HoTT.Basics.
Require Import Types.ΠTypes.Sigma Types.Paths Types.unit Types.Arrow Types.Universe.
Require Import TruncType UnivalenceImpliesfunext HProp EquivalenceVarieties Extensions Factorization.
Require Export Modality.        /- [Export] since the actual definitions of connectednes appear there, in the generality of a modality. -/
Require Import hit.Truncations.
Import TrM.
Local Open Scope equiv_scope.
Local Open Scope path_scope.
Local Open Scope trunc_scope.

/- Connectedness -/

/- There is a slight controversy of indexing for connectedness — in particular, how the indexing for maps shoud relate to the indexing for types.  One may reasonably take the connectedness of a map to correspond either to that of its *fibers*, or of its *cofiber*; these differ by 1.  The traditional topological indexing uses the cofiber.  We use the fiber, as does Lurie in [HTT]; but we choose to agree with the traditional indexing on types, while Lurie agrees with it on maps.

Currently, the translation is therefore as follows:

       HoTT              Traditional       Lurie

Map    (n-1)-connected   n-connected       n-connective
Type   n-connected       n-connected       (n+1)-connective

A handy benchmark: under our indexing, the map [S1 → 1] is 0-connected but not 1-connected, while the map [1 → S1] is (–1)–connected but not 0-connected.


One reason for our choice is that this way, the n-truncated and n-connected maps are the modal and modally-connected maps for the n-truncation modality.  Many of the basic lemmas about connected maps are in fact tt for any modality, and can be found in [Modality.v].  Thus, here we consider mainly properties that involve the interaction of connectedness at different truncation levels. -/


section Extensions
  Context [H : Univalence].

/- Truncatedness of the type of extensions -/

/- A key lemma on the interaction between connectedness and truncatedness: suppose one is trying to extend along an n-connected map, into a k-truncated family of types (k ≥ n).  Then the space of possible extensions is (k–n–2)-truncated.

(Mnemonic for the indexing: think of the base case, where k=n; then we know we can eliminate, so the space of extensions is contractible.)

This lemma is most useful via corollaries like the wedge-inclusion, the wiggly wedge, and their n-ary generalizations. -/
definition istrunc_extension_along_conn {m n : trunc_index}
  {A B : Type} (f : A → B) [H : IsConnMap n _ _ f]
  (P : B → Type) {HP : Πb:B, is_trunc (m -2+ n) (P b)}
  (d : Πa:A, P (f a))
: is_trunc m (ExtensionAlong f P d).
/-begin
  revert P HP d. induction m as [ | m' IH]; intros P HP d; simpl in *.
  /- m = –2 -/
  exists (extension_conn_map_elim n f P d).
  intros y. apply (allpath_extension_conn_map n); assumption.
  /- m = S m' -/
  intros e e'. refine (trunc_equiv _ (path_extension e e')).
  /- magically infers: paths in extensions = extensions into paths,
                       which by induction is m'-truncated. -/
end-/

/- Connectivity of pointed types -/

/- The connectivity of a pointed type and (the inclusion of) its point are intimately connected. -/

definition conn_pointed_type [instance] {n : trunc_index} {A : Type} (a0:A)
 [H : IsConnMap n _ _ (unit_name a0)] : IsConnected n.+1 A | 1000.
/-begin
  apply isconnected_from_elim.
  intros C HC f. exists (f a0).
  refine (conn_map_elim n (unit_name a0) _ (λ_, refl)).
end-/

definition conn_point_incl [instance] {n : trunc_index} {A : Type} (a0:A)
       [H : IsConnected n.+1 A] : IsConnMap n (unit_name a0) | 1000.
/-begin
  apply conn_map_from_extension_elim.
  intros P ?. set (PP := λa, BuildTruncType n (P a)).
  assert (QQ := isconnected_elim n.+1 (TruncType n) PP).
  destruct QQ as [[Q0 HQ] e].
  assert (e' := λa, ap trunctype_type (e a)); simpl in e'. clear HQ e.
  intros d. set (d0 := d star).
  exists (λa, (transport idmap (e' a0 ⬝ (e' a)⁻¹) d0)).
  intros []. change (d star) with (transport idmap 1 d0).
  apply ap10, ap, concat_pV.
end-/

/- TODO: generalise the above to any map with a section. -/

End Extensions.

section Wedge_Incl_Conn

/- Connectivity of the wedge into the product.

A very useful form of the key lemma [istrunc_extension_along_conn] is the connectivity of the wedge into the product, for a pair of pointed spaces.  In fact this can be formulated without mentioning the wedge per se (so, without requiring HIT’s), since the statement only needs to talk about maps out of the wedge.

Once again, we believe that the type of the conclusion is an hprop (though we do not prove it) — essentially because it is wrapping up an elimination principle and its corresponding computation rule — and so we make the proof of this result opaque. -/

Context [H : Univalence]
  {m n : trunc_index}
  {A : Type} (a0 : A) [H : IsConnected m.+1 A]
  {B : Type} (b0 : B) [H : IsConnected n.+1 B]
  (P : A → B → Type) {HP : Πa b, is_trunc (m -2+ n) (P a b)}
  (f_a0 : Πb:B, P a0 b)
  (f_b0 : Πa:A, P a b0)
  (f_a0b0 : f_a0 b0 = f_b0 a0).

Corollary isconn_wedge_incl
: Σf : Πa b, P a b
 , Σe_a0 : Πb, f a0 b = f_a0 b
 , Σe_b0 : Πa, f a b0 = f_b0 a
 , e_b0 a0 = (e_a0 b0) ⬝ f_a0b0 .
/-begin
  assert (goal_as_extension :
    ExtensionAlong (unit_name a0)
      (λa, ExtensionAlong (unit_name b0) (P a) (unit_name (f_b0 a)))
      (unit_name (f_a0 ; (unit_name f_a0b0)))).
    apply (extension_conn_map_elim m).
      apply (conn_point_incl a0).
    intros a.
    apply (istrunc_extension_along_conn (n := n)).
      apply (conn_point_incl b0).
    apply HP.
  destruct goal_as_extension as [f_eb name_ea_eab].
  assert (ea_eab := name_ea_eab star); clear name_ea_eab.
  exists (λa, dpr1 (f_eb a)).
  exists (λb, apD10 (ea_eab ..1) b).
  exists (λa, dpr2 (f_eb a) star).
/- The last component is essentially (g' ..2), wrapped in a bit of path-algebra. -/
  apply moveL_Mp.
  apply (concatR (apD10 (ea_eab ..2) star)).
  set (ea := ea_eab ..1). generalize ea; simpl. clear ea_eab ea. intros.
  rewrite transport_arrow. rewrite transport_const. rewrite transport_paths_Fl.
  exact 1.
Qed.

/- It is easier to apply the above result with its components separated. -/
definition wedge_incl_elim : Πa b, P a b :=
     isconn_wedge_incl.1.

definition wedge_incl_comp1 : Πb, wedge_incl_elim a0 b = f_a0 b :=
     isconn_wedge_incl.2.1.

definition wedge_incl_comp2 : Πa, wedge_incl_elim a b0 = f_b0 a :=
     isconn_wedge_incl.2.2.1.

definition wedge_incl_comp3
  : wedge_incl_comp2 a0 = (wedge_incl_comp1 b0) ⬝ f_a0b0 :=
     isconn_wedge_incl.2.2.2.

End Wedge_Incl_Conn.

definition wedge_incl_elim_uncurried [H : Univalence]
  {m n : trunc_index}
  {A : Type} (a0 : A) [H : IsConnected m.+1 A]
  {B : Type} (b0 : B) [H : IsConnected n.+1 B]
  (P : A → B → Type) {HP : Πa b, is_trunc (m -2+ n) (P a b)}
  (fs : Σf_a0 : Πb:B, P a0 b
       , Σf_b0 : Πa:A, P a b0
       , f_a0 b0 = f_b0 a0 )
  : Π(a : A) (b : B), P a b.
Proof.
  destruct fs as [f_a0 [f_b0 f_a0b0]].
  refine (wedge_incl_elim _ _ _ _ _ f_a0b0).
end-/