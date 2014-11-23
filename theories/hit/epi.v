Require Import HoTT.Basics.
Require Import Types.Universe Types.unit Types.ΠTypes.Arrow Types.Sigma Types.Paths.
Require Import HProp HSet TruncType UnivalenceImpliesFunext.
Require Import hit.Pushout hit.Truncations hit.Connectedness.

Open Local Scope path_scope.
Open Local Scope equiv_scope.


section AssumingUA
Context {ua:Univalence}.

/- We will now prove that for sets, epis and surjections are equivalent.-\
definition isepi {X Y} `(f:X->Y) := ΠZ: hSet,
  Πg h: Y → Z, g ∘ f ≈ h ∘ f → g ≈ h.

definition isepi' {X Y} `(f : X → Y) :=
  Π(Z : hSet) (g : Y → Z), is_contr { h : Y → Z | g ∘ f ≈ h ∘ f }.

definition equiv_isepi_isepi' {X Y} f : @isepi X Y f ≃ @isepi' X Y f.
/-begin
  unfold isepi, isepi'.
  apply (@equiv_functor_forall' _ _ _ _ _ (equiv_idmap _)); intro Z.
  apply (@equiv_functor_forall' _ _ _ _ _ (equiv_idmap _)); intro g.
  unfold equiv_idmap; simpl.
  refine (transitivity (@equiv_sigT_ind _ (λh : Y → Z, g ∘ f ≈ h ∘ f) (λh, g ≈ h.1)) _).
  /- TODO(JasonGross): Can we do this entirely by chaining equivalences? -/
  apply equiv_iff_hprop.
  { intro hepi.
    refine {| center := ⟨g, idpath⟩ |}.
    intro xy; specialize (hepi xy).
    apply path_sigma_uncurried.
    exists hepi.
    apply path_ishprop. }
  { intros hepi xy.
    exact (ap dpr1 ((contr ⟨g, 1⟩)⁻¹ ⬝ contr xy)). }
end-/

section cones
  definition isepi'_contr_cone [H : Funext] {A B : hSet} (f : A → B) : isepi' f → is_contr (setcone f).
  /-begin
    intros hepi.
    exists (setcone_point _).
    pose (alpha1 := @pp A B unit f (const star)).
    pose (tot:= Σh : B → setcone f, tr ∘ push ∘ inl ∘ f ≈ h ∘ f ).
    pose (l := ⟨tr ∘ push ∘ inl, idpath⟩ : tot).
    pose (r := (@const B (setcone f) (setcone_point _); (ap (λf, @tr 0 _ ∘ f) (path_Π_ _ alpha1))) : tot).
    subst tot.
    assert (X : l ≈ r) by (pose (hepi (BuildhSet (setcone f)) (tr ∘ push ∘ inl)); apply path_contr).
    subst l r.

    pose (I0 b := ap10 (X ..1) b).
    refine (Trunc_ind _ _).
    pose (λa : B + unit, (match a as a return setcone_point _ ≈ tr (push a) with
                                 | inl a' => (I0 a')⁻¹
                                 | inr star => idpath
                               end)) as I0f.
    refine (pushout_ind _ _ _ I0f _).

    simpl. subst alpha1. intros.
    unfold setcone_point.
    subst I0. simpl.
    pose (X..2) as p. simpl in p. rewrite transport_precompose in p.
    assert (H':=concat (ap (λx, ap10 x a) p) (ap10_ap_postcompose tr (path_arrow pushl pushr pp) _)).
    rewrite ap10_path_arrow in H'.
    clear p.
    /- Apparently [pose; clearbody] is only ~.8 seconds, while [pose proof] is ~4 seconds? -/
    pose (concat (ap10_ap_precompose f (X ..1) a)⁻¹ H') as p.
    clearbody p.
    simpl in p.
    rewrite p.
    rewrite transport_paths_Fr.
    apply concat_Vp.
  Qed.
End cones.

definition issurj_isepi {X Y} (f:X->Y): IsSurjection f → isepi f.
intros sur ? ? ? ep. apply path_forall. intro y.
specialize (sur y). pose (center (merely (hfiber f y))).
apply (Trunc_rec (n:=-1) (A:=(sigT (λx : X, f x ≈ y))));
  try assumption.
 intros [x p]. set (p0:=apD10 ep x).
 transitivity (g (f x)). by apply ap.
 transitivity (h (f x));auto with path_hints. by apply ap.
Qed.

/- Old-style proof using polymorphic Omega. Needs resizing for the isepi proof to live in the
 same universe as X and Y (the Z quantifier is instantiated with an hSet at a level higher)
<<
definition isepi_issurj {X Y} (f:X->Y): isepi f → issurj f.
Proof.
  intros epif y.
  set (g :=λ_:Y, Unit_hp).
  set (h:=(λy:Y, (hp (hexists (λ_ : unit, Σx:X, y ≈ (f x))) _ ))).
  assert (X1: g ∘ f ≈ h ∘ f ).
  - apply path_forall. intro x. apply path_equiv_biimp_rec;[|done].
    intros _ . apply min1. exists star. by (exists x).
  - specialize (epif _ g h).
    specialize (epif X1). clear X1.
    set (p:=apD10 epif y).
    apply (@minus1Trunc_map (sigT (λ_ : unit, sigT (λx : X, y ≈ f x)))).
    + intros [ _ [x eq]].
      exists x.
        by symmetry.
    + apply (transport hproptype p star).
end-/
>> -/

section isepi_issurj
  Context {X Y : hSet} (f : X → Y) (Hisepi : isepi f).
  definition epif := equiv_isepi_isepi' _ Hisepi.
  definition fam (c : setcone f) : hProp.
  /-begin
    pose (fib y := hexists (λx : X, f x ≈ y)).
    apply (λf, @Trunc_rec _ _ hProp _ f c).
    refine (pushout_rec hProp
                           (λx : Y + unit,
                              match x with
                                | inl y => fib y
                                | inr x => Unit_hp
                              end)
                           (λx, _)).
    /- Prove that the truncated sigma is equivalent to unit -/
    pose (contr_inhabited_hprop (fib (f x)) (tr ⟨x, idpath⟩)) as i.
    apply path_hprop. simpl. simpl in i.
    apply (equiv_contr_unit).
  end-/

  definition isepi_issurj : IsSurjection f.
  /-begin
    intros y.
    pose (i := isepi'_contr_cone _ epif).

    assert (X0 : Πx : setcone f, fam x ≈ fam (setcone_point f)).
    { intros. apply contr_dom_equiv. apply i. }
    specialize (X0 (tr (push (inl y)))). simpl in X0.
    exact (transport is_contr (ap trunctype_type X0)⁻¹ _).
  end-/
End isepi_issurj.

definition isepi_isequiv X Y (f : X → Y) [H : IsEquiv _ _ f]
: isepi f.
Proof.
  intros ? g h H'.
  apply ap10 in H'.
  apply path_forall.
  intro x.
  transitivity (g (f (f⁻¹ x))).
  - by rewrite eisretr.
  - transitivity (h (f (f⁻¹ x))).
    × apply H'.
    × by rewrite eisretr.
Qed.
End AssumingUA.
