
  /- Functorial action -/

  /- The functoriality of [forall] is slightly subtle: it is contravariant in the domain type and covariant in the codomain, but the codomain is dependent on the domain. -/
  definition functor_pi `{P : A → Type} {Q : B → Type}
      (f0 : B → A) (f1 : Πb:B, P (f0 b) → Q b)
    : (Πa:A, P a) → (Πb:B, Q b) :=
       (λg b, f1 _ (g (f0 b))).

  definition ap_functor_pi `{P : A → Type} {Q : B → Type}
      (f0 : B → A) (f1 : Πb:B, P (f0 b) → Q b)
      (g g' : Πa:A, P a) (h : g ∼ g')
    : ap (functor_pi f0 f1) (path_pi _ _ h)
      = path_pi _ _ (λb:B, (ap (f1 b) (h (f0 b)))).
  /-begin
    revert h.  equiv_intro (@apD10 A P g g') h.
    destruct h.  simpl.
    transitivity (refl (functor_pi f0 f1 g)).
    - exact (ap (ap (functor_pi f0 f1)) (path_pi_1 g)).
    - apply symmetry.  apply path_pi_1.
  end-/

  /- Equivalences -/

  definition isequiv_functor_pi [instance] {P : A → Type} {Q : B → Type}
    [H : is_equiv B A f] [H : Πb, @is_equiv (P (f b)) (Q b) (g b)]
    : is_equiv (functor_pi f g) | 1000.
  /-begin
    refine (isequiv_adjointify (functor_pi f g)
      (functor_pi (f⁻¹)
        (λ(x:A) (y:Q (f⁻¹ x)), retr f x ▹ (g (f⁻¹ x))⁻¹ y
        )) _ _);
    intros h.
    - abstract (
          apply path_forall; intros b; unfold functor_forall;
          rewrite adj;
          rewrite <- transport_compose;
          rewrite ap_transport;
          rewrite retr;
          apply apD
        ).
    - abstract (
          apply path_forall; intros a; unfold functor_forall;
          rewrite sect;
          apply apD
        ).
  end-/

  definition equiv_functor_pi `{P : A → Type} {Q : B → Type}
    (f : B → A) [H : is_equiv B A f]
    (g : Πb, P (f b) → Q b)
    [H : Πb, @is_equiv (P (f b)) (Q b) (g b)]
    : (Πa, P a) ≃ (Πb, Q b) :=
       equiv.mk _ _ (functor_pi f g) _.

  definition equiv_functor_forall' {P : A → Type} {Q : B → Type}
    (f : B ≃ A) (g : Πb, P (f b) ≃ Q b)
    : (Πa, P a) ≃ (Πb, Q b) :=
       equiv_functor_pi f g.

  definition equiv_functor_pi_id {P : A → Type} {Q : A → Type}
    (g : Πa, P a ≃ Q a)
    : (Πa, P a) ≃ (Πa, Q a) :=
       equiv_functor_pi (equiv_idmap A) g.

  /- Truncatedness: any dependent product of n-types is an n-type -/

  definition contr_pi [instance] {P : A → Type} [H : Πa, is_contr (P a)]
    : is_contr (Πa, P a) | 100.
  /-begin
    exists (λa, center (P a)).
    intro f.  apply path_forall.  intro a.  apply contr.
  end-/

  definition trunc_pi [instance] {P : A → Type} [H : Πa, is_trunc n (P a)]
    : is_trunc n (Πa, P a) | 100.
  /-begin
    generalize dependent P.
    simple_induction n n IH; simpl; intros P ?.
    /- case [n = -2], i.e. contractibility -/
    - exact _.
    /- case n = n'.+1 -/
    - intros f g; apply (trunc_equiv _ (apD10 ⁻¹)).
  end-/

  /- apply symmetry.of curried arguments -/

  /- Using the standard Haskell name for this, as it’s a handy utility function.

  Note: not sure if [P] will usually be deducible, or whether it would be better explicit. -/
  definition flip {P : A → B → Type}
    : (Πa b, P a b) → (Πb a, P a b) :=
       λf b a, f a b.

  definition isequiv_flip [instance] {P : A → B → Type}
    : is_equiv (@flip _ _ P) | 0.
  /-begin
    set (flip_P := @flip _ _ P).
    set (flip_P_inv := @flip _ _ (flip P)).
    set (flip_P_is_sect := (λf, 1) : Sect flip_P flip_P_inv).
    set (flip_P_is_retr := (λg, 1) : Sect flip_P_inv flip_P).
    exists flip_P_inv flip_P_is_retr flip_P_is_sect.
    intro g.  exact 1.
  end-/

  definition equiv_flip `(P : A → B → Type)
    : (Πa b, P a b) ≃ (Πb a, P a b) :=
       equiv.mk _ _ (@flip _ _ P) _.

  End Assumefunext.
