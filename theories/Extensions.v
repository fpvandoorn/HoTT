/- -*- mode: coq; mode: visual-line -*- -/

/- Extensions and extendible maps -/

Require Import HoTT.Basics HoTT.Types.
Require Import HProp EquivalenceVarieties.
Require Import HoTT.Tactics.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

/- Given [C : B → Type] and [f : A → B], an extension of [g : Πa, C (f a)] along [f] is a section [h : Πb, C b] such that [h (f a) ≈ g a] for all [a:A].  This is equivalently the existence of fillers for commutative squares, restricted to the case where the bottom of the square is the identity; type-theoretically, this approach is sometimes more convenient.  In this file we study the type of such extensions.  One of its crucial properties is that a path between extensions is equivalently an extension in a fibration of paths.

This turns out to be useful for several reasons.  For instance, by iterating it, we can to formulate universal properties without needing [Funext].  It also gives us a way to "quantify" a universal property by the connectedness of the type of extensions. -/

section Extensions

  /- TODO: consider naming for [ExtensionAlong] and subsequent lemmas.  As a name for the type itself, [Extension] or [ExtensionAlong] seems great; but resultant lemma names such as [path_extension] (following existing naming conventions) are rather misleading. -/

  /- This elimination rule (and others) can be seen as saying that, given a fibration over the codomain and a section of it over the domain, there is some *extension* of this to a section over the whole domain.  It can also be considered as an equivalent form of an [hfiber] of precomposition-with-[f] that replaces paths by pointwise paths, thereby avoiding [Funext]. -/

  definition ExtensionAlong {A B : Type} (f : A → B)
             (P : B → Type) (d : Πx:A, P (f x)) :=
       Σs : Πy:B, P y, Πx:A, s (f x) ≈ d x .
  /- [ExtensionAlong] takes 5 universe parameters:
      - the size of A
      - the size of B
      - the size of P
      - >= max(B,P)
      - >= max(A,P).
    The following [Check] verifies that this is in fact the case. -/
  Check ExtensionAlong@{a b p m n}.
  /- If necessary, we could coalesce the latter two with a universe annotation, but that would make the definition harder to read. -/

  definition path_extension [H : Funext] {A B : Type} {f : A → B}
             {P : B → Type} {d : Πx:A, P (f x)}
             (ext ext' : ExtensionAlong f P d)
  : (ExtensionAlong f
                    (λy, dpr1 ext y ≈ dpr1 ext' y)
                    (λx, dpr2 ext x ⬝ (dpr2 ext' x)⁻¹))
    → ext ≈ ext'.
  /-begin
    /- Note: written with liberal use of [compose], to facilitate later proving that it’s an equivalance. -/
    apply (compose (path_sigma_uncurried _ _ _)).
    apply (functor_sigma (path_Π(ext .1) (ext' .1))). intros p.
    apply (compose (path_Π_ _)). unfold pointwise_paths.
    apply (functor_Πidmap). intros x.
    apply (compose (B := (p (f x))⁻¹ ⬝ (ext .2 x) ≈ (ext' .2 x))).
    apply concat.
    transitivity ((apD10 (path_Π_ _ p) (f x))⁻¹ ⬝ ext .2 x).
    assert (transp_extension : Πp : ext .1 ≈ ext' .1,
                                 (transport (λ(s : Πy : B, P y), Πx : A, s (f x) ≈ d x)
                                            p (ext .2) x
                                  ≈ ((apD10 p (f x))⁻¹ ⬝ ext .2 x))).
    destruct ext as [g gd], ext' as [g' gd']; simpl.
    intros q; destruct q; simpl.
    apply inverse, concat_1p.
    apply transp_extension.
    apply whiskerR, ap, apD10_path_forall.
    apply (compose (moveR_Vp _ _ _)).
    apply (compose (moveL_pM _ _ _)).
    exact inverse.
  end-/

  definition isequiv_path_extension [instance] [H : Funext] {A B : Type} {f : A → B}
         {P : B → Type} {d : Πx:A, P (f x)}
         (ext ext' : ExtensionAlong f P d)
  : IsEquiv (path_extension ext ext') | 0.
  /-begin
    apply @isequiv_compose.
    2: apply @isequiv_path_sigma.
    apply @isequiv_functor_sigma.
    apply @isequiv_path_forall.
    intros a. apply @isequiv_compose.
    2: apply @isequiv_path_forall.
    apply (@isequiv_functor_Π_).
    apply isequiv_idmap.
    intros x. apply @isequiv_compose.
    apply @isequiv_compose.
    apply @isequiv_compose.
    apply isequiv_path_inverse.
    apply isequiv_moveL_pM.
    apply isequiv_moveR_Vp.
    apply isequiv_concat_l.
  Qed.
  /- Note: opaque, since this term is big enough that using its computational content will probably be pretty intractable. -/

  /- Here is the iterated version. -/

  Fixpoint ExtendableAlong
           (n : nat) {A : Type@{i}} {B : Type@{j}}
           (f : A → B) (C : B → Type@{k}) : Type@{l} :=
       match n with
         | 0 => unit@{l}
         | S n => (Π(g : Πa, C (f a)),
                     ExtensionAlong@{i j k l l} f C g) *
                  Π(h k : Πb, C b),
                    ExtendableAlong n f (λb, h b ≈ k b)
       end.
  /- [ExtendableAlong] takes 4 universe parameters:
      - size of A
      - size of B
      - size of C
      - size of result (>= A,B,C) -/
  Check ExtendableAlong@{a b c r}.

  definition equiv_extendable_pathsplit [H : Funext] (n : nat)
             {A B : Type} (C : B → Type) (f : A → B)
  : ExtendableAlong n f C
    ≃ PathSplit n (λ(g : Πb, C b), g oD f).
  Proof.
    generalize dependent C; simple_induction n n IHn; intros C.
    1:apply equiv_idmap.
    apply equiv_functor_prod'; simpl.
    - refine (equiv_functor_forall' (equiv_idmap _) _); intros g; simpl.
      refine (equiv_functor_sigma' (equiv_idmap _) _); intros rec.
      apply equiv_path_forall.
    - refine (equiv_functor_forall' (equiv_idmap _) _); intros h.
      refine (equiv_functor_forall' (equiv_idmap _) _); intros k; simpl.
      refine (equiv_compose' _ (IHn (λb, h b ≈ k b))).
      apply equiv_inverse.
      refine (equiv_functor_pathsplit n _ _
               (equiv_apD10 _ _ _) (equiv_apD10 _ _ _) _).
      intros []; reflexivity.
  end-/

  definition isequiv_extendable [H : Funext] (n : nat)
             {A B : Type} {C : B → Type} {f : A → B}
  : ExtendableAlong n.+2 f C
    → IsEquiv (λg, g oD f) :=
       isequiv_pathsplit n ∘ (equiv_extendable_pathsplit n.+2 C f).

  definition ishprop_extendable [instance] [H : Funext] (n : nat)
         {A B : Type} (C : B → Type) (f : A → B)
  : is_hprop (ExtendableAlong n.+2 f C).
  /-begin
    refine (trunc_equiv' _ (equiv_inverse (equiv_extendable_pathsplit n.+2 C f))).
  end-/

  definition equiv_extendable_isequiv [H : Funext] (n : nat)
             {A B : Type} (C : B → Type) (f : A → B)
  : ExtendableAlong n.+2 f C
    ≃ IsEquiv (λ(g : Πb, C b), g oD f).
  /-begin
    etransitivity.
    - apply equiv_extendable_pathsplit.
    - apply equiv_pathsplit_isequiv.
  end-/

  /- Postcomposition with a known equivalence.  Note that this does not require funext to define, although showing that it is an equivalence would require funext. -/
  definition extendable_postcompose' (n : nat)
             {A B : Type} (C D : B → Type) (f : A → B)
             (g : Πb, C b ≃ D b)
  : ExtendableAlong n f C → ExtendableAlong n f D.
  /-begin
    generalize dependent C; revert D.
    simple_induction n n IH; intros C D g; simpl.
    1:apply idmap.
    refine (functor_prod _ _).
    - refine (functor_Π(functor_Πidmap
                                             (λa, (g (f a))⁻¹)) _);
      intros h; simpl.
      refine (functor_sigma (functor_Πidmap g) _); intros k.
      refine (functor_Πidmap _);
        intros a; unfold functor_arrow, functor_forall, composeD; simpl.
      apply moveR_equiv_M.
    - refine (functor_Π(functor_Πidmap (λb, (g b)⁻¹)) _);
      intros h.
      refine (functor_Π(functor_Πidmap (λb, (g b)⁻¹)) _);
        intros k; simpl; unfold functor_forall.
      refine (IH _ _ _); intros b.
      apply equiv_inverse, equiv_ap; exact _.
  end-/

  definition extendable_postcompose (n : nat)
             {A B : Type} (C D : B → Type) (f : A → B)
             (g : Πb, C b → D b) [H : Πb, IsEquiv (g b)]
  : ExtendableAlong n f C → ExtendableAlong n f D :=
       extendable_postcompose' n C D f (λb, BuildEquiv _ _ (g b) _).

  /- Composition of the maps we extend along.  This also does not require funext. -/
  definition extendable_compose (n : nat)
             {A B C : Type} (P : C → Type) (f : A → B) (g : B → C)
  : ExtendableAlong n g P → ExtendableAlong n f (λb, P (g b)) → ExtendableAlong n (g ∘ f) P.
  /-begin
    revert P; simple_induction n n IHn; intros P extg extf; [ exact star | split ].
    - intros h.
      exists ((fst extg (fst extf h).1).1); intros a.
      refine ((fst extg (fst extf h).1).2 (f a) ⬝ _).
      exact ((fst extf h).2 a).
    - intros h k.
      apply IHn.
      + exact (snd extg h k).
      + exact (snd extf (h oD g) (k oD g)).
  end-/

  /- And cancellation -/
  definition cancelL_extendable (n : nat)
             {A B C : Type} (P : C → Type) (f : A → B) (g : B → C)
  : ExtendableAlong n g P → ExtendableAlong n (g ∘ f) P → ExtendableAlong n f (λb, P (g b)).
  /-begin
    revert P; simple_induction n n IHn; intros P extg extgf; [ exact star | split ].
    - intros h.
      exists ((fst extgf h).1 oD g); intros a.
      exact ((fst extgf h).2 a).
    - intros h k.
      pose (h' := (fst extg h).1).
      pose (k' := (fst extg k).1).
      refine (extendable_postcompose' n (λb, h' (g b) ≈ k' (g b)) (λb, h b ≈ k b) f _ _).
      + intros b.
        exact (equiv_concat_lr ((fst extg h).2 b)⁻¹ ((fst extg k).2 b)).
      + apply (IHn (λc, h' c ≈ k' c) (snd extg h' k') (snd extgf h' k')).
  end-/

  definition cancelR_extendable (n : nat)
             {A B C : Type} (P : C → Type) (f : A → B) (g : B → C)
  : ExtendableAlong n.+1 f (λb, P (g b)) → ExtendableAlong n (g ∘ f) P → ExtendableAlong n g P.
  /-begin
    revert P; simple_induction n n IHn; intros P extf extgf; [ exact star | split ].
    - intros h.
      exists ((fst extgf (h oD f)).1); intros b.
      refine ((fst (snd extf ((fst extgf (h oD f)).1 oD g) h) _).1 b); intros a.
      apply ((fst extgf (h oD f)).2).
    - intros h k.
      apply IHn.
      + apply (snd extf (h oD g) (k oD g)).
      + apply (snd extgf h k).
  end-/

  /- And transfer across homotopies -/
  definition extendable_homotopic (n : nat)
             {A B : Type} (C : B → Type) (f : A → B) {g : A → B} (p : f == g)
  : ExtendableAlong n f C → ExtendableAlong n g C.
  /-begin
    revert C; simple_induction n n IHn; intros C extf; [ exact star | split ].
    - intros h.
      exists ((fst extf (λa, (p a)⁻¹ ▹ h a)).1); intros a.
      refine ((apD ((fst extf (λa, (p a)⁻¹ ▹ h a)).1) (p a))⁻¹ ⬝ _).
      apply moveR_transport_p.
      exact ((fst extf (λa, (p a)⁻¹ ▹ h a)).2 a).
    - intros h k.
      apply IHn, (snd extf h k).
  end-/

  /- We can extend along equivalences -/
  definition extendable_equiv (n : nat)
             {A B : Type} (C : B → Type) (f : A → B) [H : IsEquiv _ _ f]
  : ExtendableAlong n f C.
  /-begin
    revert C; simple_induction n n IHn; intros C; [ exact star | split ].
    - intros h.
      exists (λb, eisretr f b ▹ h (f⁻¹ b)); intros a.
      refine (transport2 C (eisadj f a) _ ⬝ _).
      refine ((transport_compose C f _ _)⁻¹ ⬝ _).
      exact (apD h (eissect f a)).
    - intros h k.
      apply IHn.
  end-/

  /- And into contractible types -/
  definition extendable_contr (n : nat)
             {A B : Type} (C : B → Type) (f : A → B)
             [H : Πb, is_contr (C b)]
  : ExtendableAlong n f C.
  /-begin
    generalize dependent C; simple_induction n n IHn;
      intros C ?; [ exact star | split ].
    - intros h.
      exists (λ_, center _); intros a.
      apply contr.
    - intros h k.
      apply IHn; exact _.
  end-/

  /- This is inherited by types of homotopies. -/
  definition extendable_homotopy (n : nat)
             {A B : Type} (C : B → Type) (f : A → B)
             (h k : Πb, C b)
  : ExtendableAlong n.+1 f C → ExtendableAlong n f (λb, h b ≈ k b).
  /-begin
    revert C h k; simple_induction n n IHn;
      intros C h k ext; [exact star | split].
    - intros p.
      exact (fst (snd ext h k) p).
    - intros p q.
      apply IHn, ext.
  end-/

  /- And the oo-version. -/

  definition ooExtendableAlong
             {A : Type@{i}} {B : Type@{j}}
             (f : A → B) (C : B → Type@{k}) : Type@{l} :=
       Πn, ExtendableAlong@{i j k l} n f C.
  /- Universe parameters are the same as for [ExtendableAlong]. -/
  Check ooExtendableAlong@{a b c r}.

  definition isequiv_ooextendable [H : Funext]
             {A B : Type} (C : B → Type) (f : A → B)
  : ooExtendableAlong f C → IsEquiv (λg, g oD f) :=
       λps, isequiv_extendable 0 (ps 2).

  definition equiv_ooextendable_pathsplit [H : Funext]
             {A B : Type} (C : B → Type) (f : A → B)
  : ooExtendableAlong f C ≃
    ooPathSplit (λ(g : Πb, C b), g oD f).
  /-begin
    refine (equiv_functor_forall' (equiv_idmap _) _); intros n.
    apply equiv_extendable_pathsplit.
  end-/

  definition ishprop_ooextendable [instance] [H : Funext]
         {A B : Type} (C : B → Type) (f : A → B)
  : is_hprop (ooExtendableAlong f C).
  /-begin
    refine (trunc_equiv _ (equiv_ooextendable_pathsplit C f)⁻¹).
  end-/

  definition equiv_ooextendable_isequiv [H : Funext]
             {A B : Type} (C : B → Type) (f : A → B)
  : ooExtendableAlong f C
    ≃ IsEquiv (λ(g : Πb, C b), g oD f).
  /-begin
    eapply equiv_compose'.
    - apply equiv_oopathsplit_isequiv.
    - apply equiv_ooextendable_pathsplit.
  end-/

  definition ooextendable_postcompose
             {A B : Type} (C D : B → Type) (f : A → B)
             (g : Πb, C b → D b) [H : Πb, IsEquiv (g b)]
  : ooExtendableAlong f C → ooExtendableAlong f D :=
       λppp n, extendable_postcompose n C D f g (ppp n).

  definition ooextendable_compose
             {A B C : Type} (P : C → Type) (f : A → B) (g : B → C)
  : ooExtendableAlong g P → ooExtendableAlong f (λb, P (g b)) → ooExtendableAlong (g ∘ f) P :=
       λextg extf n, extendable_compose n P f g (extg n) (extf n).

  definition cancelL_ooextendable
             {A B C : Type} (P : C → Type) (f : A → B) (g : B → C)
  : ooExtendableAlong g P → ooExtendableAlong (g ∘ f) P → ooExtendableAlong f (λb, P (g b)) :=
     λextg extgf n, cancelL_extendable n P f g (extg n) (extgf n).

  definition cancelR_ooextendable
             {A B C : Type} (P : C → Type) (f : A → B) (g : B → C)
  : ooExtendableAlong f (λb, P (g b)) → ooExtendableAlong (g ∘ f) P → ooExtendableAlong g P :=
       λextf extgf n, cancelR_extendable n P f g (extf n.+1) (extgf n).

  definition ooextendable_homotopic
             {A B : Type} (C : B → Type) (f : A → B) {g : A → B} (p : f == g)
  : ooExtendableAlong f C → ooExtendableAlong g C :=
       λextf n, extendable_homotopic n C f p (extf n).

  definition ooextendable_equiv
             {A B : Type} (C : B → Type) (f : A → B) [H : IsEquiv _ _ f]
  : ooExtendableAlong f C :=
     λn, extendable_equiv n C f.

  definition ooextendable_contr
             {A B : Type} (C : B → Type) (f : A → B)
             [H : Πb, is_contr (C b)]
  : ooExtendableAlong f C :=
     λn, extendable_contr n C f.

  definition ooextendable_homotopy
             {A B : Type} (C : B → Type) (f : A → B)
             (h k : Πb, C b)
  : ooExtendableAlong f C → ooExtendableAlong f (λb, h b ≈ k b).
  /-begin
    intros ext n; apply extendable_homotopy, ext.
  end-/

  /- Extendability of a family [C] along a map [f] can be detected by extendability of the constant family [C b] along the projection from the corresponding fiber of [f] to [unit].  Note that this is *not* an if-and-only-if; the hypothesis can be genuinely stronger than the conclusion. -/
  definition ooextendable_isnull_fibers {A B} (f : A → B) (C : B → Type)
  : (Πb, ooExtendableAlong (@const (hfiber f b) unit star)
                                 (λ_, C b))
    → ooExtendableAlong f C.
  /-begin
    intros orth n; revert C orth.
    induction n as [|n IHn]; intros C orth; [exact star | split].
    - intros g.
      exists (λb, (fst (orth b 1%nat) (λx, x.2 ▹ g x.1)).1 star).
      intros a.
      rewrite (path_unit star (const star a)).
      exact ((fst (orth (f a) 1%nat) _).2 ⟨a , 1⟩).
    - intros h k.
      apply IHn; intros b.
      apply ooextendable_homotopy, orth.
  end-/

End Extensions.
