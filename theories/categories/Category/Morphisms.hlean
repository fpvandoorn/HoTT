/- Definitions and theorems about {iso,epi,mono,}morphisms in a precategory -/
Require Import Category.Core Functor.Core.
Require Import HoTT.Tactics Types.Record Trunc HProp Types.Sigma Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

/- definition of isomorphism -/
Local Unset Primitive Projections. /- https://coq.inria.fr/bugs/show_bug.cgi?id=3624 -/
Class IsIsomorphism {C : PreCategory} {s d} (m : morphism C s d) :=
  {
    morphism_inverse : morphism C d s;
    left_inverse : morphism_inverse ∘ m = identity _;
    right_inverse : m ∘ morphism_inverse = identity _
  }.
Local Set Primitive Projections.

Arguments morphism_inverse {C s d} m {_}.

Local Notation "m ⁻¹" := (morphism_inverse m) (at level 3, format "m '⁻¹'") : morphism_scope.

Hint Resolve left_inverse right_inverse : category morphism.
Hint Rewrite @left_inverse @right_inverse : category.
Hint Rewrite @left_inverse @right_inverse : morphism.

Class Isomorphic {C : PreCategory} s d :=
  {
    morphism_isomorphic :> morphism C s d;
    isisomorphism_isomorphic :> IsIsomorphism morphism_isomorphic
  }.

(*Coercion Build_Isomorphic : IsIsomorphism >-> Isomorphic.*)
Coercion morphism_isomorphic : Isomorphic >-> morphism.
Coercion isisomorphism_isomorphic : Isomorphic >-> IsIsomorphism.

Local Infix "<~=~>" := Isomorphic (at level 70, no associativity) : category_scope.

Global Existing Instance isisomorphism_isomorphic.

/- Theorems about isomorphisms -/
section iso_contr
  Variable C : PreCategory.

  Local Open Scope equiv_scope.

  Variables s d : C.

  section IsIsomorphism
    Variable m : morphism C s d.

    /- The inverse of a morphism is unique -/
    definition inverse_unique (m_inv0 m_inv1 : morphism C d s)
          (left_inverse_0 : m_inv0 ∘ m = identity _)
          (right_inverse_1 : m ∘ m_inv1 = identity _)
    : m_inv0 = m_inv1.
    /-begin
      transitivity (m_inv0 ∘ m ∘ m_inv1);
      try solve [ by (rewrite → ?associativity; rewrite_hyp;
                      autorewrite with morphism)
                | by (rewrite <- ?associativity; rewrite_hyp;
                      autorewrite with morphism) ].
    Qed.

    Local Notation IsIsomorphism_sig_T :=
      { inverse : morphism C d s
      | { _ : inverse ∘ m = identity _
        | m ∘ inverse = identity _ } } (only parsing).

    /- Equivalence between the record and sigma versions of [IsIsomorphism] -/
    definition issig_isisomorphism
    : IsIsomorphism_sig_T ≃ IsIsomorphism m.
    Proof.
      issig (@Build_IsIsomorphism _ _ _ m)
            (@morphism_inverse _ _ _ m)
            (@left_inverse _ _ _ m)
            (@right_inverse _ _ _ m).
    end-/

    /- Being an isomorphism is a mere proposition -/
    definition trunc_isisomorphism [instance] : is_hprop (IsIsomorphism m).
    /-begin
      eapply trunc_equiv'; [ exact issig_isisomorphism | ].
      apply hprop_allpath.
      intros [x [? ?]] [y [? ?]].
      let H := fresh in
      assert (H : x = y) by ⟨apply inverse_unique, assumption⟩;
        destruct H.
      repeat match goal with
               | _ => progress simpl
               | _ => exact (center _)
               | _ => (exists refl)
               | _ => apply path_sigma_uncurried
             end.
    Qed.
  End IsIsomorphism.

  Local Notation Isomorphic_sig_T :=
    { m : morphism C s d
    | IsIsomorphism m } (only parsing).

  /- Equivalence between record and sigma versions of [Isomorphic] -/
  definition issig_isomorphic
  : Isomorphic_sig_T ≃ Isomorphic s d.
  Proof.
    issig (@Build_Isomorphic C s d)
          (@morphism_isomorphic C s d)
          (@isisomorphism_isomorphic C s d).
  end-/

  /- Isomorphisms form an hSet -/
  definition trunc_Isomorphic [instance] : IsHSet (Isomorphic s d).
  /-begin
    eapply trunc_equiv'; [ exact issig_isomorphic | ].
    typeclasses eauto.
  Qed.

  /- Equality between isomorphisms is determined by equality between their forward components -/
  definition path_isomorphic (i j : Isomorphic s d)
  : @morphism_isomorphic _ _ _ i = @morphism_isomorphic _ _ _ j
    → i = j.
  Proof.
    destruct i, j; simpl.
    intro; path_induction.
    f_ap.
    exact (center _).
  end-/

  /- Equality between isomorphisms is equivalent to by equality between their forward components -/
  Global Instance isequiv_path_isomorphic
  : is_equiv (path_isomorphic i j).
  /-begin
    intros.
    apply (isequiv_adjointify
             (path_isomorphic i j)
             (ap (@morphism_isomorphic _ _ _)));
      intro; [ destruct i | destruct i, j ];
      path_induction_hammer.
  end-/
End iso_contr.

section iso_equiv_relation
  Variable C : PreCategory.

  /- The identity is an isomorphism -/
  definition isisomorphism_identity [instance] (x : C) : IsIsomorphism (identity x) :=
       {| morphism_inverse := identity x;
          left_inverse := left_identity C x x (identity x);
          right_inverse := right_identity C x x (identity x) |}.

  /- Inverses of isomorphisms are isomorphisms -/
  definition isisomorphism_inverse `(@IsIsomorphism C x y m) : IsIsomorphism m⁻¹ :=
       {| morphism_inverse := m;
          left_inverse := right_inverse;
          right_inverse := left_inverse |}.

  Local Ltac iso_comp_t inv_lemma :=
    etransitivity; [ | apply inv_lemma ];
    instantiate;
    first [ rewrite → ?associativity; apply ap
          | rewrite <- ?associativity; apply ap ];
    first [ rewrite → ?associativity; rewrite inv_lemma
          | rewrite <- ?associativity; rewrite inv_lemma ];
    auto with morphism.

  /- Composition of isomorphisms gives an isomorphism -/
  definition isisomorphism_compose [instance] `(@IsIsomorphism C y z m0) `(@IsIsomorphism C x y m1)
  : IsIsomorphism (m0 ∘ m1).
  /-begin
    exists (m1⁻¹ ∘ m0⁻¹);
    [ abstract iso_comp_t @left_inverse
    | abstract iso_comp_t @right_inverse ].
  end-/

  Hint Immediate isisomorphism_inverse : typeclass_instances.

  /- Being isomorphic is a reflexive relation -/
  definition isomorphic_refl [instance] : Reflexive (@Isomorphic C) :=
       λx : C, {| morphism_isomorphic := identity x |}.

  /- Being isomorphic is a symmetric relation -/
  definition isomorphic_sym [instance] : Symmetric (@Isomorphic C) :=
       λx y X, {| morphism_isomorphic := X⁻¹ |}.

  /- Being isomorphic is a transitive relation -/
  definition isomorphic_trans [instance] : Transitive (@Isomorphic C) :=
       λx y z X Y, {| morphism_isomorphic := @morphism_isomorphic _ _ _ Y ∘ @morphism_isomorphic _ _ _ X |}.

  /- Equality gives rise to isomorphism -/
  definition idtoiso (x y : C) (H : x = y) : Isomorphic x y :=
       match H in (_ = y0) return (x <~=~> y0) with
         | 1%path => reflexivity x
       end.
End iso_equiv_relation.

Hint Immediate isisomorphism_inverse : typeclass_instances.

/- Epimorphisms and Monomorphisms -/
/- Quoting Wikipedia:

    In category theory, an epimorphism (also called an epic morphism
    or, colloquially, an epi) is a morphism [f : X → Y] which is
    right-cancellative in the sense that, for all morphisms [g, g' : Y
    → Z], [g ∘ f = g' ∘ f → g = g']

    Epimorphisms are analogues of surjective functions, but they are
    not exactly the same. The dual of an epimorphism is a monomorphism
    (i.e. an epimorphism in a category [C] is a monomorphism in the
    dual category [Cᵒᵖ]).  -/

Class IsEpimorphism {C} {x y} (m : morphism C x y) :=
  is_epimorphism : Πz (m1 m2 : morphism C y z),
                     m1 ∘ m = m2 ∘ m
                     → m1 = m2.
Class IsMonomorphism {C} {x y} (m : morphism C x y) :=
  is_monomorphism : Πz (m1 m2 : morphism C z x),
                      m ∘ m1 = m ∘ m2
                      → m1 = m2.

Record Epimorphism {C} x y :=
  {
    Epimorphism_morphism :> morphism C x y;
    Epimorphism_IsEpimorphism :> IsEpimorphism Epimorphism_morphism
  }.

Record Monomorphism {C} x y :=
  {
    Monomorphism_morphism :> morphism C x y;
    Monomorphism_IsMonomorphism :> IsMonomorphism Monomorphism_morphism
  }.

Global Existing Instances Epimorphism_IsEpimorphism Monomorphism_IsMonomorphism.

Local Notation "x ->> y" := (Epimorphism x y)
                              (at level 99, right associativity, y at level 200).
Local Notation "x (-> y" := (Monomorphism x y)
                              (at level 99, right associativity, y at level 200).

Class IsSectionOf C x y (s : morphism C x y) (r : morphism C y x) :=
     is_sect_morphism : r ∘ s = identity _.

Arguments IsSectionOf [C x y] s r.

section EpiMono
  Variable C : PreCategory.

  section properties
    /- The identity is an epimorphism -/
    definition isepimorphism_identity [instance] (x : C)
    : IsEpimorphism (identity x).
    /-begin
      repeat intro; autorewrite with morphism in *; trivial.
    Qed.

    /- The identity is a monomorphism -/
    definition ismonomorphism_identity [instance] (x : C)
    : IsMonomorphism (identity x).
    Proof.
      repeat intro; autorewrite with morphism in *; trivial.
    Qed.

    /- Composition of epimorphisms gives an epimorphism -/
    definition isepimorphism_compose [instance] s d d' m0 m1
    : IsEpimorphism m0
      → IsEpimorphism m1
      → IsEpimorphism (@compose C s d d' m0 m1).
    Proof.
      repeat intro.
      rewrite <- !associativity in *.
      apply_hyp.
    Qed.

    /- Composition of monomorphisms gives a monomorphism -/
    definition ismonomorphism_compose [instance] s d d' m0 m1
    : IsMonomorphism m0
      → IsMonomorphism m1
      → IsMonomorphism (@compose C s d d' m0 m1).
    Proof.
      repeat intro.
      rewrite !associativity in *.
      apply_hyp.
    Qed.
  End properties.

  /- Existence of {epi,mono}morphisms are a preorder -/
  section equiv
    definition reflexive_epimorphism [instance] : Reflexive (@Epimorphism C) :=
         λx, Build_Epimorphism (isepimorphism_identity x).

    definition reflexive_monomorphism [instance] : Reflexive (@Monomorphism C) :=
         λx, Build_Monomorphism (ismonomorphism_identity x).

    definition transitive_epimorphism [instance] : Transitive (@Epimorphism C) :=
         λ_ _ _ m0 m1, Build_Epimorphism (isepimorphism_compose m1 m0).

    definition transitive_monomorphism [instance] : Transitive (@Monomorphism C) :=
         λ_ _ _ m0 m1, Build_Monomorphism (ismonomorphism_compose m1 m0).
  End equiv.

  section sect
    Local Ltac epi_mono_sect_t :=
      let t :=
          (solve [ autorewrite with morphism;
                   reflexivity
                 | rewrite_hyp;
                   autorewrite with morphism;
                   reflexivity ]) in
      first [ rewrite → ?associativity; t
            | rewrite <- ?associativity; t].

    /- Retractions are epimorphisms -/
    definition isepimorphism_retr [instance] `(@IsSectionOf C x y s r)
    : IsEpimorphism r | 1000.
    Proof.
      (intros ? m1 m2 ?).
      unfold IsSectionOf in *.
      transitivity ((m1 ∘ r) ∘ s);
        [ | transitivity ((m2 ∘ r) ∘ s) ];
        epi_mono_sect_t.
    Qed.

    /- Sections are monomorphisms -/
    definition ismonomorphism_sect [instance] `(@IsSectionOf C x y s r)
    : IsMonomorphism s | 1000.
    Proof.
      (intros ? m1 m2 ?).
      transitivity (r ∘ (s ∘ m1));
        [ | transitivity (r ∘ (s ∘ m2)) ];
        epi_mono_sect_t.
    Qed.

    /- Isomorphisms are both sections and retractions -/
    definition issect_isisomorphism [instance] `(@IsIsomorphism C x y m)
    : IsSectionOf m m⁻¹ | 1000 :=
         left_inverse.

    definition isretr_isisomorphism [instance] `(@IsIsomorphism C x y m)
    : IsSectionOf m⁻¹ m | 1000 :=
         right_inverse.
  End sect.

  /- Isomorphisms are therefore epimorphisms and monomorphisms -/
  section iso
    definition isepimorphism_isisomorphism [instance] `(@IsIsomorphism C s d m)
    : IsEpimorphism m | 1000 :=
         _.
    definition ismonomorphism_isisomorphism [instance] `(@IsIsomorphism C s d m)
    : IsMonomorphism m | 1000 :=
         _.
  End iso.
End EpiMono.

Hint Immediate @isepimorphism_identity @ismonomorphism_identity @ismonomorphism_compose @isepimorphism_compose : category morphism.

/- Lemmas about [idtoiso] -/
section iso_lemmas
  Local Ltac idtoiso_t :=
    path_induction; simpl; autorewrite with morphism; reflexivity.

  /- [transport]ing across an equality of morphisms is the same as conjugating with [idtoiso] -/
  definition idtoiso_of_transport (C D : PreCategory) s d
        (m1 m2 : morphism C s d)
        (p : m1 = m2)
        (s' d' : morphism C s d → D) u
  : @transport _ (λm, morphism D (s' m) (d' m)) _ _ p u
    = idtoiso _ (ap d' p) ∘ u ∘ (idtoiso _ (ap s' p))⁻¹.
  Proof. idtoiso_t. Qed.

  /- [idtoiso] respects inverse -/
  definition idtoiso_inv (C : PreCategory) (s d : C) (p : s = d)
  : (idtoiso _ p)⁻¹ = idtoiso _ (p⁻¹)%path.
  Proof.
    path_induction; reflexivity.
  end-/

  /- [idtoiso] respects composition -/
  definition idtoiso_comp (C : PreCategory) (s d d' : C)
        (m1 : d = d') (m2 : s = d)
  : idtoiso _ m1 ∘ idtoiso _ m2 = idtoiso _ (m2 ⬝ m1)%path.
  /-begin idtoiso_t. Qed.

  /- These are useful when tactics are too slow and [rewrite] doesn't
      work. -/
  definition idtoiso_comp3 (C : PreCategory) (s d d' d'' : C)
        (m0 : d' = d'') (m1 : d = d') (m2 : s = d)
  : idtoiso _ m0 ∘ (idtoiso _ m1 ∘ idtoiso _ m2) = idtoiso _ ((m2 ⬝ m1) ⬝ m0)%path.
  Proof. idtoiso_t. Qed.

  definition idtoiso_comp3' (C : PreCategory) (s d d' d'' : C)
        (m0 : d' = d'') (m1 : d = d') (m2 : s = d)
  : (idtoiso _ m0 ∘ idtoiso _ m1) ∘ idtoiso _ m2 = idtoiso _ (m2 ⬝ (m1 ⬝ m0))%path.
  Proof. idtoiso_t. Qed.

  definition idtoiso_comp4 (C : PreCategory) (s d d' d'' d''' : C)
        (m0 : d'' = d''') (m1 : d' = d'') (m2 : d = d') (m3 : s = d)
  : idtoiso _ m0 ∘ (idtoiso _ m1 ∘ (idtoiso _ m2 ∘ idtoiso _ m3)) = idtoiso _ (((m3 ⬝ m2) ⬝ m1) ⬝ m0)%path.
  Proof. idtoiso_t. Qed.

  definition idtoiso_comp4' (C : PreCategory) (s d d' d'' d''' : C)
        (m0 : d'' = d''') (m1 : d' = d'') (m2 : d = d') (m3 : s = d)
  : ((idtoiso _ m0 ∘ idtoiso _ m1) ∘ idtoiso _ m2) ∘ idtoiso _ m3 = idtoiso _ (m3 ⬝ (m2 ⬝ (m1 ⬝ m0)))%path.
  Proof. idtoiso_t. Qed.

  definition idtoiso_comp5 (C : PreCategory) (s d d' d'' d''' d'''' : C)
        (m0 : d''' = d'''') (m1 : d'' = d''') (m2 : d' = d'') (m3 : d = d') (m4 : s = d)
  : idtoiso _ m0 ∘ (idtoiso _ m1 ∘ (idtoiso _ m2 ∘ (idtoiso _ m3 ∘ idtoiso _ m4)))
    = idtoiso _ ((((m4 ⬝ m3) ⬝ m2) ⬝ m1) ⬝ m0)%path.
  Proof. idtoiso_t. Qed.

  definition idtoiso_comp5' (C : PreCategory) (s d d' d'' d''' d'''' : C)
        (m0 : d''' = d'''') (m1 : d'' = d''') (m2 : d' = d'') (m3 : d = d') (m4 : s = d)
  : (((idtoiso _ m0 ∘ idtoiso _ m1) ∘ idtoiso _ m2) ∘ idtoiso _ m3) ∘ idtoiso _ m4
    = idtoiso _ (m4 ⬝ (m3 ⬝ (m2 ⬝ (m1 ⬝ m0))))%path.
  Proof. idtoiso_t. Qed.

  /- [idtoiso] respects application of functors on morphisms and objects -/
  definition idtoiso_functor (C D : PreCategory) (s d : C) (m : s = d)
        (F : Functor C D)
  : morphism_of F (idtoiso _ m) = idtoiso _ (ap (object_of F) m).
  Proof.
    path_induction; simpl; apply identity_of.
  end-/

  /- Functors preserve isomorphisms -/
  definition iso_functor [instance] C D (F : Functor C D) `(@IsIsomorphism C s d m)
  : IsIsomorphism (morphism_of F m) :=
       {| morphism_inverse := morphism_of F m⁻¹ |}.
  /-begin
    abstract (rewrite <- composition_of, ?left_inverse, ?right_inverse, identity_of; reflexivity).
    abstract (rewrite <- composition_of, ?left_inverse, ?right_inverse, identity_of; reflexivity).
  end-/
End iso_lemmas.

Hint Extern 1 (@IsIsomorphism _ _ _ (@morphism_of ?C ?D ?F ?s ?d ?m))
=> apply (@iso_functor C D F s d m) : typeclass_instances.

Hint Rewrite idtoiso_of_transport idtoiso_inv idtoiso_comp idtoiso_functor.

/- Lemmas about how to move isomorphisms around equalities, following [HoTT.PathGroupoids] -/
section iso_concat_lemmas
  Variable C : PreCategory.

  Local Ltac iso_concat_t' :=
    intros;
    repeat match goal with
             | [ H : ?x = ?y |- _ ] => atomic y; induction H
             | [ H : ?x = ?y |- _ ] => atomic x; apply symmetry.in H; induction H
           end;
    repeat first [ done
                 | rewrite → ?associativity;
                   progress rewrite ?left_identity, ?right_identity, ?left_inverse, ?right_inverse
                 | rewrite <- ?associativity;
                   progress rewrite ?left_identity, ?right_identity, ?left_inverse, ?right_inverse
                 | rewrite → ?associativity; progress f_ap; []
                 | rewrite <- ?associativity; progress f_ap; [] ].

  Local Ltac iso_concat_t_id_fin :=
    match goal with
      | [ |- context[@identity ?C ?x] ]
        => generalize dependent (identity x)
    end;
    iso_concat_t'.

  Local Ltac iso_concat_t_id lem :=
    first [ solve [
                etransitivity; [ | eapply lem ];
                iso_concat_t_id_fin
              ]
          | solve [
                etransitivity; [ apply symmetry. eapply lem | ];
                iso_concat_t_id_fin
          ] ].

  Local Ltac iso_concat_t :=
    iso_concat_t';
    try first [ solve [ iso_concat_t_id @left_identity ]
              | solve [ iso_concat_t_id @right_identity ] ].

  definition iso_compose_pV `(@IsIsomorphism C x y p)
  : p ∘ p⁻¹ = identity _ :=
       right_inverse.
  definition iso_compose_Vp `(@IsIsomorphism C x y p)
  : p⁻¹ ∘ p = identity _ :=
       left_inverse.

  definition iso_compose_V_pp `(@IsIsomorphism C y z p) `(q : morphism C x y)
  : p⁻¹ ∘ (p ∘ q) = q.
  Proof. iso_concat_t. Qed.

  definition iso_compose_p_Vp `(@IsIsomorphism C x z p) `(q : morphism C y z)
  : p ∘ (p⁻¹ ∘ q) = q.
  Proof. iso_concat_t. Qed.

  definition iso_compose_pp_V `(p : morphism C y z) `(@IsIsomorphism C x y q)
  : (p ∘ q) ∘ q⁻¹ = p.
  Proof. iso_concat_t. Qed.

  definition iso_compose_pV_p `(p : morphism C x z) `(@IsIsomorphism C x y q)
  : (p ∘ q⁻¹) ∘ q = p.
  Proof. iso_concat_t. Qed.

  definition iso_inv_pp `(@IsIsomorphism C y z p) `(@IsIsomorphism C x y q)
  : (p ∘ q)⁻¹ = q⁻¹ ∘ p⁻¹.
  Proof. iso_concat_t. Qed.

  definition iso_inv_Vp `(@IsIsomorphism C y z p) `(@IsIsomorphism C x z q)
  : (p⁻¹ ∘ q)⁻¹ = q⁻¹ ∘ p.
  Proof. iso_concat_t. Qed.

  definition iso_inv_pV `(@IsIsomorphism C x y p) `(@IsIsomorphism C x z q)
  : (p ∘ q⁻¹)⁻¹ = q ∘ p⁻¹.
  Proof. iso_concat_t. Qed.

  definition iso_inv_VV `(@IsIsomorphism C x y p) `(@IsIsomorphism C y z q)
  : (p⁻¹ ∘ q⁻¹)⁻¹ = q ∘ p.
  Proof. iso_concat_t. Qed.

  definition iso_moveR_Mp `(p : morphism C x y) `(q : morphism C x z) `(@IsIsomorphism C y z r)
  : p = (r⁻¹ ∘ q) → (r ∘ p) = q.
  Proof. iso_concat_t. Qed.

  definition iso_moveR_pM `(@IsIsomorphism C x y p) `(q : morphism C x z) `(r : morphism C y z)
  : r = (q ∘ p⁻¹) → (r ∘ p) = q.
  Proof. iso_concat_t. Qed.

  definition iso_moveR_Vp `(p : morphism C x y) `(q : morphism C x z) `(@IsIsomorphism C z y r)
  : p = (r ∘ q) → (r⁻¹ ∘ p) = q.
  Proof. iso_concat_t. Qed.

  definition iso_moveR_pV `(@IsIsomorphism C x y p) `(q : morphism C y z) `(r : morphism C x z)
  : r = (q ∘ p) → (r ∘ p⁻¹) = q.
  Proof. iso_concat_t. Qed.

  definition iso_moveL_Mp `(p : morphism C x y) `(q : morphism C x z) `(@IsIsomorphism C y z r)
  : (r⁻¹ ∘ q) = p → q = (r ∘ p).
  Proof. iso_concat_t. Qed.

  definition iso_moveL_pM `(@IsIsomorphism C x y p) `(q : morphism C x z) `(r : morphism C y z)
  : (q ∘ p⁻¹) = r → q = (r ∘ p).
  Proof. iso_concat_t. Qed.

  definition iso_moveL_Vp `(p : morphism C x y) `(q : morphism C x z) `(@IsIsomorphism C _ _ r)
  : (r ∘ q) = p → q = (r⁻¹ ∘ p).
  Proof. iso_concat_t. Qed.

  definition iso_moveL_pV `(@IsIsomorphism C x y p) `(q : morphism C y z) r
  : (q ∘ p) = r → q = (r ∘ p⁻¹).
  Proof. iso_concat_t. Qed.

  definition iso_moveL_1M `(p : morphism C x y) `(@IsIsomorphism C x y q)
  : p ∘ q⁻¹ = identity _ → p = q.
  Proof. iso_concat_t. Qed.

  definition iso_moveL_M1 `(p : morphism C x y) `(@IsIsomorphism C x y q)
  : q⁻¹ ∘ p = identity _ → p = q.
  Proof. iso_concat_t. Qed.

  definition iso_moveL_1V `(p : morphism C x y) `(@IsIsomorphism C y x q)
  : p ∘ q = identity _ → p = q⁻¹.
  Proof. iso_concat_t. Qed.

  definition iso_moveL_V1 `(p : morphism C x y) `(@IsIsomorphism C y x q)
  : q ∘ p = identity _ → p = q⁻¹.
  Proof. iso_concat_t. Qed.

  definition iso_moveR_M1 `(@IsIsomorphism C x y p) q
  : identity _ = p⁻¹ ∘ q → p = q.
  Proof. iso_concat_t. Qed.

  definition iso_moveR_1M `(@IsIsomorphism C x y p) q
  : identity _ = q ∘ p⁻¹ → p = q.
  Proof. iso_concat_t. Qed.

  definition iso_moveR_1V `(@IsIsomorphism C x y p) q
  : identity _ = q ∘ p → p⁻¹ = q.
  Proof. iso_concat_t. Qed.

  definition iso_moveR_V1 `(@IsIsomorphism C x y p) q
  : identity _ = p ∘ q → p⁻¹ = q.
  Proof. iso_concat_t. Qed.
End iso_concat_lemmas.

/- Tactics for moving inverses around -/
Ltac iso_move_inverse' :=
  match goal with
    | [ |- _⁻¹ ∘ _ = _ ] => apply iso_moveR_Vp
    | [ |- _ = _⁻¹ ∘ _ ] => apply iso_moveL_Vp
    | [ |- _ ∘ _⁻¹ = _ ] => apply iso_moveR_pV
    | [ |- _ = _ ∘ _⁻¹ ] => apply iso_moveL_pV
    | [ |- _ ∘ (_ ∘ _⁻¹) = _ ] => rewrite <- associativity
    | [ |- _ = _ ∘ (_ ∘ _⁻¹) ] => rewrite <- associativity
    | [ |- (_⁻¹ ∘ _) ∘ _ = _ ] => rewrite → associativity
    | [ |- _ = (_⁻¹ ∘ _) ∘ _ ] => rewrite → associativity
  end.

Ltac iso_move_inverse := progress repeat iso_move_inverse'.

/- Tactics for collapsing [p ∘ p⁻¹] and [p⁻¹ ∘ p] -/
/- Now the tactics for collapsing [p ∘ p⁻¹] (and [p⁻¹ ∘ p]) in the
    middle of a chain of compositions of isomorphisms. -/

Ltac iso_collapse_inverse_left' :=
  first [ apply ap
        | progress rewrite ?iso_compose_p_Vp, ?iso_compose_V_pp ].

Ltac iso_collapse_inverse_left :=
  rewrite → ?Category.Core.associativity;
  progress repeat iso_collapse_inverse_left'.

Ltac iso_collapse_inverse_right' :=
  first [ apply ap10; apply ap
        | progress rewrite ?iso_compose_pV_p, ?iso_compose_pp_V ].

Ltac iso_collapse_inverse_right :=
  rewrite <- ?Category.Core.associativity;
  progress repeat iso_collapse_inverse_right'.

Ltac iso_collapse_inverse :=
  progress repeat first [ iso_collapse_inverse_left
                        | iso_collapse_inverse_right ].

section associativity_composition
  Variable C : PreCategory.
  Variables x0 x1 x2 x3 x4 : C.

  /- This lemma is helpful for backwards reasoning. -/
  definition compose4associativity_helper
    (a : morphism C x3 x4) (b : morphism C x2 x3)
    (c : morphism C x1 x2) (d : morphism C x0 x1)
  : a ∘ b ∘ c ∘ d = (a ∘ ((b ∘ c) ∘ d)).
  Proof.
    rewrite !associativity; reflexivity.
  Qed.
End associativity_composition.

Module Export CategoryMorphismsNotations.
  Notation "m ⁻¹" := (morphism_inverse m) (at level 3, format "m '⁻¹'") : morphism_scope.

  Infix "<~=~>" := Isomorphic (at level 70, no associativity) : category_scope.

  Notation "x ->> y" := (Epimorphism x y)
                          (at level 99, right associativity, y at level 200).
  Notation "x (-> y" := (Monomorphism x y)
                          (at level 99, right associativity, y at level 200).
End CategoryMorphismsNotations.
