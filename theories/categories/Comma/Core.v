/- Comma categories -/
Require Import Category.Core Functor.Core.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors.
Require Functor.Identity.
Require Import Category.Strict.
Require Import Types.Record Types.Paths Types.Sigma Trunc HoTT.Tactics HProp.
Import Functor.Identity.FunctorIdentityNotations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

/- Quoting Wikipedia:

    Suppose that [A], [B], and [C] are categories, and [S] and [T] are
    functors

    [S : A → C ← B : T]

    We can form the comma category [(S ↓ T)] as follows:

    - The objects are all triples [(α, β, f)] with [α] an object in
      [A], [β] an object in [B], and [f : S α → T β] a morphism in
      [C].

    - The morphisms from [(α, β, f)] to [(α', β', f')] are all pairs
      [(g, h)] where [g : α → α'] and [h : β → β'] are morphisms in
      [A] and [B] respectively, such that the following diagram
      commutes:

<<
             S g
        S α -----> S α'
         |          |
       f |          | f'
         |          |
         ↓          ↓
        T β -----> T β'
             T h
>>

    Morphisms are composed by taking [(g, h) ∘ (g', h')] to be [(g ∘
    g', h ∘ h')], whenever the latter expression is defined.  The
    identity morphism on an object [(α, β, f)] is [(1_α, 1_β)].  -/

/- Comma category [(S / T)] -/
Module Import CommaCategory.
  section comma_category_parts
    Variable A : PreCategory.
    Variable B : PreCategory.
    Variable C : PreCategory.
    Variable S : Functor A C.
    Variable T : Functor B C.

    Record object :=
      {
        a : A;
        b : B;
        f : morphism C (S a) (T b)
      }.

    Global Arguments a _ / .
    Global Arguments b _ / .
    Global Arguments f _ / .

    Local Notation object_sig_T :=
      ({ a : A
       | { b : B
         | morphism C (S a) (T b) }}).

    definition issig_object
    : object_sig_T ≃ object.
    /-begin
      issig (@Build_object)
            (@a)
            (@b)
            (@f).
    end-/

    definition trunc_object [instance] [H : is_trunc n A, is_trunc n B]
           [H : Πs d, is_trunc n (morphism C s d)]
    : is_trunc n object.
    /-begin
      eapply trunc_equiv';
      [ exact issig_object | ].
      typeclasses eauto.
    Qed.

    definition path_object' (x y : object)
    : Π(Ha : x.(a) ≈ y.(a))
             (Hb : x.(b) ≈ y.(b)),
        transport (λX, morphism C (S X) _)
                  Ha
                  (transport (λY, morphism C _ (T Y))
                             Hb
                             x.(f))
        ≈ y.(f)
        → x ≈ y.
    Proof.
      destruct x, y; simpl.
      intros; path_induction; reflexivity.
    end-/

    definition ap_a_path_object' x y Ha Hb Hf
    : ap (@a) (@path_object' x y Ha Hb Hf) ≈ Ha.
    /-begin
      destruct x, y; simpl in *.
      destruct Ha, Hb, Hf; simpl in *.
      reflexivity.
    Qed.

    definition ap_b_path_object' x y Ha Hb Hf
    : ap (@b) (@path_object' x y Ha Hb Hf) ≈ Hb.
    Proof.
      destruct x, y; simpl in *.
      destruct Ha, Hb, Hf; simpl in *.
      reflexivity.
    Qed.

    Global Arguments path_object' : simpl never.

    Record morphism (abf a'b'f' : object) :=
      Build_morphism' {
          g : Category.Core.morphism A (abf.(a)) (a'b'f'.(a));
          h : Category.Core.morphism B (abf.(b)) (a'b'f'.(b));
          p : T _1 h ∘ abf.(f) ≈ a'b'f'.(f) ∘ S _1 g;
          p_sym : a'b'f'.(f) ∘ S _1 g ≈ T _1 h ∘ abf.(f)
        }.

    definition Build_morphism abf a'b'f' g h p : morphism abf a'b'f' :=
         @Build_morphism' abf a'b'f' g h p p⁻¹.

    Global Arguments Build_morphism / .
    Global Arguments g _ _ _ / .
    Global Arguments h _ _ _ / .
    Global Arguments p _ _ _ / .
    Global Arguments p_sym _ _ _ / .

    Local Notation morphism_sig_T abf a'b'f' :=
      ({ g : Category.Core.morphism A (abf.(a)) (a'b'f'.(a))
       | { h : Category.Core.morphism B (abf.(b)) (a'b'f'.(b))
         | T _1 h ∘ abf.(f) ≈ a'b'f'.(f) ∘ S _1 g }}).

    Local Notation morphism_sig_T' abf a'b'f' :=
      ({ g : Category.Core.morphism A (abf.(a)) (a'b'f'.(a))
       | { h : Category.Core.morphism B (abf.(b)) (a'b'f'.(b))
         | { _ : T _1 h ∘ abf.(f) ≈ a'b'f'.(f) ∘ S _1 g
           | a'b'f'.(f) ∘ S _1 g ≈ T _1 h ∘ abf.(f) }}}).

    definition issig_morphism' abf a'b'f'
    : (morphism_sig_T' abf a'b'f')
        ≃ morphism abf a'b'f'.
    Proof.
      issig (@Build_morphism' abf a'b'f')
            (@g abf a'b'f')
            (@h abf a'b'f')
            (@p abf a'b'f')
            (@p_sym abf a'b'f').
    end-/

    definition issig_morphism_helper {T0} [H : IsHSet T0] (a b : T0) (pf : a ≈ b)
    : is_contr (b ≈ a).
    /-begin
      destruct pf.
      apply contr_inhabited_hprop; try reflexivity.
      typeclasses eauto.
    Qed.


    definition issig_morphism abf a'b'f'
    : (morphism_sig_T abf a'b'f')
        ≃ morphism abf a'b'f'.
    Proof.
      etransitivity; [ | exact (issig_morphism' abf a'b'f') ].
      repeat (apply equiv_functor_sigma_id; intro).
      symmetry; apply equiv_sigma_contr; intro.
      apply issig_morphism_helper; assumption.
    end-/

    definition trunc_morphism [instance] abf a'b'f'
           [H : is_trunc n (Category.Core.morphism A (abf.(a)) (a'b'f'.(a)))]
           [H : is_trunc n (Category.Core.morphism B (abf.(b)) (a'b'f'.(b)))]
           [H : Πm1 m2,
               is_trunc n (T _1 m2 ∘ abf.(f) ≈ a'b'f'.(f) ∘ S _1 m1)]
    : is_trunc n (morphism abf a'b'f').
    /-begin
      assert (Πm1 m2,
                is_trunc n (a'b'f'.(f) ∘ S _1 m1 ≈ T _1 m2 ∘ abf.(f)))
        by (intros; apply (trunc_equiv _ inverse)).
      eapply trunc_equiv';
      [ exact (issig_morphism _ _) | ].
      typeclasses eauto.
    Qed.

    definition path_morphism abf a'b'f'
          (gh g'h' : morphism abf a'b'f')
    : gh.(g) ≈ g'h'.(g)
      → gh.(h) ≈ g'h'.(h)
      → gh ≈ g'h'.
    Proof.
      destruct gh, g'h'; simpl.
      intros; path_induction.
      f_ap.
      all:exact (center _).
    Qed.

    definition compose s d d'
               (gh : morphism d d') (g'h' : morphism s d)
    : morphism s d' :=
         Build_morphism'
           s d'
           (gh.(g) ∘ g'h'.(g))
           (gh.(h) ∘ g'h'.(h))
           ((ap (λm, m ∘ s.(f)) (composition_of T _ _ _ _ _))
              ⬝ (associativity _ _ _ _ _ _ _ _)
              ⬝ (ap (λm, _ ∘ m) g'h'.(p))
              ⬝ (associativity_sym _ _ _ _ _ _ _ _)
              ⬝ (ap (λm, m ∘ _) gh.(p))
              ⬝ (associativity _ _ _ _ _ _ _ _)
              ⬝ (ap (λm, d'.(f) ∘ m) (composition_of S _ _ _ _ _)⁻¹))%path
           ((ap (λm, d'.(f) ∘ m) (composition_of S _ _ _ _ _))
              ⬝ (associativity_sym _ _ _ _ _ _ _ _)
              ⬝ (ap (λm, m ∘ _) gh.(p_sym))
              ⬝ (associativity _ _ _ _ _ _ _ _)
              ⬝ (ap (λm, _ ∘ m) g'h'.(p_sym))
              ⬝ (associativity_sym _ _ _ _ _ _ _ _)
              ⬝ (ap (λm, m ∘ s.(f)) (composition_of T _ _ _ _ _)⁻¹))%path.

    Global Arguments compose _ _ _ _ _ / .

    definition identity x : morphism x x :=
         Build_morphism'
           x x
           (identity (x.(a)))
           (identity (x.(b)))
           ((ap (λm, m ∘ x.(f)) (identity_of T _))
              ⬝ (left_identity _ _ _ _)
              ⬝ ((right_identity _ _ _ _)⁻¹)
              ⬝ (ap (λm, x.(f) ∘ m) (identity_of S _)⁻¹))
           ((ap (λm, x.(f) ∘ m) (identity_of S _))
              ⬝ (right_identity _ _ _ _)
              ⬝ ((left_identity _ _ _ _)⁻¹)
              ⬝ (ap (λm, m ∘ x.(f)) (identity_of T _)⁻¹)).

    Global Arguments identity _ / .
  End comma_category_parts.
End CommaCategory.

Global Arguments CommaCategory.path_object' : simpl never.

Local Ltac path_comma_t :=
  intros;
  apply path_morphism;
  simpl;
  auto with morphism.

definition comma_category A B C (S : Functor A C) (T : Functor B C)
: PreCategory.
Proof.
  refine (@Build_PreCategory
            (@object _ _ _ S T)
            (@morphism _ _ _ S T)
            (@identity _ _ _ S T)
            (@compose _ _ _ S T)
            _
            _
            _
            _
         );
  abstract path_comma_t.
end-/

definition isstrict_comma_category [instance] A B C S T
       [H : IsStrictCategory A, IsStrictCategory B]
: IsStrictCategory (@comma_category A B C S T).
Proof.
  typeclasses eauto.
Qed.

/- section category
    Context [H : IsCategory A, IsCategory B].
    (*Context [H : Funext]. -/

    definition comma_category_isotoid (x y : comma_category)
    : x ≅ y → x ≈ y.
    Proof.
      intro i.
      destruct i as [i [i' ? ?]].
      hnf in *.
      destruct i, i'.
      simpl in *.


    definition comma_category_IsCategory [instance] [H : IsCategory A, IsCategory B]
    : IsCategory comma_category.
    Proof.
      hnf.
      unfold IsStrictCategory in *.
      typeclasses eauto.
    Qed.
  End category.
*)

Hint Unfold compose identity : category.
Hint Constructors morphism object : category.

/- (co)slice category [(a / F)], [(F / a)] -/
section slice_category
  Variable A : PreCategory.
  Variable C : PreCategory.
  Variable a : C.
  Variable S : Functor A C.

  definition slice_category := comma_category S (!a).
  definition coslice_category := comma_category (!a) S.

  /- [x ↓ F] is a coslice category; [F ↓ x] is a slice category; [x ↓ F] deals with morphisms [x → F y]; [F ↓ x] has morphisms [F y → x] -/
End slice_category.

/- (co)slice category over [(a / C)], [(C / a)] -/
section slice_category_over
  Variable C : PreCategory.
  Variable a : C.

  definition slice_category_over := slice_category a (Functor.Identity.identity C).
  definition coslice_category_over := coslice_category a (Functor.Identity.identity C).
End slice_category_over.

/- category of arrows -/
section arrow_category
  Variable C : PreCategory.

  definition arrow_category := comma_category (Functor.Identity.identity C) (Functor.Identity.identity C).
End arrow_category.

definition CC_Functor' (C : PreCategory) (D : PreCategory) := Functor C D.
Coercion cc_functor_from_terminal' (C : PreCategory) (x : C) : CC_Functor' _ C :=
     (!x)%functor.
Coercion cc_identity_functor' (C : PreCategory) : CC_Functor' C C :=
     1%functor.
Global Arguments CC_Functor' / .
Global Arguments cc_functor_from_terminal' / .
Global Arguments cc_identity_functor' / .

Module Export CommaCoreNotations.
  /- We really want to use infix [↓] for comma categories, but that's unicode.  Infix [,] might also be reasonable, but I can't seem to get it to work without destroying the [(_, _)] notation for ordered pairs.  So I settle for the ugly ASCII rendition [/] of [↓]. -/
  /- Set some notations for printing -/
  Notation "C / a" := (@slice_category_over C a) : category_scope.
  Notation "a \ C" := (@coslice_category_over C a) (at level 40, left associativity) : category_scope.
  Notation "a / C" := (@coslice_category_over C a) : category_scope.
  Notation "x / F" := (coslice_category x F) : category_scope.
  Notation "F / x" := (slice_category x F) : category_scope.
  Notation "S / T" := (comma_category S T) : category_scope.
  /- Set the notation for parsing; coercions will automatically decide which of the arguments are functors and which are objects, i.e., functors from the terminal category. -/
  Notation "S / T" := (comma_category (S : CC_Functor' _ _)
                                      (T : CC_Functor' _ _)) : category_scope.
End CommaCoreNotations.
