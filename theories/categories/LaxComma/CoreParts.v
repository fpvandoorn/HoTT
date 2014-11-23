Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Functor.Identity.
Require Import Functor.Composition.Core.
Require Import NaturalTransformation.Paths NaturalTransformation.Composition.Core.
Require Import Category.Morphisms FunctorCategory.Core.
Require Import Pseudofunctor.Core.
Require Import NaturalTransformation.Composition.Laws.
Require Import FunctorCategory.Morphisms.
Require Import Types.Record Trunc Types.Paths Types.Sigma.

Import Functor.Identity.FunctorIdentityNotations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

/- Quoting David Spivak:

    David: ok
       so an object of [FC ⇓ D] is a pair [(X, G)], where [X] is a
       finite category (or a small category or whatever you wanted)
       and [G : X --> D] is a functor.
       a morphism in [FC ⇓ D] is a ``natural transformation diagram''
       (as opposed to a commutative diagram, in which the natural
       transformation would be ``identity'')
       so a map in [FC ⇓ D] from [(X, G)] to [(X', G')] is a pair
       [(F, α)] where [F : X --> X'] is a functor and
       [α : G --> G' ∘ F] is a natural transformation
       and the punchline is that there is a functor
       [colim : FC ⇓ D --> D]

     David: consider for yourself the case where [F : X --> X'] is
       identity ([X ≈ X']) and (separately) the case where
       [α : G --> G ∘ F] is identity.
       the point is, you've already done the work to get this colim
       functor.
       because every map in [FC ⇓ D] can be written as a composition
       of two maps, one where the [F]-part is identity and one where
       the [α]-part is identity.
       and you've worked both of those cases out already.
       -/

Module Import LaxCommaCategoryParts.
  section lax_comma_category_parts
    Context [H : Funext].
    Variable A : PreCategory.
    Variable B : PreCategory.

    Variable S : Pseudofunctor A.
    Variable T : Pseudofunctor B.

    Context [H : Πa b, IsHSet (Functor (S a) (T b))].

    Record object :=
      {
        a : A;
        b : B;
        f : Functor (S a) (T b)
      }.

    Local Notation object_sig_T :=
      ({ a : A
       | { b : B
         | Functor (S a) (T b) }}).

    definition issig_object
    : object_sig_T ≃ object.
    /-begin
      issig (@Build_object)
            (@a)
            (@b)
            (@f).
    end-/

    definition trunc_object [instance] [H : is_trunc n A, is_trunc n B]
           [H : Πs d, is_trunc n (Functor (S s) (T d))]
    : is_trunc n object.
    /-begin
      eapply trunc_equiv';
      [ exact issig_object | ].
      typeclasses eauto.
    Qed.

    definition path_object (x y : object)
    : Π(Ha : x.(a) ≈ y.(a))
             (Hb : x.(b) ≈ y.(b)),
        match Ha in _ ≈ X, Hb in _ ≈ Y return Functor (S X) (T Y) with
          | idpath, idpath => x.(f)
        end ≈ y.(f)
        → x ≈ y.
    Proof.
      destruct x, y; simpl.
      intros; path_induction; reflexivity.
    end-/

    definition path_object_uncurried x y
               (H : { HaHb : (x.(a) ≈ y.(a)) × (x.(b) ≈ y.(b))
                    | match pr1 HaHb in _ ≈ X, pr2 HaHb in _ ≈ Y return Functor (S X) (T Y) with
                        | idpath, idpath => x.(f)
                      end ≈ y.(f) })
    : x ≈ y :=
         @path_object x y (pr1 H.1) (pr2 H.1) H.2.

    definition ap_a_path_object x y Ha Hb Hf
    : ap (@a) (@path_object x y Ha Hb Hf) ≈ Ha.
    /-begin
      destruct x, y; simpl in *.
      destruct Ha, Hb, Hf; simpl in *.
      reflexivity.
    Qed.

    definition ap_b_path_object x y Ha Hb Hf
    : ap (@b) (@path_object x y Ha Hb Hf) ≈ Hb.
    Proof.
      destruct x, y; simpl in *.
      destruct Ha, Hb, Hf; simpl in *.
      reflexivity.
    Qed.

    Global Opaque path_object.

    Record morphism (abf a'b'f' : object) :=
      {
        g : Category.Core.morphism A (abf.(a)) (a'b'f'.(a));
        h : Category.Core.morphism B (abf.(b)) (a'b'f'.(b));
        p : NaturalTransformation (p_morphism_of T h ∘ abf.(f))
                                  (a'b'f'.(f) ∘ p_morphism_of S g)
      }.

    Local Notation morphism_sig_T abf a'b'f' :=
      ({ g : Category.Core.morphism A (abf.(a)) (a'b'f'.(a))
       | { h : Category.Core.morphism B (abf.(b)) (a'b'f'.(b))
         | NaturalTransformation (p_morphism_of T h ∘ abf.(f))
                                 (a'b'f'.(f) ∘ p_morphism_of S g) }}).

    definition issig_morphism abf a'b'f'
    : (morphism_sig_T abf a'b'f')
        ≃ morphism abf a'b'f'.
    Proof.
      issig (@Build_morphism abf a'b'f')
            (@g abf a'b'f')
            (@h abf a'b'f')
            (@p abf a'b'f').
    end-/

    definition trunc_morphism [instance] abf a'b'f'
           [H : is_trunc n (Category.Core.morphism A (abf.(a)) (a'b'f'.(a)))]
           [H : is_trunc n (Category.Core.morphism B (abf.(b)) (a'b'f'.(b)))]
           [H : Πm1 m2,
               is_trunc n (NaturalTransformation
                            (p_morphism_of T m2 ∘ abf.(f))
                            (a'b'f'.(f) ∘ p_morphism_of S m1))]
    : is_trunc n (morphism abf a'b'f').
    /-begin
      eapply trunc_equiv';
      [ exact (issig_morphism _ _) | ].
      typeclasses eauto.
    Qed.

    definition path_morphism abf a'b'f'
          (gh g'h' : morphism abf a'b'f')
    : forall
        (Hg : gh.(g) ≈ g'h'.(g))
        (Hh : gh.(h) ≈ g'h'.(h)),
        match Hg in _ ≈ g, Hh in _ ≈ h
              return NaturalTransformation
                       (p_morphism_of T h ∘ abf.(f))
                       (a'b'f'.(f) ∘ p_morphism_of S g)
        with
          | idpath, idpath => gh.(p)
        end ≈ g'h'.(p)
         → gh ≈ g'h'.
    Proof.
      intros Hg Hh Hp.
      destruct gh, g'h'; simpl in *.
      destruct Hg, Hh, Hp.
      reflexivity.
    Qed.

    definition path_morphism_uncurried abf a'b'f' gh g'h'
               (H : { HgHh : (gh.(g) ≈ g'h'.(g)) × (gh.(h) ≈ g'h'.(h))
                    | match pr1 HgHh in _ ≈ g, pr2 HgHh in _ ≈ h
                            return NaturalTransformation
                                     (p_morphism_of T h ∘ abf.(f))
                                     (a'b'f'.(f) ∘ p_morphism_of S g)
                      with
                        | idpath, idpath => gh.(p)
                      end ≈ g'h'.(p) })
    : gh ≈ g'h' :=
         @path_morphism abf a'b'f' gh g'h' (pr1 H.1) (pr2 H.1) H.2.

    definition path_morphism'_helper abf a'b'f'
          (gh g'h' : morphism abf a'b'f')
    : forall
        (Hg : gh.(g) ≈ g'h'.(g))
        (Hh : gh.(h) ≈ g'h'.(h)),
        ((_ oL (Category.Morphisms.idtoiso (_ → _) (ap (@p_morphism_of _ _ S _ _) Hg) : Category.Core.morphism _ _ _))
           ∘ (gh.(p))
           ∘ ((Category.Morphisms.idtoiso (_ → _) (ap (@p_morphism_of _ _ T _ _) Hh) : Category.Core.morphism _ _ _)⁻¹ oR _)
         ≈ g'h'.(p))%natural_transformation
        → match Hg in _ ≈ g, Hh in _ ≈ h
                 return NaturalTransformation
                          (p_morphism_of T h ∘ abf.(f))
                          (a'b'f'.(f) ∘ p_morphism_of S g)
           with
             | idpath, idpath => gh.(p)
           end ≈ g'h'.(p).
    Proof.
      simpl; intros Hg Hh Hp.
      destruct g'h'; simpl in *.
      destruct Hg, Hh, Hp; simpl in *.
      path_natural_transformation.
      autorewrite with functor morphism.
      reflexivity.
    Qed.

    definition path_morphism' abf a'b'f'
               (gh g'h' : morphism abf a'b'f')
               (Hg : gh.(g) ≈ g'h'.(g))
               (Hh : gh.(h) ≈ g'h'.(h))
               (Hp : ((_ oL (Category.Morphisms.idtoiso (_ → _) (ap (@p_morphism_of _ _ S _ _) Hg) : Category.Core.morphism _ _ _))
                        ∘ (gh.(p))
                        ∘ ((Category.Morphisms.idtoiso (_ → _) (ap (@p_morphism_of _ _ T _ _) Hh) : Category.Core.morphism _ _ _)⁻¹ oR _)
                      ≈ g'h'.(p))%natural_transformation)
    : gh ≈ g'h' :=
         @path_morphism abf a'b'f' gh g'h' Hg Hh
                        (@path_morphism'_helper abf a'b'f' gh g'h' Hg Hh Hp).

    definition path_morphism'_uncurried abf a'b'f' gh g'h'
               (H : { HgHh : (gh.(g) ≈ g'h'.(g)) × (gh.(h) ≈ g'h'.(h))
                    | ((_ oL (Category.Morphisms.idtoiso (_ → _) (ap (@p_morphism_of _ _ S _ _) (pr1 HgHh)) : Category.Core.morphism _ _ _))
                         ∘ (gh.(p))
                         ∘ ((Category.Morphisms.idtoiso (_ → _) (ap (@p_morphism_of _ _ T _ _) (pr2 HgHh)) : Category.Core.morphism _ _ _)⁻¹ oR _)
                       ≈ g'h'.(p))%natural_transformation })
    : gh ≈ g'h' :=
         @path_morphism' abf a'b'f' gh g'h' (pr1 H.1) (pr2 H.1) H.2.

    definition compose s d d'
               (gh : morphism d d') (g'h' : morphism s d)
    : morphism s d'.
    Proof.
      exists (gh.(g) ∘ g'h'.(g)) (gh.(h) ∘ g'h'.(h)).
      exact ((_ oL (p_composition_of S _ _ _ _ _)⁻¹)
               ∘ (associator_1 _ _ _)
               ∘ (gh.(p) oR _)
               ∘ (associator_2 _ _ _)
               ∘ (_ oL g'h'.(p))
               ∘ (associator_1 _ _ _)
               ∘ ((p_composition_of T _ _ _ _ _ : Category.Core.morphism _ _ _)
                    oR _))%natural_transformation.
    end-/

    Global Arguments compose _ _ _ _ _ / .

    definition identity x : morphism x x.
    /-begin
      exists (identity (x.(a))) (identity (x.(b))).
      exact ((_ oL (p_identity_of S _ : Category.Core.morphism _ _ _)⁻¹)
               ∘ (right_identity_natural_transformation_2 _)
               ∘ (left_identity_natural_transformation_1 _)
               ∘ ((p_identity_of T _ : Category.Core.morphism _ _ _)
                    oR _))%natural_transformation.
    end-/

    Global Arguments identity _ / .
  End lax_comma_category_parts.
End LaxCommaCategoryParts.
