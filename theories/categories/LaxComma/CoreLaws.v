Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Functor.Identity.
Require Import Category.Strict.
Require Import Functor.Composition.Core.
Require Import NaturalTransformation.Paths NaturalTransformation.Composition.Core.
Require Import Category.Morphisms FunctorCategory.Core.
Require Import Pseudofunctor.Core Pseudofunctor.RewriteLaws.
Require Import NaturalTransformation.Composition.Laws.
Require Import FunctorCategory.Morphisms.
Require LaxComma.CoreParts.
Require Import Types.Record Trunc HoTT.Tactics Types.Paths Types.Sigma.

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

Module Import LaxCommaCategory.
  Include LaxComma.CoreParts.LaxCommaCategoryParts.
  section lax_comma_category_parts
    Context [H : Funext].
    Variable A : PreCategory.
    Variable B : PreCategory.

    Variable S : Pseudofunctor A.
    Variable T : Pseudofunctor B.

    Context [H : Πa b, IsHSet (Functor (S a) (T b))].

    Local Notation object := (@object _ A B S T).
    Local Notation morphism := (@morphism _ A B S T).
    Local Notation compose := (@compose _ A B S T).
    Local Notation identity := (@identity _ A B S T).

    Local Ltac t_do_work :=
      repeat match goal with
               | _ => reflexivity
               | [ |- context[components_of ?T⁻¹ ?x] ]
                 => progress change (T⁻¹ x) with ((T x)⁻¹)
               | [ |- context[?F _1 ?m⁻¹] ]
                 => progress change (F _1 m⁻¹) with ((F _1 m)⁻¹)
               | _ => progress repeat iso_collapse_inverse_right'
             end.

    Local Ltac t_start :=
      simpl in *;
      repeat match goal with
               | [ H : ?x ≈ _ |- _ ] => rewrite H; clear H; try clear x
             end;
      path_natural_transformation;
      simpl in *;
      rewrite !Category.Core.left_identity, !Category.Core.right_identity;
      rewrite !composition_of.

    Local Ltac t :=
      t_start;
      rewrite <- !Category.Core.associativity;
      /- A reflective simplifier would be really useful here... -/
      repeat match goal with
               | _ => progress t_do_work
               | [ |- context[components_of ?T ?x] ]
                 => simpl rewrite <- !(commutes_pT_F T)
               | [ |- context[components_of ?T ?x] ]
                 => simpl rewrite <- !(commutes T)
               | _ => iso_move_inverse
             end.

    /- Ugh. The following code constructs the type of the helper lemma:
<<
      definition associativity x1 x2 x3 x4
            (m1 : morphism x1 x2) (m2 : morphism x2 x3) (m3 : morphism x3 x4)
      : compose (compose m3 m2) m1 ≈ compose m3 (compose m2 m1).
      /-begin
        refine (@path_morphism' _ _
                                (compose (compose m3 m2) m1)
                                (compose m3 (compose m2 m1))
                                (Category.Core.associativity _ _ _ _ _ _ _ _)
                                (Category.Core.associativity _ _ _ _ _ _ _ _)
                                _).
        simpl in *.
        repeat match goal with
                 | [ |- context[@morphism_inverse
                                     _ _ _ _
                                     (@isisomorphism_isomorphic
                                        _ _ _
                                        (Category.Morphisms.idtoiso
                                           ?C0
                                           (ap (p_morphism_of ?F (s:=_) (d:=_))
                                               (Category.Core.associativity ?C ?x1 ?x2 ?x3 ?x4 ?m1 ?m2 ?m3))))] ]
                   => generalize (@p_composition_of_coherent_inverse_for_rewrite _ C F x1 x2 x3 x4 m1 m2 m3);
                     generalize (Category.Morphisms.idtoiso
                                   C0
                                   (ap (p_morphism_of F (s:=_) (d:=_))
                                       (Category.Core.associativity C x1 x2 x3 x4 m1 m2 m3)))
                 | [ |- context[Category.Morphisms.idtoiso
                                     ?C0
                                     (ap (p_morphism_of ?F (s:=_) (d:=_))
                                         (Category.Core.associativity ?C ?x1 ?x2 ?x3 ?x4 ?m1 ?m2 ?m3))] ]
                   => generalize (@p_composition_of_coherent_for_rewrite _ C F x1 x2 x3 x4 m1 m2 m3);
                     generalize (Category.Morphisms.idtoiso
                                   C0
                                   (ap (p_morphism_of F (s:=_) (d:=_))
                                       (Category.Core.associativity C x1 x2 x3 x4 m1 m2 m3)))
               end.
        simpl.
        destruct_head morphism.
        destruct_head object.
        simpl in *.
        repeat match goal with
                 | [ |- context[p_composition_of ?F ?x ?y ?z ?m1 ?m2] ]
                   => generalize dependent (p_composition_of F x y z m1 m2)
                 | [ |- context[p_identity_of ?F ?x] ]
                   => generalize dependent (p_identity_of F x)
                 | [ |- context[p_morphism_of ?F ?x] ]
                   => generalize dependent (p_morphism_of F x)
                 | [ |- context[p_object_of ?F ?x] ]
                   => generalize dependent (p_object_of F x)
               end.
        simpl.
        clear.
        repeat (let H := fresh "x" in intro H).
        repeat match goal with H : _ |- _ => revert H end.
        intro.
>> -/

    definition associativity_helper
          {x x0 : PreCategory} {x1 : Functor x0 x}
          {x2 x3 : PreCategory} {x4 : Functor x3 x2} {x5 x6 : PreCategory}
          {x7 : Functor x6 x5} {x8 x9 : PreCategory} {x10 : Functor x9 x8}
          {x11 : Functor x9 x6} {x12 : Functor x9 x3} {x13 : Functor x0 x6}
          {x14 : Functor x9 x6} {x15 : Functor x8 x5} {x16 : Functor x x5}
          {x17 : Functor x9 x0} {x18 : Functor x8 x}
          {x19 : NaturalTransformation (x18 ∘ x10) (x1 ∘ x17)}
          {x20 : Functor x0 x3} {x21 : Functor x x2}
          {x22 : NaturalTransformation (x21 ∘ x1) (x4 ∘ x20)}
          {x23 : Functor x8 x2} {x24 : Functor x3 x6} {x25 : Functor x2 x5}
          {x26 : NaturalTransformation (x25 ∘ x4) (x7 ∘ x24)}
          {x27 : Functor x8 x5} {x28 : @Isomorphic (_ → _) x27 (x25 ∘ x23)%functor}
          {x29 : @Isomorphic (_ → _) x23 (x21 ∘ x18)%functor}
          {x30 : @Isomorphic (_ → _) x16 (x25 ∘ x21)%functor}
          {x31 : @Isomorphic (_ → _) x15 (x16 ∘ x18)%functor}
          {x32 : @Isomorphic (_ → _) x14 (x13 ∘ x17)%functor}
          {x33 : @Isomorphic (_ → _) x13 (x24 ∘ x20)%functor}
          {x34 : @Isomorphic (_ → _) x12 (x20 ∘ x17)%functor}
          {x35 : @Isomorphic (_ → _) x11 (x24 ∘ x12)%functor}
          {x36 : @Isomorphic (_ → _) x14 x11}
          (x37 : (x36 : Category.Core.morphism _ _ _) =
                 (x35 ⁻¹
                      ∘ (x24 oL x34 ⁻¹ ∘ (associator_1 x24 x20 x17 ∘ ((x33 : Category.Core.morphism _ _ _) oR x17 ∘ (x32 : Category.Core.morphism _ _ _)))))%natural_transformation)
          {x38 : @Isomorphic (_ → _) x15 x27}
          (x39 : x38 ⁻¹ =
                 (x31 ⁻¹ ∘ (x30 ⁻¹ oR x18) ∘ inverse (associator_1 x25 x21 x18)
                      ∘ (x25 oL (x29 : Category.Core.morphism _ _ _)) ∘ (x28 : Category.Core.morphism _ _ _))%natural_transformation)
    : (x7 oL (x36 : Category.Core.morphism _ _ _)
          ∘ (x7 oL x32 ⁻¹ ∘ associator_1 x7 x13 x17
                ∘ (x7 oL x33 ⁻¹ ∘ associator_1 x7 x24 x20 ∘ (x26 oR x20)
                      ∘ associator_2 x25 x4 x20 ∘ (x25 oL x22) o
                      associator_1 x25 x21 x1 ∘ ((x30 : Category.Core.morphism _ _ _) oR x1) oR x17)
                ∘ associator_2 x16 x1 x17 ∘ (x16 oL x19) ∘ associator_1 x16 x18 x10
                ∘ ((x31 : Category.Core.morphism _ _ _) oR x10)) ∘ (x38 ⁻¹ oR x10))%natural_transformation =
      (x7 oL x35 ⁻¹ ∘ associator_1 x7 x24 x12 ∘ (x26 oR x12)
          ∘ associator_2 x25 x4 x12
          ∘ (x25
               oL (x4 oL x34 ⁻¹ ∘ associator_1 x4 x20 x17 ∘ (x22 oR x17)
                      ∘ associator_2 x21 x1 x17 ∘ (x21 oL x19)
                      ∘ associator_1 x21 x18 x10 ∘ ((x29 : Category.Core.morphism _ _ _) oR x10)))
          ∘ associator_1 x25 x23 x10 ∘ ((x28 : Category.Core.morphism _ _ _) oR x10))%natural_transformation.
    Proof.
      Time t. /- 18.647s -/
    Qed.

    definition associativity x1 x2 x3 x4
          (m1 : morphism x1 x2) (m2 : morphism x2 x3) (m3 : morphism x3 x4)
    : compose (compose m3 m2) m1 ≈ compose m3 (compose m2 m1).
    Proof.
      refine (@path_morphism' _ A B S T _ _
                              (compose (compose m3 m2) m1)
                              (compose m3 (compose m2 m1))
                              (Category.Core.associativity _ _ _ _ _ _ _ _)
                              (Category.Core.associativity _ _ _ _ _ _ _ _)
                              _).
      simpl.
      Time apply associativity_helper.
      - Time exact (p_composition_of_coherent_for_rewrite _ _ _ _ _ _ _ _).
      - Time exact (p_composition_of_coherent_inverse_for_rewrite _ _ _ _ _ _ _ _).
    end-/

    /- Ugh.  To construct the type of this lemma, the code is:
<<
definition left_identity (s d : object) (m : morphism s d)
      : compose (identity _) m ≈ m.
      /-begin
        refine (@path_morphism' _ _
                               (compose (identity _) m) m
                               (Category.Core.left_identity _ _ _ _)
                               (Category.Core.left_identity _ _ _ _)
                               _).
        simpl in *.
        repeat match goal with
                 | [ |- context[@morphism_inverse
                                     _ _ _ _
                                     (@isisomorphism_isomorphic
                                        _ _ _
                                        (Category.Morphisms.idtoiso
                                           ?C0
                                           (ap (p_morphism_of ?F (s:=_) (d:=_))
                                               (Category.Core.left_identity ?C ?x ?y ?f))))] ]
                   => generalize (@p_left_identity_of_coherent_inverse_for_rewrite _ C F x y f);
                     generalize (Category.Morphisms.idtoiso
                                   C0
                                   (ap (p_morphism_of F (s:=_) (d:=_))
                                       (Category.Core.left_identity C x y f)))
                 | [ |- context[Category.Morphisms.idtoiso
                                     ?C0
                                     (ap (p_morphism_of ?F (s:=_) (d:=_))
                                         (Category.Core.left_identity ?C ?x ?y ?f))] ]
                   => generalize (@p_left_identity_of_coherent_for_rewrite _ C F x y f);
                     generalize (Category.Morphisms.idtoiso
                                   C0
                                   (ap (p_morphism_of F (s:=_) (d:=_))
                                       (Category.Core.left_identity C x y f)))
               end.
        simpl.
        destruct_head morphism.
        destruct_head object.
        simpl in *.
        repeat match goal with
                 | [ |- context[p_composition_of ?F ?x ?y ?z ?m1 ?m2] ]
                   => generalize dependent (p_composition_of F x y z m1 m2)
                 | [ |- context[p_identity_of ?F ?x] ]
                   => generalize dependent (p_identity_of F x)
                 | [ |- context[p_morphism_of ?F ?x] ]
                   => generalize dependent (p_morphism_of F x)
                 | [ |- context[p_object_of ?F ?x] ]
                   => generalize dependent (p_object_of F x)
               end.
        simpl.
        clear.
        repeat (let H := fresh "x" in intro H).
        repeat match goal with H : _ |- _ => revert H end.
        intro.
>> -/

    definition left_identity_helper
          {x x0 : PreCategory} {x1 : Functor x0 x}
          {x2 x3 : PreCategory} {x4 : Functor x3 x2} {x5 x6 : Functor x3 x0}
          {x7 : Functor x2 x} {x8 : NaturalTransformation (x7 ∘ x4) (x1 ∘ x6)}
          {x9 : Functor x2 x} {x10 : Functor x0 x0} {x11 : Functor x x}
          {x12 : @Isomorphic (_ → _) x11 1%functor} {x13 : @Isomorphic (_ → _) x10 1%functor}
          {x14 : @Isomorphic (_ → _) x9 (x11 ∘ x7)%functor} {x15 : @Isomorphic (_ → _) x5 (x10 ∘ x6)%functor}
          {x16 : @Isomorphic (_ → _) x5 x6}
          {x17 : (x16 : Category.Core.morphism _ _ _) =
                 (left_identity_natural_transformation_1 x6 ∘ ((x13 : Category.Core.morphism _ _ _) oR x6 ∘ (x15 : Category.Core.morphism _ _ _)))%natural_transformation}
          {x18 : @Isomorphic (_ → _) x9 x7}
          {x19 : x18 ⁻¹ =
                 (x14 ⁻¹ ∘ (x12 ⁻¹ oR x7)
                      ∘ inverse (left_identity_natural_transformation_1 x7))%natural_transformation}
    : (x1 oL (x16 : Category.Core.morphism _ _ _)
          ∘ (x1 oL x15 ⁻¹ ∘ associator_1 x1 x10 x6
                ∘ (x1 oL x13 ⁻¹ ∘ right_identity_natural_transformation_2 x1
                      ∘ left_identity_natural_transformation_1 x1 o
                      ((x12 : Category.Core.morphism _ _ _) oR x1) oR x6) ∘ associator_2 x11 x1 x6 o
                (x11 oL x8) ∘ associator_1 x11 x7 x4 ∘ ((x14 : Category.Core.morphism _ _ _) oR x4)) o
          (x18 ⁻¹ oR x4))%natural_transformation ≈ x8.
    Proof.
      Time t. /- 3.959 s -/
    Qed.

    definition left_identity (s d : object) (m : morphism s d)
    : compose (identity _) m ≈ m.
    Proof.
      refine (@path_morphism' _ A B S T _ _
                              (compose (identity _) m) m
                              (Category.Core.left_identity _ _ _ _)
                              (Category.Core.left_identity _ _ _ _)
                              _).
      simpl.
      Time refine left_identity_helper.
      - exact (p_left_identity_of_coherent_for_rewrite _ _ _ _).
      - exact (p_left_identity_of_coherent_inverse_for_rewrite _ _ _ _).
    end-/

    /- To generate the type of this helper lemma, we used:
<<
      definition right_identity (s d : object) (m : morphism s d)
      : compose m (identity _) ≈ m.
      /-begin
        refine (@path_morphism' _ _
                               (compose m (identity _)) m
                               (Category.Core.right_identity _ _ _ _)
                               (Category.Core.right_identity _ _ _ _)
                               _).
        simpl in *.
        repeat match goal with
                 | [ |- context[@morphism_inverse
                                     _ _ _ _
                                     (@isisomorphism_isomorphic
                                        _ _ _
                                        (Category.Morphisms.idtoiso
                                           ?C0
                                           (ap (p_morphism_of ?F (s:=_) (d:=_))
                                               (Category.Core.right_identity ?C ?x ?y ?f))))] ]
                   => generalize (@p_right_identity_of_coherent_inverse_for_rewrite _ C F x y f);
                     generalize (Category.Morphisms.idtoiso
                                   C0
                                   (ap (p_morphism_of F (s:=_) (d:=_))
                                       (Category.Core.right_identity C x y f)))
                 | [ |- context[Category.Morphisms.idtoiso
                                     ?C0
                                     (ap (p_morphism_of ?F (s:=_) (d:=_))
                                         (Category.Core.right_identity ?C ?x ?y ?f))] ]
                   => generalize (@p_right_identity_of_coherent_for_rewrite _ C F x y f);
                     generalize (Category.Morphisms.idtoiso
                                   C0
                                   (ap (p_morphism_of F (s:=_) (d:=_))
                                       (Category.Core.right_identity C x y f)))
               end.
        simpl.
        destruct_head morphism.
        destruct_head object.
        simpl in *.
        repeat match goal with
                 | [ |- context[p_composition_of ?F ?x ?y ?z ?m1 ?m2] ]
                   => generalize dependent (p_composition_of F x y z m1 m2)
                 | [ |- context[p_identity_of ?F ?x] ]
                   => generalize dependent (p_identity_of F x)
                 | [ |- context[p_morphism_of ?F ?x] ]
                   => generalize dependent (p_morphism_of F x)
                 | [ |- context[p_object_of ?F ?x] ]
                   => generalize dependent (p_object_of F x)
               end.
        simpl.
        clear.
        repeat (let H := fresh "x" in intro H).
        repeat match goal with H : _ |- _ => revert H end.
        intro.
>> -/

    definition right_identity_helper
          {x x0 : PreCategory} {x1 : Functor x0 x}
          {x2 x3 : PreCategory} {x4 : Functor x3 x2} {x5 x6 : Functor x3 x0}
          {x7 : Functor x2 x} {x8 : NaturalTransformation (x7 ∘ x4) (x1 ∘ x6)}
          {x9 : Functor x2 x} {x10 : Functor x3 x3} {x11 : Functor x2 x2}
          {x12 : @Isomorphic (_ → _) x11 1%functor} {x13 : @Isomorphic (_ → _) x10 1%functor}
          {x14 : @Isomorphic (_ → _) x9 (x7 ∘ x11)%functor} {x15 : @Isomorphic (_ → _) x5 (x6 ∘ x10)%functor}
          {x16 : @Isomorphic (_ → _) x5 x6}
          {x17 : (x16 : Category.Core.morphism _ _ _) =
                 (right_identity_natural_transformation_1 x6 ∘ (x6 oL (x13 : Category.Core.morphism _ _ _) ∘ (x15 : Category.Core.morphism _ _ _)))%natural_transformation}
          {x18 : @Isomorphic (_ → _) x9 x7}
          {x19 : x18 ⁻¹ =
                 (x14 ⁻¹ ∘ (x7 oL x12 ⁻¹)
                      ∘ inverse (right_identity_natural_transformation_1 x7))%natural_transformation}
    : (x1 oL (x16 : Category.Core.morphism _ _ _)
          ∘ (x1 oL x15 ⁻¹ ∘ associator_1 x1 x6 x10 ∘ (x8 oR x10)
                ∘ associator_2 x7 x4 x10
                ∘ (x7
                     oL (x4 oL x13 ⁻¹ ∘ right_identity_natural_transformation_2 x4
                            ∘ left_identity_natural_transformation_1 x4 o
                            ((x12 : Category.Core.morphism _ _ _) oR x4))) ∘ associator_1 x7 x11 x4 o
                ((x14 : Category.Core.morphism _ _ _) oR x4)) ∘ (x18 ⁻¹ oR x4))%natural_transformation ≈ x8.
    Proof.
      Time t. /- 3.26 s -/
    Qed.

    definition right_identity (s d : object) (m : morphism s d)
    : compose m (identity _) ≈ m.
    Proof.
      refine (@path_morphism' _ A B S T _ _
                              (compose m (identity _)) m
                              (Category.Core.right_identity _ _ _ _)
                              (Category.Core.right_identity _ _ _ _)
                              _).
      simpl.
      Time refine right_identity_helper.
      - exact (p_right_identity_of_coherent_for_rewrite _ _ _ _).
      - exact (p_right_identity_of_coherent_inverse_for_rewrite _ _ _ _).
    end-/
  End lax_comma_category_parts.
End LaxCommaCategory.
