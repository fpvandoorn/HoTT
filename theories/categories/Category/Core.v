/- definition of a [PreCategory] -/
Require Export Overture.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Global Set Primitive Projections.

Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.

Local Open Scope morphism_scope.

/- Quoting the HoTT Book: -/
/- definition 9.1.1. A precategory [A] consists of the following.

    (i) A type [A₀] of objects. We write [a : A] for [a : A₀].

    (ii) For each [a, b : A], a set [hom_A(a, b)] of arrows or morphisms.

    (iii) For each [a : A], a morphism [1ₐ : hom_A(a, a)].

    (iv) For each [a, b, c : A], a function

         [hom_A(b, c) → hom_A(a, b) → hom_A(a, c)]

         denoted infix by [g ↦ f ↦ g ∘ f] , or sometimes simply by [g f].

    (v) For each [a, b : A] and [f : hom_A(a, b)], we have [f ≈ 1_b ∘
        f] and [f ≈ f ∘ 1ₐ].

    (vi) For each [a, b, c, d : A] and [f : hom_A(a, b)], [g :
         hom_A(b, c)], [h : hom_A(c,d)], we have [h ∘ (g ∘ f) ≈ (h ∘
         g) ∘ f]. -/
/- In addition to these laws, we ask for a few redundant laws to give
    us more judgmental equalities.  For example, since [(p⁻¹)⁻¹ ≢ p] for
    paths [p], we ask for the symmetrized version of the associativity
    law, so we can swap them when we take the dual. -/

Record PreCategory :=
  Build_PreCategory' {
      object :> Type;
      morphism : object → object → Type;

      identity : Πx, morphism x x;
      compose : Πs d d',
                  morphism d d'
                  → morphism s d
                  → morphism s d'
                              where "f 'o' g" := (compose f g);

      associativity : Πx1 x2 x3 x4
                             (m1 : morphism x1 x2)
                             (m2 : morphism x2 x3)
                             (m3 : morphism x3 x4),
                        (m3 ∘ m2) ∘ m1 ≈ m3 ∘ (m2 ∘ m1);
      /- Ask for the symmetrized version of [associativity], so that [(Cᵒᵖ)ᵒᵖ] and [C] are equal without [Funext] -/
      associativity_sym : Πx1 x2 x3 x4
                                 (m1 : morphism x1 x2)
                                 (m2 : morphism x2 x3)
                                 (m3 : morphism x3 x4),
                            m3 ∘ (m2 ∘ m1) ≈ (m3 ∘ m2) ∘ m1;

      left_identity : Πa b (f : morphism a b), identity b ∘ f ≈ f;
      right_identity : Πa b (f : morphism a b), f ∘ identity a ≈ f;
      /- Ask for the double-identity version so that [InitialTerminalCategory.Functors.from_terminal Cᵒᵖ X] and [(InitialTerminalCategory.Functors.from_terminal C X)ᵒᵖ] are convertible. -/
      identity_identity : Πx, identity x ∘ identity x ≈ identity x;

      trunc_morphism : Πs d, IsHSet (morphism s d)
    }.

Bind Scope category_scope with PreCategory.
Bind Scope object_scope with object.
Bind Scope morphism_scope with morphism.

/- We want eta-expanded primitive projections to [simpl] away. -/
Arguments object !C%category / : rename.
Arguments morphism !C%category / s d : rename.
Arguments identity {!C%category} / x%object : rename.
Arguments compose {!C%category} / {s d d'}%object (m1 m2)%morphism : rename.

Local Infix "o" := compose : morphism_scope.
/- Perhaps we should consider making this notation more global. -/
/- Perhaps we should pre-reserve all of the notations. -/
Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
Local Notation "1" := (identity _) : morphism_scope.

/- Define a convenience wrapper for building a precategory without
    specifying the redundant proofs. -/
definition Build_PreCategory
           object morphism compose identity
           associativity left_identity right_identity :=
     @Build_PreCategory'
       object
       morphism
       compose
       identity
       associativity
       (λ_ _ _ _ _ _ _, symmetry _ _ (associativity _ _ _ _ _ _ _))
       left_identity
       right_identity
       (λ_, left_identity _ _ _).

Global Existing Instance trunc_morphism.

/- create a hint db for all category theory things -/
Create HintDb category discriminated.
/- create a hint db for morphisms in categories -/
Create HintDb morphism discriminated.

Hint Resolve @left_identity @right_identity @associativity : category morphism.
Hint Rewrite @left_identity @right_identity : category.
Hint Rewrite @left_identity @right_identity : morphism.

/- Simple laws about the identity morphism -/
section identity_unique
  Variable C : PreCategory.

  /- The identity morphism is unique. -/
  Lemma identity_unique (id0 id1 : Πx, morphism C x x)
        (id1_left : Πs d (m : morphism C s d), id1 _ ∘ m ≈ m)
        (id0_right : Πs d (m : morphism C s d), m ∘ id0 _ ≈ m)
  : id0 == id1.
  Proof.
    intro.
    etransitivity;
      [ symmetry; apply id1_left
      | apply id0_right ].
  Qed.

  /- Anything equal to the identity acts like it.  This is obvious,
      but useful as a helper lemma for automation. -/
  definition concat_left_identity s d (m : morphism C s d) i
  : i ≈ 1 → i ∘ m ≈ m :=
       λH, (ap10 (ap _ H) _ ⬝ left_identity _ _ _ m)%path.

  definition concat_right_identity s d (m : morphism C s d) i
  : i ≈ 1 → m ∘ i ≈ m :=
       λH, (ap _ H ⬝ right_identity _ _ _ m)%path.
End identity_unique.

/- Make a separate module for Notations, which can be exported/imported separately. -/
Module Export CategoryCoreNotations.
  /- We have notations for both the eta-expanded and non-eta-expanded
      forms. -/
  Infix "o" := (@compose _ _ _ _) : morphism_scope.
  Infix "o" := compose : morphism_scope.
  /- Perhaps we should consider making this notation more global. -/
  /- Perhaps we should pre-reserve all of the notations. -/
  Local Notation "x --> y" := (@morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
  Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
  Notation "1" := (identity _) : morphism_scope.
End CategoryCoreNotations.

/- We have a tactic for trying to run a tactic after associating morphisms either all the way to the left, or all the way to the right -/
/- We must first eta-contract primitive projections so that [rewrite] works -/
Tactic Notation "try_associativity_quick" tactic(tac) :=
  repeat match goal with
           | [ |- context[@compose ?C ?s ?d ?d' ?m1 ?m2] ]
             => progress change (@compose C s d d' m1 m2)
                with (compose (C := C) (s := s) (d := d) (d' := d') m1 m2)
         end;
  first [ rewrite <- ?associativity; tac
        | rewrite → ?associativity; tac ].
