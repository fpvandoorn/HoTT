/- Composition of natural transformations -/
Require Import Category.Core Functor.Core Functor.Composition.Core NaturalTransformation.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

/- Vertical composition -/
section composition
  (**
     We have the diagram
<<
          F
     C -------> D
          |
          |
          | T
          |
          V
     C -------> D
          F'
          |
          | T'
          |
          V
     C ------> D
          F''
>>

     And we want the commutative diagram
<<
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    F' m    V
     F' A -------> F' B
      |            |
      |            |
      | T' A       | T' B
      |            |
      V    F'' m   V
     F'' A ------> F'' B
>>
  *)

  section compose
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variables F F' F'' : Functor C D.

    Variable T' : NaturalTransformation F' F''.
    Variable T : NaturalTransformation F F'.

    Local Notation CO c := (T' c ∘ T c).

    definition compose_commutes s d (m : morphism C s d)
    : CO d ∘ morphism_of F m ≈ morphism_of F'' m ∘ CO s :=
         (associativity _ _ _ _ _ _ _ _)
           ⬝ ap (λx, _ ∘ x) (commutes T _ _ m)
           ⬝ (associativity_sym _ _ _ _ _ _ _ _)
           ⬝ ap (λx, x ∘ _) (commutes T' _ _ m)
           ⬝ (associativity _ _ _ _ _ _ _ _).

    /- We define the symmetrized version separately so that we can get more unification in the functor [(C → D)ᵒᵖ → (Cᵒᵖ → Dᵒᵖ)] -/
    definition compose_commutes_sym s d (m : morphism C s d)
    : morphism_of F'' m ∘ CO s ≈ CO d ∘ morphism_of F m :=
         (associativity_sym _ _ _ _ _ _ _ _)
           ⬝ ap (λx, x ∘ _) (commutes_sym T' _ _ m)
           ⬝ (associativity _ _ _ _ _ _ _ _)
           ⬝ ap (λx, _ ∘ x) (commutes_sym T _ _ m)
           ⬝ (associativity_sym _ _ _ _ _ _ _ _).

    Global Arguments compose_commutes : simpl never.
    Global Arguments compose_commutes_sym : simpl never.

    definition compose
    : NaturalTransformation F F'' :=
         Build_NaturalTransformation' F F''
                                      (λc, CO c)
                                      compose_commutes
                                      compose_commutes_sym.
  End compose.

  /- Whiskering -/
  Local Ltac whisker_t :=
    simpl;
    repeat first [ apply commutes
                 | apply ap
                 | progress (etransitivity; try apply composition_of); []
                 | progress (etransitivity; try (symmetry; apply composition_of)); [] ].

  section whisker
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable E : PreCategory.

    section L
      Variable F : Functor D E.
      Variables G G' : Functor C D.
      Variable T : NaturalTransformation G G'.

      Local Notation CO c := (morphism_of F (T c)).

      definition whisker_l_commutes s d (m : morphism C s d)
      : F _1 (T d) ∘ (F ∘ G) _1 m ≈ (F ∘ G') _1 m ∘ F _1 (T s).
      /-begin
        whisker_t.
      end-/

      Global Arguments whisker_l_commutes : simpl never.

      definition whisker_l :=
           Build_NaturalTransformation
             (F ∘ G) (F ∘ G')
             (λc, CO c)
             whisker_l_commutes.
    End L.

    section R
      Variables F F' : Functor D E.
      Variable T : NaturalTransformation F F'.
      Variable G : Functor C D.

      Local Notation CO c := (T (G c)).

      definition whisker_r_commutes s d (m : morphism C s d)
      : T (G d) ∘ (F ∘ G) _1 m ≈ (F' ∘ G) _1 m ∘ T (G s).
      /-begin
        whisker_t.
      end-/

      Global Arguments whisker_r_commutes : simpl never.

      definition whisker_r :=
           Build_NaturalTransformation
             (F ∘ G) (F' ∘ G)
             (λc, CO c)
             whisker_r_commutes.
    End R.
  End whisker.
End composition.

Module Export NaturalTransformationCompositionCoreNotations.
  Infix "o" := compose : natural_transformation_scope.
  Infix "oL" := whisker_l (at level 40, left associativity) : natural_transformation_scope.
  Infix "oR" := whisker_r (at level 40, left associativity) : natural_transformation_scope.
End NaturalTransformationCompositionCoreNotations.
