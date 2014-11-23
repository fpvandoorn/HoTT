/- Limits and Colimits -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core.
Require Import ExponentialLaws.Law1.Functors FunctorCategory.Core.
Require Import UniversalProperties KanExtensions.Core InitialTerminalCategory.Core NatCategory.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import Comma.Core.
Require Import Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope functor_scope.
Local Open Scope category_scope.

/- The diagonal or "constant diagram" functor Δ -/
section diagonal_functor
  Context [H : Funext].
  Variable C : PreCategory.
  Variable D : PreCategory.

  (**
     Quoting Dwyer and Spalinski:

     There is a diagonal or ``constant diagram'' functor

<<
     Δ : C → Cᴰ,
>>

     which carries an object [X : C] to the constant functor [Δ X : D
     → C] (by definition, this ``constant functor'' sends each object
     of [D] to [X] and each morphism of [D] to [Identity X]). The
     functor Δ assigns to each morphism [f : X → X'] of [C] the
     constant natural transformation [t(f) : Δ X → Δ X'] determined
     by the formula [t(f) d ≈ f] for each object [d] of [D].  **)

  /- We use [C¹] rather than [C] for judgemental compatibility with
      Kan extensions. -/

  definition diagonal_functor : Functor (1 → C) (D → C) :=
       @pullback_along _ D 1 C (Functors.to_terminal _).

  definition diagonal_functor' : Functor C (D → C) :=
       diagonal_functor ∘ ExponentialLaws.Law1.Functors.inverse _.

  section convert
    definition diagonal_functor_diagonal_functor' X
    : diagonal_functor X ≈ diagonal_functor' (X (center _)).
    Proof.
      path_functor.
      simpl.
      repeat (apply path_Π|| intro).
      apply identity_of.
    Qed.
  End convert.
End diagonal_functor.

Arguments diagonal_functor : simpl never.

section diagonal_functor_lemmas
  Context [H : Funext].
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable D' : PreCategory.

  definition compose_diagonal_functor x (F : Functor D' D)
  : diagonal_functor C D x ∘ F ≈ diagonal_functor _ _ x.
  Proof.
    path_functor.
  Qed.

  definition compose_diagonal_functor_natural_transformation
             x (F : Functor D' D)
  : NaturalTransformation (diagonal_functor C D x ∘ F) (diagonal_functor _ _ x) :=
       Build_NaturalTransformation
         (diagonal_functor C D x ∘ F)
         (diagonal_functor _ _ x)
         (λz, identity _)
         (λ_ _ _, transitivity
                         (left_identity _ _ _ _)
                         (symmetry
                            _ _
                            (right_identity _ _ _ _))).
End diagonal_functor_lemmas.

Hint Rewrite @compose_diagonal_functor : category.

section Limit
  Context [H : Funext].
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor D C.

  /- definition of Limit -/
  (**
     Quoting Dwyer and Spalinski:

     Let [D] be a small category and [F : D → C] a functor. A limit
     for [F] is an object [L] of [C] together with a natural
     transformation [t : Δ L → F] such that for every object [X] of
     [C] and every natural transformation [s : Δ X → F], there exists
     a unique map [s' : X → L] in [C] such that [t (Δ s') ≈ s].  **)

  definition IsLimit :=
       @IsRightKanExtensionAlong _ D 1 C (Functors.to_terminal _) F.
  (*definition IsLimit' := @IsTerminalMorphism (_ → _) (_ → _) (diagonal_functor C D) F.*)
  /- definition Limit (L : C) :=
    { t : SmallNaturalTransformation ((diagonal_functor C D) L) F &
      ΠX : C, Πs : SmallNaturalTransformation ((diagonal_functor C D) X) F,
        { s' : C.(Morphism) X L |
          unique
          (λs', SNTComposeT t ((diagonal_functor C D).(MorphismOf) s') ≈ s)
          s'
        }
    }.-/

  (**
     Quoting Dwyer and Spalinski:

     Let [D] be a small category and [F : D → C] a functor. A colimit
     for [F] is an object [c] of [C] together with a natural
     transformation [t : F → Δ c] such that for every object [X] of
     [C] and every natural transformation [s : F → Δ X], there exists
     a unique map [s' : c → X] in [C] such that [(Δ s') t ≈ s].  **)

  /- definition of Colimit -/
  definition IsColimit :=
       @IsLeftKanExtensionAlong _ D 1 C (Functors.to_terminal _) F.
  (*definition IsColimit' := @IsInitialMorphism (_ → _) (_ → _) F (diagonal_functor C D).*)
  /- definition Colimit (c : C) :=
    { t : SmallNaturalTransformation F ((diagonal_functor C D) c) &
      ΠX : C, Πs : SmallNaturalTransformation F ((diagonal_functor C D) X),
        { s' : C.(Morphism) c X | is_unique s' /\
          SNTComposeT ((diagonal_functor C D).(MorphismOf) s') t ≈ s
        }
    }.-/
  /- TODO(JasonGross): Figure out how to get good introduction and elimination rules working, which don't mention spurious identities. -/
  (*section AbstractionBarrier
    section Limit
      Set Printing  Implicit.
      section IntroductionAbstractionBarrier
        Local Open Scope morphism_scope.

        definition Build_IsLimit
                 (lim_obj : C)
                 (lim_mor : morphism (D → C)
                                     (diagonal_functor' C D lim_obj)
                                     F)
                 (lim := CommaCategory.Build_object
                           (diagonal_functor C D)
                           !(F : object (_ → _))
                           !lim_obj
                           (center _)
                           lim_mor)
                 (UniversalProperty
                  : Π(lim_obj' : C)
                           (lim_mor' : morphism (D → C)
                                                (diagonal_functor' C D lim_obj')
                                                F),
                      is_contr { m : morphism C lim_obj' lim_obj
                            | lim_mor ∘ morphism_of (diagonal_functor' C D) m ≈ lim_mor' })
        : IsTerminalMorphism lim.
        Proof.
          apply Build_IsTerminalMorphism.
          intros A' p'.
          specialize (UniversalProperty (A' (center _))).*)
End Limit.

/- TODO(JasonGross): Port MorphismsBetweenLimits from catdb -/
