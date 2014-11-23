/- Adjunctions as universal morphisms -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Identity Functor.Composition.Core.
Require Import Functor.Dual NaturalTransformation.Dual Category.Dual.
Require Import Adjoint.Core Adjoint.UnitCounit Adjoint.UnitCounitCoercions Adjoint.Dual.
Require Import Comma.Core UniversalProperties Comma.Dual InitialTerminalCategory.Core InitialTerminalCategory.Functors.
Require Import HProp Types.Sigma HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

section adjunction_universal
  /- [F ⊣ G] gives an initial object of [(Y / G)] for all [Y : C] -/
  section initial
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.
    Variable A : F -| G.
    Variable Y : C.

    definition initial_morphism__of__adjunction
    : object (Y / G) :=
         @CommaCategory.Build_object
           _ D C
           (! Y) G
           (center _)
           (F Y)
           ((unit A) Y).

    definition is_initial_morphism__of__adjunction
    : IsInitialMorphism initial_morphism__of__adjunction :=
         Build_IsInitialMorphism
           _
           _
           _
           _
           ((A : AdjunctionUnit _ _).2 _).
  End initial.

  Global Arguments initial_morphism__of__adjunction [C D F G] A Y.
  Global Arguments is_initial_morphism__of__adjunction [C D F G] A Y _.

  /- [F ⊣ G] gives a terminal object of [(F / X)] for all [X : D] -/
  section terminal
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.
    Variable A : F -| G.
    Variable X : D.

    definition terminal_morphism__of__adjunction
    : object (F / X) :=
         Eval simpl in
          dual_functor
            (! X)⁻¹op F⁻¹op
            (initial_morphism__of__adjunction A⁻¹op X).

    definition is_terminal_morphism__of__adjunction
    : IsTerminalMorphism terminal_morphism__of__adjunction :=
         is_initial_morphism__of__adjunction A⁻¹op X.
  End terminal.

  Global Arguments terminal_morphism__of__adjunction [C D F G] A X.
  Global Arguments is_terminal_morphism__of__adjunction [C D F G] A X _.
End adjunction_universal.

section adjunction_from_universal
  /- an initial object of [(Y / G)] for all [Y : C] gives a left adjoint to [G] -/
  section initial
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable G : Functor D C.
    Context `(HM : ΠY, @IsInitialMorphism _ _ Y G (M Y)).

    Local Notation obj_of Y :=
      (IsInitialMorphism_object (@HM Y))
        (only parsing).

    Local Notation mor_of Y0 Y1 f :=
      (let etaY1 := IsInitialMorphism_morphism (@HM Y1) in
       IsInitialMorphism_property_morphism (@HM Y0) _ (etaY1 ∘ f))
        (only parsing).

    Lemma identity_of Y : mor_of Y Y 1 ≈ 1.
    /-begin
      simpl.
      erewrite IsInitialMorphism_property_morphism_unique; [ reflexivity | ].
      rewrite ?identity_of, ?left_identity, ?right_identity.
      reflexivity.
    Qed.

    Lemma composition_of x y z g f
    : mor_of _ _ (f ∘ g) ≈ mor_of y z f ∘ mor_of x y g.
    Proof.
      simpl.
      erewrite IsInitialMorphism_property_morphism_unique; [ reflexivity | ].
      rewrite ?composition_of.
      repeat
        try_associativity_quick
        rewrite IsInitialMorphism_property_morphism_property.
      reflexivity.
    Qed.

    definition functor__of__initial_morphism : Functor C D :=
         Build_Functor
           C D
           (λx, obj_of x)
           (λs d m, mor_of s d m)
           composition_of
           identity_of.

    definition adjunction__of__initial_morphism
    : functor__of__initial_morphism -| G.
    Proof.
      refine (_ : AdjunctionUnit functor__of__initial_morphism G).
      eexists (Build_NaturalTransformation
                1
                (G ∘ functor__of__initial_morphism)
                (λx, IsInitialMorphism_morphism (@HM x))
                (λs d m,
                   symmetry
                     _ _
                     (IsInitialMorphism_property_morphism_property (@HM s) _ _))).
      simpl.
      exact (λc, @IsInitialMorphism_property _ _ c G (M c) (@HM c)).
    end-/
  End initial.

  /- a terminal object of [(F / X)] for all [X : D] gives a right adjoint to [F] -/
  section terminal
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable F : Functor C D.
    Context `(HM : ΠX, @IsTerminalMorphism _ _ F X (M X)).

    definition functor__of__terminal_morphism : Functor D C :=
         (@functor__of__initial_morphism
            (D⁻¹op) (C⁻¹op)
            (F⁻¹op)
            (λx : D, dual_functor F !x (M x)) HM)⁻¹op.

    definition adjunction__of__terminal_morphism
    : F -| functor__of__terminal_morphism :=
         ((@adjunction__of__initial_morphism
             (D⁻¹op) (C⁻¹op)
             (F⁻¹op)
             (λx : D, dual_functor F !x (M x)) HM)⁻¹op)%adjunction.
  End terminal.
End adjunction_from_universal.
