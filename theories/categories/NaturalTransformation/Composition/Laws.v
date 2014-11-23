/- Laws about composition of functors -/
Require Import Category.Core Functor.Core Functor.Identity Functor.Composition.Core NaturalTransformation.Core NaturalTransformation.Identity NaturalTransformation.Composition.Core NaturalTransformation.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

section natural_transformation_identity
  Context [H : Funext].

  Variable C : PreCategory.
  Variable D : PreCategory.

  /- left identity : [1 ∘ T ≈ T] -/
  definition left_identity (F F' : Functor C D)
        (T : NaturalTransformation F F')
  : 1 ∘ T ≈ T.
  Proof.
    path_natural_transformation; auto with morphism.
  Qed.

  /- right identity : [T ∘ 1 ≈ T] -/
  definition right_identity (F F' : Functor C D)
        (T : NaturalTransformation F F')
  : T ∘ 1 ≈ T.
  Proof.
    path_natural_transformation; auto with morphism.
  Qed.

  /- right whisker left identity : [1 ∘ᴿ F ≈ 1] -/
  definition whisker_r_left_identity E
             (G : Functor D E) (F : Functor C D)
  : identity G oR F ≈ 1.
  Proof.
    path_natural_transformation; auto with morphism.
  Qed.

  /- left whisker right identity : [G ∘ᴸ 1 ≈ 1] -/
  definition whisker_l_right_identity E
             (G : Functor D E) (F : Functor C D)
  : G oL identity F ≈ 1.
  Proof.
    path_natural_transformation; auto with functor.
  Qed.
End natural_transformation_identity.

Hint Rewrite @left_identity @right_identity : category.
Hint Rewrite @left_identity @right_identity : natural_transformation.

section whisker
  Context {fs : Funext}.

  /- whisker exchange law : [(G' ∘ᴸ T) ∘ (T' ∘ᴿ F) ≈ (T' ∘ᴿ F') ∘ (G ∘ᴸ T)] -/
  section exch
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable E : PreCategory.
    Variables G G' : Functor D E.
    Variables F F' : Functor C D.
    Variable T' : NaturalTransformation G G'.
    Variable T : NaturalTransformation F F'.

    definition exchange_whisker
    : (G' oL T) ∘ (T' oR F) ≈ (T' oR F') ∘ (G oL T).
    Proof.
      path_natural_transformation; simpl.
      symmetry.
      apply NaturalTransformation.Core.commutes.
    Qed.
  End exch.

  section whisker
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variables F G H : Functor C D.
    Variable T : NaturalTransformation G H.
    Variable T' : NaturalTransformation F G.

    /- left whisker composition : [F ∘ᴸ (T ∘ T') ≈ (F ∘ᴸ T) ∘ (F ∘ᴸ T')] -/
    definition composition_of_whisker_l E (I : Functor D E)
    : I oL (T ∘ T') ≈ (I oL T) ∘ (I oL T').
    Proof.
      path_natural_transformation; apply composition_of.
    Qed.

    /- right whisker composition : [(T ∘ T') ∘ᴿ F ≈ (T ∘ᴿ F) ∘ (T' ∘ᴿ F)] -/
    definition composition_of_whisker_r B (I : Functor B C)
    : (T ∘ T') oR I ≈ (T oR I) ∘ (T' oR I).
    Proof.
      path_natural_transformation; apply idpath.
    Qed.
  End whisker.
End whisker.

section associativity
  /- associators - natural transformations between [F ∘ (G ∘ H)] and [(F ∘ G) ∘ H] -/
  section functors
    Variable B : PreCategory.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable E : PreCategory.
    Variable F : Functor D E.
    Variable G : Functor C D.
    Variable H : Functor B C.

    Local Notation F0 := ((F ∘ G) ∘ H)%functor.
    Local Notation F1 := (F ∘ (G ∘ H))%functor.

    definition associator_1 : NaturalTransformation F0 F1 :=
         Eval simpl in
          generalized_identity F0 F1 idpath idpath.

    definition associator_2 : NaturalTransformation F1 F0 :=
         Eval simpl in
          generalized_identity F1 F0 idpath idpath.
  End functors.

  /- associativity : [(T ∘ U) ∘ V ≈ T ∘ (U ∘ V)] -/
  section nt
    Context {fs : Funext}.

    Local Open Scope natural_transformation_scope.

    definition associativity
               C D F G H I
               (V : @NaturalTransformation C D F G)
               (U : @NaturalTransformation C D G H)
               (T : @NaturalTransformation C D H I)
    : (T ∘ U) ∘ V ≈ T ∘ (U ∘ V).
    Proof.
      path_natural_transformation.
      apply associativity.
    Qed.
  End nt.
End associativity.

section functor_identity
  Context [H : Funext].

  Variable C : PreCategory.
  Variable D : PreCategory.

  Local Ltac nt_id_t := split; path_natural_transformation;
                        autorewrite with morphism; reflexivity.

  /- left unitors : natural transformations between [1 ∘ F] and [F] -/
  section left
    Variable F : Functor D C.

    definition left_identity_natural_transformation_1
    : NaturalTransformation (1 ∘ F) F :=
         Eval simpl in generalized_identity (1 ∘ F) F idpath idpath.
    definition left_identity_natural_transformation_2
    : NaturalTransformation F (1 ∘ F) :=
         Eval simpl in generalized_identity F (1 ∘ F) idpath idpath.

    definition left_identity_isomorphism
    : left_identity_natural_transformation_1 ∘ left_identity_natural_transformation_2 ≈ 1
      /\ left_identity_natural_transformation_2 ∘ left_identity_natural_transformation_1 ≈ 1.
    Proof.
      nt_id_t.
    Qed.
  End left.

  /- right unitors : natural transformations between [F ∘ 1] and [F] -/
  section right
    Variable F : Functor C D.

    definition right_identity_natural_transformation_1 : NaturalTransformation (F ∘ 1) F :=
         Eval simpl in generalized_identity (F ∘ 1) F idpath idpath.
    definition right_identity_natural_transformation_2 : NaturalTransformation F (F ∘ 1) :=
         Eval simpl in generalized_identity F (F ∘ 1) idpath idpath.

    definition right_identity_isomorphism
    : right_identity_natural_transformation_1 ∘ right_identity_natural_transformation_2 ≈ 1
      /\ right_identity_natural_transformation_2 ∘ right_identity_natural_transformation_1 ≈ 1.
    Proof.
      nt_id_t.
    Qed.
  End right.
End functor_identity.

/- Tactics for inserting appropriate associators, whiskers, and unitors -/
Ltac nt_solve_associator' :=
  repeat match goal with
           | _ => exact (associator_1 _ _ _)
           | _ => exact (associator_2 _ _ _)
           | _ => exact (left_identity_natural_transformation_1 _)
           | _ => exact (left_identity_natural_transformation_2 _)
           | _ => exact (right_identity_natural_transformation_1 _)
           | _ => exact (right_identity_natural_transformation_2 _)
           | [ |- NaturalTransformation (?F ∘ _) (?F ∘ _) ] =>
             refine (whisker_l F _)
           | [ |- NaturalTransformation (_ ∘ ?F) (_ ∘ ?F) ] =>
             refine (whisker_r _ F)
         end.
Ltac nt_solve_associator :=
  repeat match goal with
           | _ => refine (compose (associator_1 _ _ _) _); progress nt_solve_associator'
           | _ => refine (compose _ (associator_1 _ _ _)); progress nt_solve_associator'
           | _ => refine (compose (associator_2 _ _ _) _); progress nt_solve_associator'
           | _ => refine (compose _ (associator_2 _ _ _)); progress nt_solve_associator'
           | _ => progress nt_solve_associator'
         end.
