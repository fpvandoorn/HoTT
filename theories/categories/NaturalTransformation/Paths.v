/- Classify the path space of natural transformations -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Equivalences Types.Sigma Trunc.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

section path_natural_transformation
  Context [H : Funext].

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.

  Local Open Scope equiv_scope.

  /- Equivalence between record and sigma versions of natural transformation -/
  Lemma equiv_sig_natural_transformation
  : { CO : Πx, morphism D (F x) (G x)
    | Πs d (m : morphism C s d),
        CO d ∘ F _1 m ≈ G _1 m ∘ CO s }
      ≃ NaturalTransformation F G.
  /-begin
    let build := constr:(@Build_NaturalTransformation _ _ F G) in
    let dpr1 := constr:(@components_of _ _ F G) in
    let dpr2 := constr:(@commutes _ _ F G) in
    apply (equiv_adjointify (λu, build u.1 u.2)
                            (λv, ⟨dpr1 v, dpr2 v⟩));
      hnf;
      [ intros []; intros; simpl; expand; f_ap; exact (center _)
      | intros; apply eta_sigma ].
  end-/

  /- The type of natural transformations is an hSet -/
  Global Instance trunc_natural_transformation
  : IsHSet (NaturalTransformation F G).
  /-begin
    eapply trunc_equiv'; [ exact equiv_sig_natural_transformation | ].
    typeclasses eauto.
  Qed.

  section path
    Variables T U : NaturalTransformation F G.

    /- Equality of natural transformations is implied by equality of components -/
    Lemma path'_natural_transformation
    : components_of T ≈ components_of U
      → T ≈ U.
    Proof.
      intros.
      destruct T, U; simpl in *.
      path_induction.
      f_ap;
        refine (center _).
    Qed.

    Lemma path_natural_transformation
    : components_of T == components_of U
      → T ≈ U.
    Proof.
      intros.
      apply path'_natural_transformation.
      apply path_forall; assumption.
    Qed.

    Let path_inv
    : T ≈ U → components_of T == components_of U :=
         (λH _, match H with idpath => idpath end).

    Lemma eisretr_path_natural_transformation
    : Sect path_natural_transformation path_inv.
    Proof.
      repeat intro.
      refine (center _).
    Qed.

    Lemma eissect_path_natural_transformation
    : Sect path_inv path_natural_transformation.
    Proof.
      repeat intro.
      refine (center _).
    Qed.

    Lemma eisadj_path_natural_transformation
    : Πx,
        @eisretr_path_natural_transformation (path_inv x)
        ≈ ap path_inv (eissect_path_natural_transformation x).
    Proof.
      repeat intro.
      refine (center _).
    Qed.

    /- Equality of natural transformations is equivalent to equality of components -/
    Lemma equiv_path_natural_transformation
    : T ≈ U ≃ (components_of T == components_of U).
    Proof.
      econstructor. econstructor. exact eisadj_path_natural_transformation.
    end-/
  End path.
End path_natural_transformation.

/- Tactic for proving equality of natural transformations -/
Ltac path_natural_transformation :=
  repeat match goal with
           | _ => intro
           | _ => apply path_natural_transformation; simpl
         end.
