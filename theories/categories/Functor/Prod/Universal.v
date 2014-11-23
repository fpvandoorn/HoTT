/- Universal properties of product categories -/
Require Import Category.Core Functor.Core Category.Prod NaturalTransformation.Core Functor.Composition.Core Functor.Prod.Core.
Require Import Functor.Paths.
Require Import Types.Prod HoTT.Tactics Types.ΠTypes.Sigma.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation fst_type := Coq.Init.Datatypes.fst.
Local Notation snd_type := Coq.Init.Datatypes.snd.
Local Notation pair_type := Coq.Init.Datatypes.pair.
Local Notation prod_type := Coq.Init.Datatypes.prod.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.

section universal
  Context [H : Funext].

  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.

  Local Open Scope functor_scope.

  section universal
    Variable a : Functor C A.
    Variable b : Functor C B.

    /- [fst ∘ (a × b) ≈ a] -/
    Lemma compose_fst_prod : fst ∘ (a × b) ≈ a.
    /-begin
      path_functor; trivial.
    end-/

    /- [snd ∘ (a × b) ≈ b] -/
    Lemma compose_snd_prod : snd ∘ (a × b) ≈ b.
    /-begin
      path_functor; trivial.
    end-/

    section unique
      Variable F : Functor C (A × B).
      Hypothesis H1 : fst ∘ F ≈ a.
      Hypothesis H2 : snd ∘ F ≈ b.

      Lemma unique_helper c
      : (a × b) c ≈ F c.
      /-begin
        pose proof (ap (λF, object_of F c) H1).
        pose proof (ap (λF, object_of F c) H2).
        simpl in *.
        path_induction.
        apply eta_prod.
      end-/

      Lemma unique_helper2
      : transport
          (λGO : C → prod_type A B,
             Πs d : C,
               morphism C s d ->
               prod_type (morphism A (fst_type (GO s)) (fst_type (GO d)))
                         (morphism B (snd_type (GO s)) (snd_type (GO d))))
          (path_Π(a × b) F unique_helper)
          (λ(s d : C) (m : morphism C s d), pair_type (a _1 m) (b _1 m)) =
        morphism_of F.
      /-begin
        repeat ⟨apply path_forall, intro⟩.
        repeat match goal with
                 | _ => reflexivity
                 | _ => progress simpl
                 | _ => rewrite !transport_forall_constant
               end.
        transport_path_forall_hammer.
        unfold unique_helper.
        repeat match goal with
                 | [ H : _ ≈ _ |- _ ] => case H; simpl; clear H
               end.
        repeat match goal with
                 | [ |- context[@morphism_of ?C ?D ?F ?s ?d ?m] ]
                   => destruct (@morphism_of C D F s d m); clear m
                 | [ |- context[@object_of ?C ?D ?F ?x] ]
                   => destruct (@object_of C D F x); clear x
               end.
        reflexivity.
      Qed.

      Lemma unique
      : a × b ≈ F.
      Proof.
        path_functor.
        exists (path_Π_ _ unique_helper).
        apply unique_helper2.
      end-/
    End unique.

    Local Open Scope core_scope.

    /- Universal property characterizing unique product of functors -/
    Global Instance contr_prod_type
           [H : IsHSet (Functor C A), IsHSet (Functor C B)]
    : is_contr { F : Functor C (A × B)
            | fst ∘ F ≈ a
              /\ snd ∘ F ≈ b } :=
         let x := {| center := (a × b;
                                (compose_fst_prod,
                                 compose_snd_prod)) |}
         in x.
    /-begin
      intro y.
      apply path_sigma_uncurried.
      simpl.
      exists (unique (fst_type y.2) (snd_type y.2)).
      exact (center _).
    Qed.
  End universal.

  /- Classification of path space of functors to a product precategory -/
  definition path_prod (F G : Functor C (A × B))
             (H1 : fst ∘ F ≈ fst ∘ G)
             (H2 : snd ∘ F ≈ snd ∘ G)
  : F ≈ G.
  Proof.
    etransitivity; [ symmetry | ];
    apply unique; try eassumption; reflexivity.
  end-/
End universal.
