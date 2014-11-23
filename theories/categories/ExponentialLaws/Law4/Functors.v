/- Functors about currying, between [C₁ × C₂ → D] and [C₁ → (C₂ → D)] -/
Require Import Category.Core Category.Prod FunctorCategory.Core Functor.Core NaturalTransformation.Core NaturalTransformation.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

section law4
  Context [H : Funext].
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  Local Open Scope morphism_scope.

  Local Ltac do_exponential4_helper rew_comp :=
    intros; simpl;
    repeat (simpl;
            match goal with
              | _ => reflexivity
              | _ => progress rew_comp
              | _ => rewrite !identity_of
              | _ => rewrite !left_identity
              | _ => rewrite !right_identity
              | _ => rewrite ?associativity; progress f_ap
              | _ => rewrite <- ?associativity; progress f_ap
              | _ => rewrite !commutes
              | _ => rewrite ?associativity, !commutes
              | _ => rewrite <- ?associativity, !commutes
            end).

  /- [(yⁿ)ᵐ → yⁿᵐ] -/
  section functor
    Local Ltac do_exponential4 :=
         do_exponential4_helper ltac:(rewrite !composition_of).

    definition functor_object_of
    : (C1 → (C2 → D))%category → (C1 × C2 → D)%category.
    /-begin
      intro F; hnf in F |- *.
      refine (Build_Functor
                (C1 × C2) D
                (λc1c2, F (fst c1c2) (snd c1c2))
                (λs d m, F (fst d) _1 (snd m) ∘ (F _1 (fst m)) (snd s))
                _
                _);
        abstract do_exponential4.
    end-/

    definition functor_morphism_of
               s d (m : morphism (C1 → (C2 → D)) s d)
    : morphism (C1 × C2 → D)
               (functor_object_of s)
               (functor_object_of d).
    /-begin
      simpl.
      refine (Build_NaturalTransformation
                (functor_object_of s)
                (functor_object_of d)
                (λc, m (fst c) (snd c))
                _);
        abstract (
            repeat match goal with
                     | [ |- context[components_of ?T ?x ∘ components_of ?U ?x] ] =>
                       change (T x ∘ U x) with ((compose (C := (_ → _)) T U) x)
                     | _ => f_ap
                     | _ => rewrite !commutes
                     | _ => do_exponential4
                   end
          ).
    end-/

    definition functor
    : Functor (C1 → (C2 → D)) (C1 × C2 → D).
    /-begin
      refine (Build_Functor
                (C1 → (C2 → D)) (C1 × C2 → D)
                functor_object_of
                functor_morphism_of
                _
                _);
      abstract by path_natural_transformation.
    end-/
  End functor.

  /- [yⁿᵐ → (yⁿ)ᵐ] -/
  section inverse
    Local Ltac do_exponential4_inverse :=
         do_exponential4_helper ltac:(rewrite <- !composition_of).

    section object_of
      Variable F : Functor (C1 × C2) D.

      definition inverse_object_of_object_of
      : C1 → (C2 → D)%category.
      /-begin
        intro c1.
        refine (Build_Functor
                  C2 D
                  (λc2, F (c1, c2))
                  (λs2 d2 m2, morphism_of
                                     F
                                     (s := (c1, s2))
                                     (d := (c1, d2))
                                     (identity c1, m2))
                  _
                  _);
          abstract do_exponential4_inverse.
      end-/

      definition inverse_object_of_morphism_of
                 s d (m : morphism C1 s d)
      : morphism (C2 → D)
                 (inverse_object_of_object_of s)
                 (inverse_object_of_object_of d).
      /-begin
        refine (Build_NaturalTransformation
                  (inverse_object_of_object_of s)
                  (inverse_object_of_object_of d)
                  (λc, morphism_of
                              F
                              (s := (s, c))
                              (d := (d, c))
                              (m, identity c))
                  _);
        abstract do_exponential4_inverse.
      end-/

      definition inverse_object_of
      : (C1 → (C2 → D))%category.
      /-begin
        refine (Build_Functor
                  C1 (C2 → D)
                  inverse_object_of_object_of
                  inverse_object_of_morphism_of
                  _
                  _);
        abstract (path_natural_transformation; do_exponential4_inverse).
      end-/
    End object_of.

    section morphism_of
      definition inverse_morphism_of_components_of
                 s d (m : morphism (C1 × C2 → D) s d)
      : Πc, morphism (C2 → D)
                           ((inverse_object_of s) c)
                           ((inverse_object_of d) c).
      /-begin
        intro c.
        refine (Build_NaturalTransformation
                  ((inverse_object_of s) c)
                  ((inverse_object_of d) c)
                  (λc', m (c, c'))
                  _).
        abstract do_exponential4_inverse.
      end-/

      definition inverse_morphism_of
                 s d (m : morphism (C1 × C2 → D) s d)
      : morphism (C1 → (C2 → D))
                 (inverse_object_of s)
                 (inverse_object_of d).
      /-begin
        refine (Build_NaturalTransformation
                  (inverse_object_of s)
                  (inverse_object_of d)
                  (inverse_morphism_of_components_of m)
                  _).
        abstract (path_natural_transformation; do_exponential4_inverse).
      end-/
    End morphism_of.

    Arguments inverse_morphism_of_components_of / _ _ _ _ .

    definition inverse
    : Functor (C1 × C2 → D) (C1 → (C2 → D)).
    /-begin
      refine (Build_Functor
                (C1 × C2 → D) (C1 → (C2 → D))
                inverse_object_of
                inverse_morphism_of
                _
                _);
      abstract by path_natural_transformation.
    end-/
  End inverse.
End law4.
