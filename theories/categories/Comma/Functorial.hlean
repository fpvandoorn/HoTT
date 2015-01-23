/- Functoriality of the comma category construction -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core NaturalTransformation.Composition.Core.
Require Import NaturalTransformation.Composition.Laws.
Require Import InitialTerminalCategory.
Require Import Functor.Paths.
Require Functor.Identity NaturalTransformation.Identity.
Require Import Category.Strict.
Require Import Comma.Core.
Import Functor.Identity.FunctorIdentityNotations NaturalTransformation.Identity.NaturalTransformationIdentityNotations.
Require Import Types.Record Trunc HoTT.Tactics PathGroupoids Types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

/- The comma category construction is functorial in its category
    arguments.  We really should be using ∏ (dependent product) here,
    but I'm lazy, and will instead expand it out. -/

Local Ltac helper_t fwd_tac bak_tac fin :=
  repeat
    first [ fin
          | rewrite <- ?Category.Core.associativity;
            progress repeat first [ bak_tac
                                  | apply ap10; apply ap ]
          | rewrite → ?Category.Core.associativity;
            progress repeat first [ fwd_tac
                                  | apply ap ]
          | rewrite <- !composition_of ].

Local Tactic Notation "helper" tactic(fin) constr(hyp_fwd) constr(hyp_bak) :=
  let H := fresh in
  let H' := fresh in
  pose proof hyp_fwd as H;
    pose proof hyp_bak as H';
    simpl in *;
    helper_t ltac:(rewrite → H) ltac:(rewrite <- H') fin.

Local Ltac functorial_helper_t unfold_lem :=
  repeat (apply path_pi || intro); simpl;
  rewrite !transport_pi_constant; simpl;
  transport_path_pi_hammer; simpl;
  apply CommaCategory.path_morphism; simpl;
  unfold unfold_lem; simpl;
  repeat match goal with
           | _ => exact refl
           | [ |- context[CommaCategory.g (transport ?P ?p ?z)] ]
             => simpl rewrite (@ap_transport _ P _ _ _ p (λ_, @CommaCategory.g _ _ _ _ _ _ _) z)
           | [ |- context[CommaCategory.h (transport ?P ?p ?z)] ]
             => simpl rewrite (@ap_transport _ P _ _ _ p (λ_, @CommaCategory.h _ _ _ _ _ _ _) z)
           | [ |- context[transport (λy, ?f (?g y) ?z)] ]
             => simpl rewrite (λa b, @transport_compose _ _ a b (λy, f y z) g)
           | [ |- context[transport (λy, ?f (?g y))] ]
             => simpl rewrite (λa b, @transport_compose _ _ a b (λy, f y) g)
           | _ => rewrite !CommaCategory.ap_a_path_object'; simpl
           | _ => rewrite !CommaCategory.ap_b_path_object'; simpl
         end.

section functorial
  section single_source
    Variable A : PreCategory.
    Variable B : PreCategory.
    Variable C : PreCategory.
    Variable S : Functor A C.
    Variable T : Functor B C.

    section morphism_of
      Variable A' : PreCategory.
      Variable B' : PreCategory.
      Variable C' : PreCategory.
      Variable S' : Functor A' C'.
      Variable T' : Functor B' C'.

      Variable AF : Functor A A'.
      Variable BF : Functor B B'.
      Variable CF : Functor C C'.

      Variable TA : NaturalTransformation (S' ∘ AF) (CF ∘ S).
      Variable TB : NaturalTransformation (CF ∘ T) (T' ∘ BF).

      definition functorial_morphism_of_object_of : (S / T) → (S' / T') :=
           λx, CommaCategory.Build_object
                      S' T'
                      (AF (CommaCategory.a x))
                      (BF (CommaCategory.b x))
                      (TB (CommaCategory.b x) ∘ CF _1 (CommaCategory.f x) ∘ TA (CommaCategory.a x)).

      definition functorial_morphism_of_morphism_of
                 s d (m : morphism (S / T) s d)
      : morphism (S' / T') (functorial_morphism_of_object_of s) (functorial_morphism_of_object_of d).
      /-begin
        simpl in *.
        refine (CommaCategory.Build_morphism
                  (functorial_morphism_of_object_of s)
                  (functorial_morphism_of_object_of d)
                  (AF _1 (CommaCategory.g m))
                  (BF _1 (CommaCategory.h m))
                  _).
        unfold functorial_morphism_of_object_of; simpl.
        clear.
        abstract helper (exact (CommaCategory.p m)) (commutes TA) (commutes TB).
      end-/

      definition functorial_morphism_of : Functor (S / T) (S' / T').
      /-begin
        refine (Build_Functor
                  (S / T) (S' / T')
                  functorial_morphism_of_object_of
                  functorial_morphism_of_morphism_of
                  _
                  _);
        abstract (
            intros;
            apply CommaCategory.path_morphism; simpl;
            auto with functor
          ).
      end-/
    End morphism_of.

    section identity_of
      definition functorial_identity_of_helper x
      : @functorial_morphism_of_object_of _ _ _ S T 1 1 1 1 1 x = x.
      /-begin
        let A := match goal with |- ?A = ?B => constr:(A) end in
        let B := match goal with |- ?A = ?B => constr:(B) end in
        refine (@CommaCategory.path_object' _ _ _ _ _ A B 1%path 1%path _).
        exact (Category.Core.right_identity _ _ _ _ ⬝ Category.Core.left_identity _ _ _ _)%path.
      end-/

      definition functorial_identity_of [H : funext]
      : @functorial_morphism_of
          _ _ _ S T
          1 1 1 1 1
        = 1%functor.
      /-begin
        path_functor; simpl.
        exists (path_pi _ _ functorial_identity_of_helper).
        simpl.
        functorial_helper_t functorial_identity_of_helper.
      Qed.
    End identity_of.
  End single_source.

  section composition_of
    Variable A : PreCategory.
    Variable B : PreCategory.
    Variable C : PreCategory.
    Variable S : Functor A C.
    Variable T : Functor B C.

    Variable A' : PreCategory.
    Variable B' : PreCategory.
    Variable C' : PreCategory.
    Variable S' : Functor A' C'.
    Variable T' : Functor B' C'.

    Variable A'' : PreCategory.
    Variable B'' : PreCategory.
    Variable C'' : PreCategory.
    Variable S'' : Functor A'' C''.
    Variable T'' : Functor B'' C''.

    Variable AF : Functor A A'.
    Variable BF : Functor B B'.
    Variable CF : Functor C C'.

    Variable TA : NaturalTransformation (S' ∘ AF) (CF ∘ S).
    Variable TB : NaturalTransformation (CF ∘ T) (T' ∘ BF).

    Variable AF' : Functor A' A''.
    Variable BF' : Functor B' B''.
    Variable CF' : Functor C' C''.

    Variable TA' : NaturalTransformation (S'' ∘ AF') (CF' ∘ S').
    Variable TB' : NaturalTransformation (CF' ∘ T') (T'' ∘ BF').

    Let AF'' := (AF' ∘ AF)%functor.
    Let BF'' := (BF' ∘ BF)%functor.
    Let CF'' := (CF' ∘ CF)%functor.

    Let TA'' : NaturalTransformation (S'' ∘ AF'') (CF'' ∘ S) :=
         ((associator_2 _ _ _)
            ∘ (CF' oL TA)
            ∘ (associator_1 _ _ _)
            ∘ (TA' oR AF)
            ∘ associator_2 _ _ _)%natural_transformation.
    Let TB'' : NaturalTransformation (CF'' ∘ T) (T'' ∘ BF'') :=
         ((associator_1 _ _ _)
            ∘ (TB' oR BF)
            ∘ (associator_2 _ _ _)
            ∘ (CF' oL TB)
            ∘ associator_1 _ _ _)%natural_transformation.

    definition functorial_composition_of_helper x
    : (functorial_morphism_of TA' TB' ∘ functorial_morphism_of TA TB)%functor x
      = functorial_morphism_of TA'' TB'' x.
    Proof.
      let A := match goal with |- ?A = ?B => constr:(A) end in
      let B := match goal with |- ?A = ?B => constr:(B) end in
      refine (@CommaCategory.path_object' _ _ _ _ _ A B 1%path 1%path _).
      subst AF'' BF'' CF'' TA'' TB''.
      simpl in *.
      abstract (
          autorewrite with morphism; simpl;
          helper (exact refl) (commutes TA') (commutes TB')
        ).
    end-/

    definition functorial_composition_of [H : funext]
    : (functorial_morphism_of TA' TB' ∘ functorial_morphism_of TA TB)%functor
      = functorial_morphism_of TA'' TB''.
    Proof.
      path_functor; simpl.
      exists (path_pi _ _ functorial_composition_of_helper).
      functorial_helper_t functorial_composition_of_helper.
    Qed.
  End composition_of.
End functorial.
