/- ∑-categories on morphisms - a category with the same objects, but a ∑ type for morphisms -/
Require Import HSet Types.unit HoTT.Tactics Types.ΠTypes.Sigma Basics.Trunc.
Require Import Category.Core Functor.Core Category.Sigma.Core.
Require Functor.Composition.Core Functor.Identity.
Require Import Functor.Paths.
Import Functor.Identity.FunctorIdentityNotations.
Import Functor.Composition.Core.FunctorCompositionCoreNotations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation sigT_type := Coq.Init.Specif.sigT.
Local Notation pr1_type := Overture.dpr1.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.

section sigT_mor
  Variable A : PreCategory.
  Variable Pmor : Πs d, morphism A s d → Type.

  Local Notation mor s d := (sigT_type (Pmor s d)).
  Context `(HPmor : Πs d, IsHSet (mor s d)).

  Variable Pidentity : Πx, @Pmor x x (@identity A _).
  Variable Pcompose : Πs d d' m1 m2,
                        @Pmor d d' m1
                        → @Pmor s d m2
                        → @Pmor s d' (m1 ∘ m2).

  Local Notation identity x := ⟨@identity A x, @Pidentity x⟩.
  Local Notation compose m1 m2 := (m1.1 ∘ m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Hypothesis P_associativity
  : Πx1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 ≈ compose m3 (compose m2 m1).

  Hypothesis P_left_identity
  : Πa b (f : mor a b),
      compose (identity b) f ≈ f.

  Hypothesis P_right_identity
  : Πa b (f : mor a b),
      compose f (identity a) ≈ f.

  /- definition of [sigT_mor]-precategory -/
  definition sigT_mor : PreCategory.
  /-begin
    refine (@Build_PreCategory
              (object A)
              (λs d, mor s d)
              (λx, identity x)
              (λs d d' m1 m2, compose m1 m2)
              _
              _
              _
              _);
    assumption.
  end-/

  /- First projection functor -/
  definition pr1_mor : Functor sigT_mor A :=
       Build_Functor
         sigT_mor A
         idmap
         (λ_ _, @pr1_type _ _)
         (λ_ _ _ _ _, idpath)
         (λ_, idpath).

  definition sigT_mor_as_sigT : PreCategory.
  /-begin
    refine (@sigT A (λ_, unit) (λs d, @Pmor (pr1_type s) (pr1_type d)) _ (λ_, Pidentity _) (λ_ _ _ _ _ m1 m2, Pcompose m1 m2) _ _ _);
    intros; trivial.
  end-/

  definition sigT_functor_mor : Functor sigT_mor_as_sigT sigT_mor :=
       Build_Functor
         sigT_mor_as_sigT sigT_mor
         (@pr1_type _ _)
         (λ_ _, idmap)
         (λ_ _ _ _ _, idpath)
         (λ_, idpath).

  definition sigT_functor_mor_inv : Functor sigT_mor sigT_mor_as_sigT :=
       Build_Functor
         sigT_mor sigT_mor_as_sigT
         (λx, existT _ x star)
         (λ_ _, idmap)
         (λ_ _ _ _ _, idpath)
         (λ_, idpath).

  Local Open Scope functor_scope.

  definition sigT_mor_eq [H : Funext]
  : sigT_functor_mor ∘ sigT_functor_mor_inv ≈ 1
    /\ sigT_functor_mor_inv ∘ sigT_functor_mor ≈ 1.
  /-begin
    split; path_functor; simpl; trivial.
    refine (existT
              _
              (path_forall
                 _
                 _
                 (fun x
                  => match x as x return ⟨x.1, star⟩ ≈ x with
                       | ⟨_, star⟩ => idpath
                     end))
              _).
    repeat ⟨apply path_forall, intro⟩.
    destruct_head @sigT_type.
    destruct_head unit.
    rewrite !transport_forall_constant.
    transport_path_forall_hammer.
    reflexivity.
  Qed.

  definition sigT_mor_compat : pr1_mor ∘ sigT_functor_mor ≈ dpr1 :=
       idpath.
End sigT_mor.

Arguments pr1_mor {A Pmor _ Pidentity Pcompose P_associativity P_left_identity P_right_identity}.

section sigT_mor_hProp
  Variable A : PreCategory.
  Variable Pmor : Πs d, morphism A s d → Type.

  Local Notation mor s d := (sigT_type (Pmor s d)).
  Context `(HPmor : Πs d m, is_hprop (Pmor s d m)).

  Variable Pidentity : Πx, @Pmor x x (@identity A _).
  Variable Pcompose : Πs d d' m1 m2,
                        @Pmor d d' m1
                        → @Pmor s d m2
                        → @Pmor s d' (m1 ∘ m2).

  Local Notation identity x := ⟨@identity A x, @Pidentity x⟩.
  Local Notation compose m1 m2 := (m1.1 ∘ m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Local Ltac t ex_tac :=
    intros;
    simpl;
    apply path_sigma_uncurried;
    simpl;
    ex_tac;
    apply path_ishprop.

  Let P_associativity
  : Πx1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 ≈ compose m3 (compose m2 m1).
  Proof.
    abstract t ltac:(exists (associativity _ _ _ _ _ _ _ _))
      using P_associativity_on_morphisms_subproof.
  end-/

  Let P_left_identity
  : Πa b (f : mor a b),
      compose (identity b) f ≈ f.
  /-begin
    clear P_associativity.
    abstract t ltac:(exists (left_identity _ _ _ _))
      using P_left_identity_on_morphisms_subproof.
  end-/

  Let P_right_identity
  : Πa b (f : mor a b),
      compose f (identity a) ≈ f.
  /-begin
    clear P_associativity P_left_identity.
    abstract t ltac:(exists (right_identity _ _ _ _))
      using P_right_identity_on_morphisms_subproof.
  end-/

  /- definition of [sig_mor]-precategory -/
  definition sig_mor : PreCategory :=
       Eval cbv delta [P_associativity P_left_identity P_right_identity]
      in @sigT_mor A Pmor _ Pidentity Pcompose P_associativity P_left_identity P_right_identity.

  /- First projection functor -/
  definition proj1_sig_mor : Functor sig_mor A :=
       pr1_mor.
End sigT_mor_hProp.

Arguments proj1_sig_mor {A Pmor HPmor Pidentity Pcompose}.
