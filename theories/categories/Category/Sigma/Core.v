/- ∑-categories - exploded Grothendieck constructions, or generalizations of subcategories -/
Require Import Category.Core Functor.Core.
Require Import Basics.Trunc Types.Sigma.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation sigT_type := sigT.

/- We can generalize the notion of [sigT] to categories.  This is, essentially, a type-theoretic perspecitive on the Grothendieck construction. -/

section sigT_obj_mor
  Variable A : PreCategory.
  Variable Pobj : A → Type.

  Local Notation obj := (sigT Pobj).

  Variable Pmor : Πs d : obj, morphism A s.1 d.1 → Type.

  Local Notation mor s d := (sigT (Pmor s d)).
  Context `(HPmor : Πs d, IsHSet (mor s d)).

  Variable Pidentity : Πx, @Pmor x x (@identity A _).
  Variable Pcompose : Πs d d' m1 m2,
                        @Pmor d d' m1
                        → @Pmor s d m2
                        → @Pmor s d' (m1 ∘ m2).

  Local Notation identity x := ⟨@identity A x.1, @Pidentity x⟩.
  Local Notation compose m1 m2 := (m1.1 ∘ m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Hypothesis P_associativity
  : Πx1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 ≈ compose m3 (compose m2 m1).

  Hypothesis P_LeftIdentity
  : Πa b (f : mor a b),
      compose (identity b) f ≈ f.

  Hypothesis P_RightIdentity
  : Πa b (f : mor a b),
      compose f (identity a) ≈ f.

  /- definition of a [sigT]-precategory -/
  definition sigT : PreCategory.
  /-begin
    refine (@Build_PreCategory
              obj
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
  definition dpr1 : Functor sigT A :=
       Build_Functor
         sigT A
         (@dpr1 _ _)
         (λ_ _, @dpr1 _ _)
         (λ_ _ _ _ _, idpath)
         (λ_, idpath).
End sigT_obj_mor.

Arguments dpr1 {A Pobj Pmor HPmor Pidentity Pcompose P_associativity P_LeftIdentity P_RightIdentity}.

/- Variant of [sigT]-precategory when we are taking a subset of morphisms -/
section sigT_obj_mor_hProp
  Variable A : PreCategory.
  Variable Pobj : A → Type.

  Local Notation obj := (sigT_type Pobj).

  Variable Pmor : Πs d : obj, morphism A s.1 d.1 → Type.

  Local Notation mor s d := (sigT_type (Pmor s d)).
  Context `(HPmor : Πs d m, is_hprop (Pmor s d m)).

  Variable Pidentity : Πx, @Pmor x x (@identity A _).
  Variable Pcompose : Πs d d' m1 m2,
                        @Pmor d d' m1
                        → @Pmor s d m2
                        → @Pmor s d' (m1 ∘ m2).

  Local Notation identity x := ⟨@identity A x.1, @Pidentity x⟩.
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
  /-begin
    abstract t ltac:(exists (associativity _ _ _ _ _ _ _ _))
      using P_associativity_core_subproof.
  end-/

  Let P_left_identity
  : Πa b (f : mor a b),
      compose (identity b) f ≈ f.
  /-begin
    clear P_associativity.
    abstract t ltac:(exists (left_identity _ _ _ _))
      using P_left_identity_core_subproof.
  end-/

  Let P_right_identity
  : Πa b (f : mor a b),
      compose f (identity a) ≈ f.
  /-begin
    clear P_associativity P_left_identity.
    abstract t ltac:(exists (right_identity _ _ _ _))
      using P_right_identity_core_subproof.
  end-/

  /- definition of [sig]-precategory -/
  definition sig : PreCategory :=
       Eval cbv delta [P_associativity P_left_identity P_right_identity]
      in @sigT A Pobj Pmor _ Pidentity Pcompose P_associativity P_left_identity P_right_identity.

  /- First projection functor -/
  definition proj1_sig : Functor sig A :=
       dpr1.
End sigT_obj_mor_hProp.

Arguments proj1_sig {A Pobj Pmor HPmor Pidentity Pcompose}.

Notation subcategory := sig.
