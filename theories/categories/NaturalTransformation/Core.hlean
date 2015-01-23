/- definition of natural transformation -/
Require Import Category.Core Functor.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Delimit Scope natural_transformation_scope with natural_transformation.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

section NaturalTransformation
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of functors is known as a natural transformation. Namely,
     given two functors [F : C → D], [G : C → D], a natural
     transformation [T: F → G] is a collection of maps [T A : F A ->
     G A], one for each object [A] of [C], such that [(T B) ∘ (F m) =
     (G m) ∘ (T A)] for every map [m : A → B] of [C]; that is, the
     following diagram is commutative:

<<
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    G m     V
     G A --------> G B
>>
     **)

  Record NaturalTransformation :=
    Build_NaturalTransformation' {
        components_of :> Πc, morphism D (F c) (G c);
        commutes : Πs d (m : morphism C s d),
                     components_of d ∘ F _1 m = G _1 m ∘ components_of s;
        /- We require the following symmetrized version so that for eta-expanded [T], we have [(T⁻¹op)⁻¹op = T] judgementally. -/
        commutes_sym : Πs d (m : C.(morphism) s d),
                         G _1 m ∘ components_of s = components_of d ∘ F _1 m
      }.

  definition Build_NaturalTransformation CO COM :=
       Build_NaturalTransformation'
         CO
         COM
         (λ_ _ _, apply symmetry._ _ (COM _ _ _)).
End NaturalTransformation.

Bind Scope natural_transformation_scope with NaturalTransformation.

Create HintDb natural_transformation discriminated.

Global Arguments components_of {C D}%category {F G}%functor T%natural_transformation /
          c%object : rename.
Global Arguments commutes {C D F G} !T / _ _ _ : rename.
Global Arguments commutes_sym {C D F G} !T / _ _ _ : rename.

Hint Resolve @commutes : category natural_transformation.

/- Helper lemmas -/
/- Some helper lemmas for rewriting.  In the names, [p] stands for a
    morphism, [T] for natural transformation, and [F] for functor. -/
definition commutes_pT_F C D (F G : Functor C D) (T : NaturalTransformation F G)
      s d d' (m : morphism C s d) (m' : morphism D _ d')
: (m' ∘ T d) ∘ F _1 m = (m' ∘ G _1 m) ∘ T s :=
     ((Category.Core.associativity _ _ _ _ _ _ _ _)
        ⬝ ap _ (commutes _ _ _ _)
        ⬝ (Category.Core.associativity_sym _ _ _ _ _ _ _ _))%path.

definition commutes_T_Fp C D (F G : Functor C D) (T : NaturalTransformation F G)
      s d d' (m : morphism C s d) (m' : morphism D d' _)
: T d ∘ (F _1 m ∘ m') = G _1 m ∘ (T s ∘ m') :=
     ((Category.Core.associativity_sym _ _ _ _ _ _ _ _)
        ⬝ ap10 (ap _ (commutes _ _ _ _)) _
        ⬝ (Category.Core.associativity _ _ _ _ _ _ _ _))%path.
