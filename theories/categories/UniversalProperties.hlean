/- Universal morphisms -/
Require Import Category.Core Functor.Core.
Require Import Category.Dual Functor.Dual.
Require Import Category.Objects Category.Morphisms.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors.
Require Import Comma.Core.
Require Import Types.unit Trunc Types.Sigma HProp HoTT.Tactics Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

section UniversalMorphism
  /- Quoting Wikipedia:

      Suppose that [U : D → C] is a functor from a category [D] to a
      category [C], and let [X] be an object of [C].  Consider the
      following dual (opposite) notions: -/

  Local Ltac univ_hprop_t UniversalProperty :=
    apply @trunc_succ in UniversalProperty;
    eapply @trunc_sigma;
    first [ intro;
            simpl;
            match goal with
              | [ |- context[?m ∘ 1] ]
                => simpl rewrite (right_identity _ _ _ m)
              | [ |- context[1 ∘ ?m] ]
                => simpl rewrite (left_identity _ _ _ m)
            end;
            assumption
          | by typeclasses eauto ].

  /- Initial morphisms -/
  section InitialMorphism
    /- definition -/
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable X : C.
    Variable U : Functor D C.
    /- An initial morphism from [X] to [U] is an initial object in
        the category [(X ↓ U)] of morphisms from [X] to [U].  In other
        words, it consists of a pair [(A, φ)] where [A] is an object
        of [D] and [φ: X → U A] is a morphism in [C], such that the
        following initial property is satisfied:

       - Whenever [Y] is an object of [D] and [f : X → U Y] is a
         morphism in [C], then there exists a unique morphism [g : A
         → Y] such that the following diagram commutes:

<<
             φ
         X -----> U A       A
          \        .        .
            \      . U g    . g
           f  \    .        .
               ↘   ↓        ↓
                 U Y        Y
>>
       -/

    definition IsInitialMorphism (Ap : object (X / U)) :=
      IsInitialObject (X / U) Ap.

    /- Introduction rule -/
    section IntroductionAbstractionBarrier
      definition Build_IsInitialMorphism
                 (*(Ap : Object (X ↓ U))*)
                 (A : D)/- := CCO_b Ap-/
                 (p : morphism C X (U A))(*:= CCO_f Ap*)
                 (Ap := CommaCategory.Build_object !X U star A p)
                 (UniversalProperty
                  : Π(A' : D) (p' : morphism C X (U A')),
                      is_contr { m : morphism D A A'
                            | morphism_of U m ∘ p = p' })
      : IsInitialMorphism Ap.
      /-begin
        intro x.
        specialize (UniversalProperty (CommaCategory.b x) (CommaCategory.f x)).
        /- We want to preserve the computation rules for the morphisms, even though they're unique up to unique isomorphism. -/
        eapply trunc_equiv'.
        apply CommaCategory.issig_morphism.
        apply contr_inhabited_hprop.
        - abstract univ_hprop_t UniversalProperty.
        - (exists star).
          (exists (@center _ UniversalProperty).1).
          abstract (progress rewrite ?right_identity, ?left_identity;
                    exact (@center _ UniversalProperty).2).
      end-/

      definition Build_IsInitialMorphism_curried
                 (A : D)
                 (p : morphism C X (U A))
                 (Ap := CommaCategory.Build_object !X U star A p)
                 (m : Π(A' : D) (p' : morphism C X (U A')),
                        morphism D A A')
                 (H : Π(A' : D) (p' : morphism C X (U A')),
                        morphism_of U (m A' p') ∘ p = p')
                 (H' : Π(A' : D) (p' : morphism C X (U A')) m',
                         morphism_of U m' ∘ p = p'
                         → m A' p' = m')
      : IsInitialMorphism Ap :=
           Build_IsInitialMorphism
             A
             p
             (λA' p',
                {| center := ⟨m A' p', H A' p'⟩;
                   contr m' := path_sigma
                                 _
                                 ⟨m A' p', H A' p'⟩
                                 m'
                                 (H' A' p' m'.1 m'.2)
                                 (center _) |}).

      /- Projections from nested sigmas are currently rather slow.  We should just be able to do

<<
      definition Build_IsInitialMorphism_uncurried
                 (univ
                  : { A : D
                    | { p : morphism C X (U A)
                       | let Ap := CommaCategory.Build_object !X U star A p in
                         Π(A' : D) (p' : morphism C X (U A')),
                           { m : morphism D A A'
                           | { H : morphism_of U m ∘ p = p'
                             | Πm',
                                 morphism_of U m' ∘ p = p'
                                 → m = m' }}}}) :=
           @Build_IsInitialMorphism_curried
             (univ.1)
             (univ.2.1)
             (λA' p', (univ.2.2 A' p').1)
             (λA' p', (univ.2.2 A' p').2.1)
             (λA' p', (univ.2.2 A' p').2.2).
>>

      But that's currently too slow.  (About 6-8 seconds, on my machine.)  So instead we factor out all of the type parts by hand, and then apply them after. -/

      Let make_uncurried A' B' C' D' E'0
          (E'1 : Πa a' b b' (c : C' a a'), D' a a' b b' c → E'0 a a' → Type)
          (E' : Πa a' b b' (c : C' a a'), D' a a' b b' c → E'0 a a' → Type)
          F'
          (f : Π(a : A')
                      (b : B' a)
                      (c : Π(a' : A') (b' : B' a'),
                             C' a a')
                      (d : Π(a' : A') (b' : B' a'),
                             D' a a' b b' (c a' b'))
                      (e : Π(a' : A') (b' : B' a')
                                  (e0 : E'0 a a')
                                  (e1 : E'1 a a' b b' (c a' b') (d a' b') e0),
                             E' a a' b b' (c a' b') (d a' b') e0),
                 F' a b)
          (univ
           : { a : A'
             | { b : B' a
               | Π(a' : A') (b' : B' a'),
                   { c : C' a a'
                   | { d : D' a a' b b' c
                     | Π(e0 : E'0 a a')
                              (e1 : E'1 a a' b b' c d e0),
                         E' a a' b b' c d e0 }}}})
      : F' univ.1 univ.2.1 :=
           f
             (univ.1)
             (univ.2.1)
             (λA' p', (univ.2.2 A' p').1)
             (λA' p', (univ.2.2 A' p').2.1)
             (λA' p', (univ.2.2 A' p').2.2).

      definition Build_IsInitialMorphism_uncurried
      : Π(univ
                : { A : D
                  | { p : morphism C X (U A)
                    | let Ap := CommaCategory.Build_object !X U star A p in
                      Π(A' : D) (p' : morphism C X (U A')),
                        { m : morphism D A A'
                        | { H : morphism_of U m ∘ p = p'
                          | Πm',
                              morphism_of U m' ∘ p = p'
                              → m = m' }}}}),
          IsInitialMorphism (CommaCategory.Build_object !X U star univ.1 univ.2.1) :=
           @make_uncurried
             _ _ _ _ _ _ _ _
             (@Build_IsInitialMorphism_curried).
    End IntroductionAbstractionBarrier.

    Global Arguments Build_IsInitialMorphism : simpl never.
    Global Arguments Build_IsInitialMorphism_curried : simpl never.
    Global Arguments Build_IsInitialMorphism_uncurried : simpl never.

    /- Elimination rule -/
    section EliminationAbstractionBarrier
      Variable Ap : object (X / U).

      definition IsInitialMorphism_object (M : IsInitialMorphism Ap) : D :=
           CommaCategory.b Ap.
      definition IsInitialMorphism_morphism (M : IsInitialMorphism Ap)
      : morphism C X (U (IsInitialMorphism_object M)) :=
           CommaCategory.f Ap.
      definition IsInitialMorphism_property_morphism (M : IsInitialMorphism Ap)
                 (Y : D) (f : morphism C X (U Y))
      : morphism D (IsInitialMorphism_object M) Y :=
           CommaCategory.h
             (@center _ (M (CommaCategory.Build_object !X U star Y f))).
      definition IsInitialMorphism_property_morphism_property
                 (M : IsInitialMorphism Ap)
                 (Y : D) (f : morphism C X (U Y))
      : (morphism_of U (IsInitialMorphism_property_morphism M Y f))
          ∘ IsInitialMorphism_morphism M = f :=
           concat
             (CommaCategory.p
                (@center _ (M (CommaCategory.Build_object !X U star Y f))))
             (right_identity _ _ _ _).
      definition IsInitialMorphism_property_morphism_unique
                 (M : IsInitialMorphism Ap)
                 (Y : D) (f : morphism C X (U Y))
                 m'
                 (H : morphism_of U m' ∘ IsInitialMorphism_morphism M = f)
      : IsInitialMorphism_property_morphism M Y f = m' :=
           ap
             (@CommaCategory.h _ _ _ _ _ _ _)
             (@contr _
                     (M (CommaCategory.Build_object !X U star Y f))
                     (CommaCategory.Build_morphism
                        Ap (CommaCategory.Build_object !X U star Y f)
                        star m' (H ⬝ (right_identity _ _ _ _)⁻¹)%path)).
      definition IsInitialMorphism_property
                 (M : IsInitialMorphism Ap)
                 (Y : D) (f : morphism C X (U Y))
      : is_contr { m : morphism D (IsInitialMorphism_object M) Y
              | morphism_of U m ∘ IsInitialMorphism_morphism M = f } :=
           {| center := (IsInitialMorphism_property_morphism M Y f;
                         IsInitialMorphism_property_morphism_property M Y f);
              contr m' := path_sigma
                            _
                            (IsInitialMorphism_property_morphism M Y f;
                             IsInitialMorphism_property_morphism_property M Y f)
                            m'
                            (@IsInitialMorphism_property_morphism_unique M Y f m'.1 m'.2)
                            (center _) |}.
    End EliminationAbstractionBarrier.

    Global Arguments IsInitialMorphism_object : simpl never.
    Global Arguments IsInitialMorphism_morphism : simpl never.
    Global Arguments IsInitialMorphism_property : simpl never.
    Global Arguments IsInitialMorphism_property_morphism : simpl never.
    Global Arguments IsInitialMorphism_property_morphism_property : simpl never.
    Global Arguments IsInitialMorphism_property_morphism_unique : simpl never.
  End InitialMorphism.

  /- Terminal morphisms -/
  section TerminalMorphism
    /- definition -/
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable U : Functor D C.
    Variable X : C.
    /- A terminal morphism from [U] to [X] is a terminal object in
       the comma category [(U ↓ X)] of morphisms from [U] to [X].  In
       other words, it consists of a pair [(A, φ)] where [A] is an
       object of [D] and [φ : U A → X] is a morphism in [C], such
       that the following terminal property is satisfied:

       - Whenever [Y] is an object of [D] and [f : U Y → X] is a
         morphism in [C], then there exists a unique morphism [g : Y
         → A] such that the following diagram commutes:

<<
         Y      U Y
         .       . \
       g .   U g .   \  f
         .       .     \
         ↓       ↓       ↘
         A      U A -----> X
                      φ
>>
       -/
    Local Notation op_object Ap :=
         (CommaCategory.Build_object
            (Functors.from_terminal C⁻¹op X) (U⁻¹op)
            (CommaCategory.b (Ap : object (U / X)))
            (CommaCategory.a (Ap : object (U / X)))
            (CommaCategory.f (Ap : object (U / X)))
          : object ((X : object C⁻¹op) / U⁻¹op)).

    definition IsTerminalMorphism (Ap : object (U / X)) : Type :=
         @IsInitialMorphism
           (C⁻¹op)
           _
           X
           (U⁻¹op)
           (op_object Ap).

    /- Introduction rule -/
    section IntroductionAbstractionBarrier
      definition Build_IsTerminalMorphism
      : forall
          (*(Ap : Object (U ↓ X))*)
          (A : D)/- := CommaCategory.a Ap-/
          (p : morphism C (U A) X)(*:= CommaCategory.f Ap*)
          (Ap := CommaCategory.Build_object U !X A star p)
          (UniversalProperty
           : Π(A' : D) (p' : morphism C (U A') X),
               is_contr { m : morphism D A' A
                     | p ∘ morphism_of U m = p' }),
          IsTerminalMorphism Ap :=
           @Build_IsInitialMorphism
             (C⁻¹op)
             (D⁻¹op)
             X
             (U⁻¹op).

      definition Build_IsTerminalMorphism_curried
      : forall
          (A : D)
          (p : morphism C (U A) X)
          (Ap := CommaCategory.Build_object U !X A star p)
          (m : Π(A' : D) (p' : morphism C (U A') X),
                 morphism D A' A)
          (H : Π(A' : D) (p' : morphism C (U A') X),
                 p ∘ morphism_of U (m A' p') = p')
          (H' : Π(A' : D) (p' : morphism C (U A') X) m',
                  p ∘ morphism_of U m' = p'
                  → m A' p' = m'),
          IsTerminalMorphism Ap :=
           @Build_IsInitialMorphism_curried
             (C⁻¹op)
             (D⁻¹op)
             X
             (U⁻¹op).

      definition Build_IsTerminalMorphism_uncurried
      : forall
          (univ : { A : D
                  | { p : morphism C (U A) X
                    | let Ap := CommaCategory.Build_object U !X A star p in
                      Π(A' : D) (p' : morphism C (U A') X),
                        { m : morphism D A' A
                        | { H : p ∘ morphism_of U m = p'
                          | Πm',
                              p ∘ morphism_of U m' = p'
                              → m = m' }}}}),
          IsTerminalMorphism (CommaCategory.Build_object U !X univ.1 star univ.2.1) :=
           @Build_IsInitialMorphism_uncurried
             (C⁻¹op)
             (D⁻¹op)
             X
             (U⁻¹op).
    End IntroductionAbstractionBarrier.

    /- Elimination rule -/
    section EliminationAbstractionBarrier
      Variable Ap : object (U / X).
      Variable M : IsTerminalMorphism Ap.

      definition IsTerminalMorphism_object : D :=
        @IsInitialMorphism_object C⁻¹op D⁻¹op X U⁻¹op (op_object Ap) M.
      definition IsTerminalMorphism_morphism
      : morphism C (U IsTerminalMorphism_object) X :=
           @IsInitialMorphism_morphism C⁻¹op D⁻¹op X U⁻¹op (op_object Ap) M.
      definition IsTerminalMorphism_property
      : Π(Y : D) (f : morphism C (U Y) X),
          is_contr { m : morphism D Y IsTerminalMorphism_object
                | IsTerminalMorphism_morphism ∘ morphism_of U m = f } :=
           @IsInitialMorphism_property C⁻¹op D⁻¹op X U⁻¹op (op_object Ap) M.
      definition IsTerminalMorphism_property_morphism
      : Π(Y : D) (f : morphism C (U Y) X),
          morphism D Y IsTerminalMorphism_object :=
           @IsInitialMorphism_property_morphism
             C⁻¹op D⁻¹op X U⁻¹op (op_object Ap) M.
      definition IsTerminalMorphism_property_morphism_property
      : Π(Y : D) (f : morphism C (U Y) X),
          IsTerminalMorphism_morphism
            ∘ (morphism_of U (IsTerminalMorphism_property_morphism Y f))
          = f :=
           @IsInitialMorphism_property_morphism_property
             C⁻¹op D⁻¹op X U⁻¹op (op_object Ap) M.
      definition IsTerminalMorphism_property_morphism_unique
      : Π(Y : D) (f : morphism C (U Y) X)
               m'
               (H : IsTerminalMorphism_morphism ∘ morphism_of U m' = f),
          IsTerminalMorphism_property_morphism Y f = m' :=
           @IsInitialMorphism_property_morphism_unique
             C⁻¹op D⁻¹op X U⁻¹op (op_object Ap) M.
    End EliminationAbstractionBarrier.
  End TerminalMorphism.

  section UniversalMorphism
    /- The term universal morphism refers either to an initial
        morphism or a terminal morphism, and the term universal
        property refers either to an initial property or a terminal
        property.  In each definition, the existence of the morphism
        [g] intuitively expresses the fact that [(A, φ)] is ``general
        enough'', while the uniqueness of the morphism ensures that
        [(A, φ)] is ``not too general''.  -/
  End UniversalMorphism.
End UniversalMorphism.

Arguments Build_IsInitialMorphism [C D] X U A p UniversalProperty _.
Arguments Build_IsTerminalMorphism [C D] U X A p UniversalProperty _.
