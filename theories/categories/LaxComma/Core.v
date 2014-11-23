/- Lax Comma Category -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Pseudofunctors.
Require Import Cat.Core.
Require Functor.Identity.
Require Pseudofunctor.Identity.
Require Import Category.Strict.
Require Import Functor.Composition.Core.
Require Import NaturalTransformation.Paths NaturalTransformation.Composition.Core.
Require Import Category.Morphisms FunctorCategory.Core.
Require Import Pseudofunctor.Core.
Require Import NaturalTransformation.Composition.Laws.
Require Import FunctorCategory.Morphisms.
Require LaxComma.CoreLaws.
Require Import Types.Record Trunc HoTT.Tactics Types.Paths Types.Sigma.

Import Functor.Identity.FunctorIdentityNotations.
Import Pseudofunctor.Identity.PseudofunctorIdentityNotations.
Import LaxComma.CoreLaws.LaxCommaCategory.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

/- Quoting David Spivak:

    David: ok
       so an object of [FC ⇓ D] is a pair [(X, G)], where [X] is a
       finite category (or a small category or whatever you wanted)
       and [G : X --> D] is a functor.
       a morphism in [FC ⇓ D] is a ``natural transformation diagram''
       (as opposed to a commutative diagram, in which the natural
       transformation would be ``identity'')
       so a map in [FC ⇓ D] from [(X, G)] to [(X', G')] is a pair
       [(F, α)] where [F : X --> X'] is a functor and
       [α : G --> G' ∘ F] is a natural transformation
       and the punchline is that there is a functor
       [colim : FC ⇓ D --> D]

     David: consider for yourself the case where [F : X --> X'] is
       identity ([X ≈ X']) and (separately) the case where
       [α : G --> G ∘ F] is identity.
       the point is, you've already done the work to get this colim
       functor.
       because every map in [FC ⇓ D] can be written as a composition
       of two maps, one where the [F]-part is identity and one where
       the [α]-part is identity.
       and you've worked both of those cases out already.
       -/

/- definition of Lax Comma Category -/
definition lax_comma_category [H : Funext] A B
           (S : Pseudofunctor A) (T : Pseudofunctor B)
           [H : Πa b, IsHSet (Functor (S a) (T b))]
: PreCategory :=
     @Build_PreCategory
       (@object _ _ _ S T)
       (@morphism _ _ _ S T)
       (@identity _ _ _ S T)
       (@compose _ _ _ S T)
       (@associativity _ _ _ S T)
       (@left_identity _ _ _ S T)
       (@right_identity _ _ _ S T)
       _.

definition oplax_comma_category [H : Funext] A B
           (S : Pseudofunctor A) (T : Pseudofunctor B)
           [H : Πa b, IsHSet (Functor (S a) (T b))]
: PreCategory :=
     (lax_comma_category S T)⁻¹op.

definition isstrict_lax_comma_category [instance] [H : Funext] A B
       (S : Pseudofunctor A) (T : Pseudofunctor B)
       [H : IsStrictCategory A, IsStrictCategory B]
       [H : Πa b, IsHSet (Functor (S a) (T b))]
: IsStrictCategory (@lax_comma_category _ A B S T _).
Proof.
  typeclasses eauto.
Qed.

definition isstrict_oplax_comma_category [instance] {fs : Funext} A B S T HA HB H
: IsStrictCategory (@oplax_comma_category fs A B S T H) :=
     @isstrict_lax_comma_category fs A B S T HA HB H.

/- section category
    Context [H : IsCategory A, IsCategory B].
    (*Context [H : Funext]. -/

    definition comma_category_isotoid (x y : comma_category)
    : x ≅ y → x ≈ y.
    Proof.
      intro i.
      destruct i as [i [i' ? ?]].
      hnf in *.
      destruct i, i'.
      simpl in *.


    definition comma_category_IsCategory [instance] [H : IsCategory A, IsCategory B]
    : IsCategory comma_category.
    Proof.
      hnf.
      unfold IsStrictCategory in *.
      typeclasses eauto.
    Qed.
  End category.
 *)

/- definition of Lax (Co)Slice Category -/
section lax_slice_category
  Context [H : Funext].
  Variable A : PreCategory.
  Variable a : PreCategory.
  Variable S : Pseudofunctor A.
  Context [H : Πa0, IsHSet (Functor (S a0) a)].
  Context [H : Πa0, IsHSet (Functor a (S a0))].

  definition lax_slice_category : PreCategory := lax_comma_category S !a.
  definition lax_coslice_category : PreCategory := lax_comma_category !a S.

  definition oplax_slice_category : PreCategory := oplax_comma_category S !a.
  definition oplax_coslice_category : PreCategory := oplax_comma_category !a S.

/- [x ↓ F] is a coslice category; [F ↓ x] is a slice category; [x ↓ F] deals with morphisms [x → F y]; [F ↓ x] has morphisms [F y → x] -/
End lax_slice_category.

Arguments lax_slice_category {_} [A] a S {_}.
Arguments lax_coslice_category {_} [A] a S {_}.
Arguments oplax_slice_category {_} [A] a S {_}.
Arguments oplax_coslice_category {_} [A] a S {_}.

/- definition of Lax (Co)Slice Category Over -/
section lax_slice_category_over
  Context [H : Funext].

  Variable P : PreCategory → Type.
  Context {HF : ΠC D, P C → P D → IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P HF).

  Variable a : PreCategory.
  Context {Πa0 : cat, IsHSet (Functor a0.1 a)}.
  Context {Πa0 : cat, IsHSet (Functor a a0.1)}.

  definition lax_slice_category_over : PreCategory := @lax_slice_category _ cat a (Pseudofunctor.Identity.identity P) _.
  definition lax_coslice_category_over : PreCategory := @lax_coslice_category _ cat a (Pseudofunctor.Identity.identity P) _.
  definition oplax_slice_category_over : PreCategory := @oplax_slice_category _ cat a (Pseudofunctor.Identity.identity P) _.
  definition oplax_coslice_category_over : PreCategory := @oplax_coslice_category _ cat a (Pseudofunctor.Identity.identity P) _.
End lax_slice_category_over.

Arguments lax_slice_category_over {_} P {HF} a {_}.
Arguments lax_coslice_category_over {_} P {HF} a {_}.
Arguments oplax_slice_category_over {_} P {HF} a {_}.
Arguments oplax_coslice_category_over {_} P {HF} a {_}.

/- definition of Lax (Co)Slice Arrow Category -/
section lax_arrow_category
  Context [H : Funext].

  Variable P : PreCategory → Type.
  Context {HF : ΠC D, P C → P D → IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P HF).

  definition lax_arrow_category : PreCategory := @lax_comma_category _ cat cat (Pseudofunctor.Identity.identity P) (Pseudofunctor.Identity.identity P) (λC D, HF C.2 D.2).
  definition oplax_arrow_category : PreCategory := @oplax_comma_category _ cat cat (Pseudofunctor.Identity.identity P) (Pseudofunctor.Identity.identity P) (λC D, HF C.2 D.2).
End lax_arrow_category.

Arguments lax_arrow_category {_} P {_}.
Arguments oplax_arrow_category {_} P {_}.

Module Export LaxCommaCoreNotations.
  /- We play some games to get nice notations for lax comma categories. -/
  section tc_notation_boiler_plate
    Class LCC_Builder {A B C} (x : A) (y : B) (z : C) := lcc_builder_dummy : True.
    definition get_LCC [H : @LCC_Builder A B C x y z] : C := z.

    Global Arguments get_LCC / {A B C} x y {z} {_}.

    definition LCC_comma [instance] [H : Funext] A B
           (S : Pseudofunctor A) (T : Pseudofunctor B)
           {_ : Πa b, IsHSet (Functor (S a) (T b))}
    : LCC_Builder S T (lax_comma_category S T) | 1000 :=
         I.

    definition LCC_slice [instance] [H : Funext] A x (F : Pseudofunctor A)
           [H : Πa0, IsHSet (Functor (F a0) x)]
    : LCC_Builder F x (lax_slice_category x F) | 100 :=
         I.

    definition LCC_coslice [instance] [H : Funext] A x (F : Pseudofunctor A)
           [H : Πa0, IsHSet (Functor x (F a0))]
    : LCC_Builder x F (lax_coslice_category x F) | 100 :=
         I.

    definition LCC_slice_over [instance] [H : Funext]
           P {HF : ΠC D, P C → P D → IsHSet (Functor C D)}
           a
           {Πa0 : @sub_pre_cat _ P HF, IsHSet (Functor a0.1 a)}
    : LCC_Builder a (@sub_pre_cat _ P HF) (@lax_slice_category_over _ P HF a _) | 10 :=
         I.

    definition LCC_coslice_over [instance] [H : Funext]
           P {HF : ΠC D, P C → P D → IsHSet (Functor C D)}
           a
           {Πa0 : @sub_pre_cat _ P HF, IsHSet (Functor a a0.1)}
    : LCC_Builder (@sub_pre_cat _ P HF) a (@lax_coslice_category_over _ P HF a _) | 10 :=
         I.

    Class OLCC_Builder {A B C} (x : A) (y : B) (z : C) := olcc_builder_dummy : True.

    definition get_OLCC [H : @OLCC_Builder A B C x y z] : C := z.

    Global Arguments get_OLCC / {A B C} x y {z} {_}.

    definition OLCC_comma [instance] [H : Funext] A B
           (S : Pseudofunctor A) (T : Pseudofunctor B)
           {_ : Πa b, IsHSet (Functor (S a) (T b))}
    : OLCC_Builder S T (lax_comma_category S T) | 1000 :=
         I.

    definition OLCC_slice [instance] [H : Funext] A x (F : Pseudofunctor A)
           [H : Πa0, IsHSet (Functor (F a0) x)]
    : OLCC_Builder F x (lax_slice_category x F) | 100 :=
         I.

    definition OLCC_coslice [instance] [H : Funext] A x (F : Pseudofunctor A)
           [H : Πa0, IsHSet (Functor x (F a0))]
    : OLCC_Builder x F (lax_coslice_category x F) | 100 :=
         I.

    definition OLCC_slice_over [instance] [H : Funext]
           P {HF : ΠC D, P C → P D → IsHSet (Functor C D)}
           a
           {Πa0 : @sub_pre_cat _ P HF, IsHSet (Functor a0.1 a)}
    : OLCC_Builder a (@sub_pre_cat _ P HF) (@lax_slice_category_over _ P HF a _) | 10 :=
         I.

    definition OLCC_coslice_over [instance] [H : Funext]
           P {HF : ΠC D, P C → P D → IsHSet (Functor C D)}
           a
           {Πa0 : @sub_pre_cat _ P HF, IsHSet (Functor a a0.1)}
    : OLCC_Builder (@sub_pre_cat _ P HF) a (@lax_coslice_category_over _ P HF a _) | 10 :=
         I.
  End tc_notation_boiler_plate.

  /- We really want to use infix [⇓] and [⇑] for lax comma categories, but that's unicode.  Infix [,] might also be reasonable, but I can't seem to get it to work without destroying the [(_, _)] notation for ordered pairs.  So I settle for the ugly ASCII rendition [//] of [⇓] and [\\] for [⇑]. -/
  /- Set some notations for printing -/
  Notation "'CAT' // a" := (@lax_slice_category_over _ _ _ a _) (at level 40, left associativity) : category_scope.
  Notation "a // 'CAT'" := (@lax_coslice_category_over _ _ _ a _) (at level 40, left associativity) : category_scope.
  Notation "x // F" := (lax_coslice_category x F) (at level 40, left associativity) : category_scope.
  Notation "F // x" := (lax_slice_category x F) : category_scope.
  Notation "S // T" := (lax_comma_category S T) : category_scope.
  /- Set the notation for parsing; typeclasses will automatically decide which of the arguments are functors and which are objects, i.e., functors from the terminal category. -/
  Notation "S // T" := (get_LCC S T) : category_scope.

  Notation "'CAT' \\ a" := (@oplax_slice_category_over _ _ _ a _) (at level 40, left associativity) : category_scope.
  Notation "a \\ 'CAT'" := (@oplax_coslice_category_over _ _ _ a _) (at level 40, left associativity) : category_scope.
  Notation "x \\ F" := (oplax_coslice_category x F) (at level 40, left associativity) : category_scope.
  Notation "F \\ x" := (oplax_slice_category x F) : category_scope.
  Notation "S \\ T" := (oplax_comma_category S T) : category_scope.
  /- Set the notation for parsing; typeclasses will automatically decide which of the arguments are functors and which are objects, i.e., functors from the terminal category. -/
  Notation "S \\ T" := (get_OLCC S T) : category_scope.
End LaxCommaCoreNotations.
