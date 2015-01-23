/- definition of a univalent/saturated precategory, or just "category" -/
Require Import Category.Core Category.Morphisms.
Require Import HoTT.Tactics Trunc.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

/- A category is a precategory for which [idtoiso] is an equivalence. -/

Notation IsCategory C := (Πs d : object C, is_equiv (@idtoiso C s d)).

Notation isotoid C s d := (@equiv_inv _ _ (@idtoiso C s d) _).

/- The objects of a category are a 1-type -/

definition trunc_category [instance] [H : IsCategory C] : is_trunc 1 C | 10000.
Proof.
  intros ? ?.
  eapply trunc_equiv';
  [ apply symmetry.
    esplit;
    apply_hyp
  | ].
  typeclasses eauto.
Qed.

Record Category :=
  {
    precategory_of_category :> PreCategory;
    iscategory_precategory_of_category :> IsCategory precategory_of_category
  }.

Global Existing Instance iscategory_precategory_of_category.
