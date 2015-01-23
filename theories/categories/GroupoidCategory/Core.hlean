/- Groupoids -/
Require Import Category.Core Category.Morphisms Category.Strict.
Require Import Trunc Types.ΠPathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope category_scope.

/- A groupoid is a precategory where every morphism is an isomorphism.  Since 1-types are 1-groupoids, we can construct the category corresponding to the 1-groupoid of a 1-type. -/

/- definition of what it means to be a groupoid -/
Class IsGroupoid (C : PreCategory) :=
     isgroupoid : Πs d (m : morphism C s d),
                    IsIsomorphism m.

definition trunc_isgroupoid [instance] [H : funext] C : is_hprop (IsGroupoid C) :=
     trunc_forall.

/- We don't want access to all of the internals of a groupoid category at top level. -/
Module GroupoidCategoryInternals.
  section groupoid_category
    Variable X : Type.
    Context [H : is_trunc 1 X].

    Local Notation morphism := (@paths X).

    definition compose s d d' (m : morphism d d') (m' : morphism s d)
    : morphism s d' :=
         transitivity m' m.

    definition identity x : morphism x x :=
         reflexivity _.

    Global Arguments compose [s d d'] m m' / .
    Global Arguments identity x / .
  End groupoid_category.
End GroupoidCategoryInternals.

/- Categorification of the groupoid of a 1-type -/
definition groupoid_category X [H : is_trunc 1 X] : PreCategory.
/-begin
  refine (@Build_PreCategory X
                             (@paths X)
                             (@GroupoidCategoryInternals.identity X)
                             (@GroupoidCategoryInternals.compose X)
                             _
                             _
                             _
                             _);
  simpl; intros; path_induction; reflexivity.
end-/

Arguments groupoid_category X {_}.

definition isgroupoid_groupoid_category [instance] X [H : is_trunc 1 X]
: IsGroupoid (groupoid_category X).
 /-begin
  intros s d m; simpl in *.
  exact (Build_IsIsomorphism
           (groupoid_category X)
           s d
           m m⁻¹%path
           (concat_pV m)
           (concat_Vp m)).
end-/

/- 0-types give rise to strict (groupoid) categories -/
definition isstrict_groupoid_category X [H : IsHSet X]
: IsStrictCategory (groupoid_category X).
/-begin
  typeclasses eauto.
end-/
