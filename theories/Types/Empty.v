/- -*- mode: coq; mode: visual-line -*- -/
/- Theorems about the empty type -/

Require Import HoTT.Basics.
Local Open Scope path_scope.

/- Unpacking -/
/- Eta conversion -/
/- Paths -/
/- Transport -/
/- Functorial action -/
/- Equivalences -/
/- Universal mapping properties -/

definition contr_from_Empty [instance] {_ : Funext} (A : Type) :
  is_contr (Empty → A) :=
  BuildContr _
             (Empty_ind (λ_, A))
             (λf, path_Π_ f (λx, Empty_ind _ x)).

/- Behavior with respect to truncation -/

definition hprop_Empty [instance] : is_hprop Empty.
/-begin intro x. destruct x. end-/

Lemma Empty_rec {T : Type} (falso: Empty) : T.
/-begin case falso. end-/

definition all_to_empty_isequiv [instance] (T : Type) (f : T → Empty) : IsEquiv f.
/-begin
  refine (BuildIsEquiv _ _ _ 
    (Empty_ind (λ_, T))                /- := equiv_inf -/
    (λfals:Empty, match fals with end) /- : Sect equiv_inf f -/
    (λt:T, match (f t) with end)       /- : Sect f equiv_inf -/
    (_)                                     /- adjointify part -/  ).
  intro t. 
  exact (Empty_rec (f t)).
end-/

/- Paths -/

/- We could probably prove some theorems about non-existing paths in
   [Empty], but this is really quite useless. As soon as an element
   of [Empty] is hypothesized, we can prove whatever we like with
   a simple elimination. -/
