/- -*- mode: coq; mode: visual-line -*- -/
/- Pointed Types -/

Require Import Overture.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

/- Allow ourselves to implicitly generalize over types [A] and [B], and a function [f]. -/
Generalizable Variables A B f.

/- Any contratible type is pointed. -/
definition ispointed_contr [instance] [H : is_contr A] : IsPointed A := center A.

/- A pi type with a pointed target is pointed. -/
definition ispointed_pi [instance] {H : Πa : A, IsPointed (B a)}
: IsPointed (Πa, B a) :=
     λa, point (B a).

/- A sigma type of pointed components is pointed. -/
definition ispointed_sigma [instance] [H : IsPointed A] [H : IsPointed (B (point A))]
: IsPointed (sigT B) :=
     (point A; point (B (point A))).

/- A cartesian product of pointed types is pointed. -/
definition ispointed_prod [instance] [H : IsPointed A, IsPointed B] : IsPointed (A × B) :=
     (point A, point B).

/- The type [x = x] is pointed. -/
definition ispointed_loop_space [instance] A (a : A) : IsPointed (a = a) := idpath.

/- We can build an iterated loop space -/
definition loopSpace (A : pointedType) : pointedType :=
  ⟨A.1 = A.1, refl⟩.

Fixpoint iteratedLoopSpace (n : nat) (A : Type) {H : IsPointed A} {struct n} : pointedType :=
     match n with
       | ∘ => existT IsPointed A (@point A H)
       | S p => iteratedLoopSpace p (point = point)
     end.
