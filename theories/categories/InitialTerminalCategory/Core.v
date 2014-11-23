/- Initial and terminal category definitions -/
Require Import Category.Core.
Require Import NatCategory Contractible.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Notation initial_category := (nat_category 0) (only parsing).
Notation terminal_category := (nat_category 1) (only parsing).

/- Terminal categories -/
/- A precategory is terminal if its objects and morphisms are contractible types. -/
Class IsTerminalCategory (C : PreCategory)
      [H : is_contr (object C)]
      [H : Πs d, is_contr (morphism C s d)] := {}.

/- Initial categories -/
/- An initial precategory is one whose objects have the recursion priniciple of the empty type -/
Class IsInitialCategory (C : PreCategory) :=
     initial_category_ind : ΠP : Type, C → P.

definition trunc_initial_category [instance] [H : IsInitialCategory C]
: is_hprop C :=
     λx y, initial_category_ind _ x.
definition trunc_initial_category_mor [instance] [H : IsInitialCategory C] x y
: is_contr (morphism C x y) :=
     initial_category_ind _ x.

/- Default intitial ([0]) and terminal ([1]) precategories. -/
definition is_initial_category_0 [instance] : IsInitialCategory 0 := (λT, @Empty_ind (λ_, T)).
Global Instance: IsTerminalCategory 1 | 0.
Global Instance: is_contr (object 1) | 0 := _.
Global Instance: is_contr (morphism 1 x y) | 0 := λx y, _.
definition default_terminal [instance] C {H H1} : @IsTerminalCategory C H H1 | 10.

Arguments initial_category_ind / .
Arguments is_initial_category_0 / .
