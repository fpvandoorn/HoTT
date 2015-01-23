/- Discrete category -/
Require Import Category.Core GroupoidCategory.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

/- A discrete category is a groupoid which is a 0-type -/
Module Export Core.
  definition discrete_category X [H : IsHSet X] := groupoid_category X.

  Arguments discrete_category X {_} / .
End Core.
