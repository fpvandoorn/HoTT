Require Import Overture.

/- Universe Levels -/

/- We provide casting definitions for raising universe levels. -/

/- Because we have cumulativity (that [T : U@{i}] gives us [T : U@{j}] when [i < j]), we may define [Lift : U@{i} → U@{j}] to be the identity function with a fancy type; the type says that [i < j]. -/
definition Lift (A : Type@{i}) : Type@{j} :=
     Eval hnf in let enforce_lt := Type@{i} : Type@{j} in A.

definition lift {A} : A → Lift A := λx, x.

definition lower {A} : Lift A → A := λx, x.

definition isequiv_lift [instance] T : IsEquiv (@lift T) :=
     @IsEquiv.mk
       _ _
       (@lift T)
       (@lower T)
       (λ_, idpath)
       (λ_, idpath)
       (λ_, idpath).

/- This version doesn't force strict containment, i.e. it allows the two universes to possibly be the same.  No fancy type is necessary here other than the universe annotations, because of cumulativity. -/

definition Lift' (A : Type@{i}) : Type@{j} := A.

/- However, if we don't give the universes as explicit arguments here, then Coq collapses them. -/
definition lift' {A : Type@{i}} : A → Lift'@{i j} A := λx, x.

definition lower' {A : Type@{i}} : Lift'@{i j} A → A := λx, x.

definition isequiv_lift' [instance] T : IsEquiv (@lift'@{i j} T) :=
     @IsEquiv.mk
       _ _
       (@lift' T)
       (@lower' T)
       (λ_, idpath)
       (λ_, idpath)
       (λ_, idpath).

/- We make [lift] and [lower] opaque so that typeclass resolution doesn't pick up [isequiv_lift] as an instance of [IsEquiv idmap] and wreck havok. -/
Typeclasses Opaque lift lower lift' lower'.

(*Fail Check Lift nat : Type0.
Check 1 : Lift nat.*)
