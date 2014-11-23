/- Representable profunctors -/
Require Import Category.Core Functor.Core Category.Prod Category.Dual Functor.Prod.Core SetCategory.Core Profunctor.Core Functor.Dual Profunctor.Identity Functor.Composition.Core Functor.Identity.
Require Import HSet.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.
Local Open Scope profunctor_scope.

section representable
  /- Quoting nCatLab on profunctors:

      Every functor [f : C → D] induces two profunctors [D(1, f) : C ⇸ D] and [D(f, 1) : D ⇸ C], defined by [D(1, f)(d, c) ≈ D(d, f(c))] and [D(f, 1)(c, d) ≈ D(f(c), d)]. These profunctors are called representable (or sometimes one of them is corepresentable). -/

  Context [H : Funext].

  definition representable C D (F : Functor C D) : C -|-> D :=
       1%profunctor ∘ (1, F).

  /- TODO: Is there a define this so that we get proofs by duality about representable functors?  If we had judgemental eta expansion, maybe we could do it as [swap ∘ (representable F⁻¹op)⁻¹op]? -/
  definition corepresentable C D (F : Functor C D) : D -|-> C :=
       1%profunctor ∘ (F⁻¹op, 1).
End representable.
