/- Functors involving coproduct categories -/
Require Import Category.Sum Functor.Core Functor.Composition.Core Functor.Identity.
Require Import Functor.Paths HoTT.Tactics Types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

/- We save [inl] and [inr] so we can use them to refer to the functors, too.  Outside of the [categories/] directory, they should always be referred to as [Functor.inl] and [Functor.inr], after a [Require Functor].  Outside of this file, but in the [categories/] directory, if you do not want to depend on all of [Functor] (for e.g., speed reasons), they should be referred to as [Functor.Sum.inl] and [Functor.Sum.inr] after a [Require Functor.Sum]. -/
Local Notation type_inl := inl.
Local Notation type_inr := inr.

/- Injections [inl : C → C + D] and [inr : D → C + D] -/
section sum_functors
  Variable C : PreCategory.
  Variable D : PreCategory.

  definition inl : Functor C (C + D) :=
       Build_Functor C (C + D)
                     (@inl _ _)
                     (λ_ _ m, m)
                     (λ_ _ _ _ _, idpath)
                     (λ_, idpath).

  definition inr : Functor D (C + D) :=
       Build_Functor D (C + D)
                     (@inr _ _)
                     (λ_ _ m, m)
                     (λ_ _ _ _ _, idpath)
                     (λ_, idpath).
End sum_functors.

/- Coproduct of functors [F + F' : C + C' → D] -/
section sum
  Variable C : PreCategory.
  Variable C' : PreCategory.
  Variable D : PreCategory.

  definition sum (F : Functor C D) (F' : Functor C' D)
  : Functor (C + C') D.
  /-begin
    refine (Build_Functor
              (C + C') D
              (fun cc'
               => match cc' with
                    | type_inl c => F c
                    | type_inr c' => F' c'
                  end)
              (fun s d
               => match s, d with
                    | type_inl cs, type_inl cd
                      => morphism_of F (s := cs) (d := cd)
                    | type_inr c's, type_inr c'd
                      => morphism_of F' (s := c's) (d := c'd)
                    | _, _ => λm, match m with end
                  end)
              _
              _);
    abstract (
        repeat (intros [] || intro);
        simpl in *;
          auto with functor
      ).
  end-/
End sum.

/- swap : [C + D → D + C] -/
section swap_functor
  definition swap C D
  : Functor (C + D) (D + C) :=
       sum (inr _ _) (inl _ _).

  Local Open Scope functor_scope.

  definition swap_involutive_helper {C D} c
  : (swap C D) ((swap D C) c)
    ≈ c :=
       match c with type_inl _ => idpath | type_inr _ => idpath end.

  definition swap_involutive [H : Funext] C D
  : swap C D ∘ swap D C ≈ 1.
  Proof.
    path_functor.
    exists (path_Π_ _ swap_involutive_helper).
    repeat (apply (@path_Π_); intro).
    repeat match goal with
               | [ |- context[transport (λx, Πy, @?C x y) ?p ?f ?x] ]
                 => simpl rewrite (@transport_forall_constant _ _ C _ _ p f x)
           end.
    transport_path_forall_hammer.
      by repeat match goal with
                  | [ H : Empty |- _ ] => destruct H
                  | [ H : (_ + _)%type |- _ ] => destruct H
                  | _ => progress hnf in *
                end.
  Qed.
End swap_functor.

Module Export FunctorSumNotations.
  Notation "F + G" := (sum F G) : functor_scope.
End FunctorSumNotations.
