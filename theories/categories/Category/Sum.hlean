/- The coproduct of categories -/
Require Export Category.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

/- definition of [+] for categories -/
section internals
  Variable C : PreCategory.
  Variable D : PreCategory.

  definition sum_morphism (s d : C + D) : Type :=
       match s, d with
         | inl s, inl d => morphism C s d
         | inr s, inr d => morphism D s d
         | _, _ => Empty
       end.

  Global Arguments sum_morphism _ _ / .

  definition sum_identity (x : C + D) : sum_morphism x x :=
       match x with
         | inl x => identity x
         | inr x => identity x
       end.

  Global Arguments sum_identity _ / .

  definition sum_compose (s d d' : C + D)
             (m1 : sum_morphism d d') (m2 : sum_morphism s d)
  : sum_morphism s d'.
  /-begin
    case s, d, d'; simpl in *;
    solve [ case m1
          | case m2
          | eapply compose; eassumption ].
  end-/

  Global Arguments sum_compose [_ _ _] _ _ / .
End internals.

definition sum (C D : PreCategory) : PreCategory.
/-begin
  refine (@Build_PreCategory
            (C + D)%type
            (sum_morphism C D)
            (sum_identity C D)
            (sum_compose C D)
            _
            _
            _
            _);
  abstract (
      repeat (simpl || intros [] || intro);
      auto with morphism;
      typeclasses eauto
    ).
end-/

Module Export CategorySumNotations.
  Infix "+" := sum : category_scope.
End CategorySumNotations.
