/- -*- mode: coq; mode: visual-line -*- -/

Require Import HoTT.Basics HoTT.Types.
Require Import HProp HSet.
Require Import hit.Pushout.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

/- Joins -/

/- The join is the pushout of two types under their product. -/
section Join

  Context (A B : Type).

  definition join := pushout (@pr1 A B) (@pr2 A B).

  definition joinpp := @pp (A*B) A B pr1 snd.

  /- Joining with a contractible type produces a contractible type -/
  definition contr_join [instance] [H : is_contr A] : is_contr join.
  /-begin
    exists (push (inl (center A))).
    intros y; refine (pushout_ind _ _ _ _ _ y).
    - intros [a | b].
      × apply ap, ap, contr.
      × exact (pp (center A , b)).
    - intros [a b]. cbn.
      refine (_ ⬝ apD (λa', joinpp (a',b)) (contr a)⁻¹).
      rewrite transport_paths_r, transport_paths_FlFr.
      rewrite ap_V, inv_V, concat_pp_p.
      unfold pushl, pushr; simpl.
      rewrite <- ap_compose; unfold compose, joinpp.
      rewrite ap_const, concat_p1.
      reflexivity.
  end-/

End Join.
