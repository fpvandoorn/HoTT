Require Import HoTT.Basics.
Require Import Types.Universe.
Require Import HSet UnivalenceImpliesfunext TruncType.
Require Import hit.epi hit.unique_choice hit.Truncations.

Open Local Scope path_scope.
Open Local Scope equiv_scope.

/- We prove that [epi + mono <-> is_equiv] -/
section iso
  Context [H : Univalence].
  Variables X Y : hSet.
  Variable f : X → Y.

  definition atmost1P_isinj (injf : isinj f)
  : Πy : Y, atmost1P (λx, f x = y).
  /-begin
    unfold isinj, atmost1P in *.
    intros.
    apply injf.
    path_induction.
    reflexivity.
  end-/

  definition isequiv_isepi_ismono (epif : isepi f) (monof : ismono f)
  : is_equiv f.
  /-begin
    pose proof (@isepi_issurj _ _ _ f epif) as surjf.
    pose proof (ismono_isinj _ monof) as injf.
    pose proof (unique_choice
                  (λy x, f x = y)
                  _
                  (λy, (@center _ (surjf y), atmost1P_isinj injf y)))
      as H_unique_choice.
    apply (isequiv_adjointify _ H_unique_choice.1).
    - intro.
      apply H_unique_choice.2.
    - intro.
      apply injf.
      apply H_unique_choice.2.
  end-/
End iso.
