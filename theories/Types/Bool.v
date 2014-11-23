/- -*- mode: coq; mode: visual-line -*- -/
/- Theorems about the booleans -/

Require Import HoTT.Basics.
Require Import Types.Prod Types.Equiv.
Local Open Scope equiv_scope.

/- coq calls it "bool", we call it "bool" -/
Local Unset Elimination Schemes.
Inductive bool : Type1 :=
  | tt : bool
  | ff : bool.
Scheme Bool_ind := Induction for bool Sort Type.
Scheme Bool_rec := Minimality for bool Sort Type.

Add Printing If bool.

Delimit Scope bool_scope with bool.

Bind Scope bool_scope with bool.

definition andb (b1 b2 : bool) : bool := if b1 then b2 else ff.

definition orb (b1 b2 : bool) : bool := if b1 then tt else b2.

definition negb (b : bool) := if b then ff else tt.

definition implb (b1 b2 : bool) : bool := if b1 then b2 else tt.

Infix "||" := orb : bool_scope.
Infix "&&" := andb : bool_scope.

definition trunc_if [instance] n A B [H : is_trunc n A, is_trunc n B] (b : bool)
: is_trunc n (if b then A else B) | 100 :=
     if b as b return (IsTrunc n (if b then A else B)) then _ else _.

section BoolDecidable
  definition false_ne_true : ~ff ≈ tt :=
       λH, match H in (_ ≈ y) return (if y then Empty else bool) with
                  | 1%path => tt
                end.

  definition true_ne_false : ~tt ≈ ff :=
       λH, false_ne_true (symmetry _ _ H).

  definition decidable_paths_bool [instance] : DecidablePaths bool :=
       λx y, match x as x, y as y return ((x ≈ y) + (~x ≈ y)) with
                    | tt, tt => inl idpath
                    | ff, ff => inl idpath
                    | tt, ff => inr true_ne_false
                    | ff, tt => inr false_ne_true
                  end.

  Corollary hset_bool : IsHSet bool.
  /-begin
    exact _.
  end-/
End BoolDecidable.

section BoolForall
  Variable P : bool → Type.

  Let f (s : Πb, P b) := (s ff, s tt).

  Let g (u : P ff × P tt) (b : bool) : P b :=
    match b with
      | ff => pr1 u
      | tt => pr2 u
    end.

  definition equiv_bool_forall_prod [H : Funext] :
    (Πb, P b) ≃ P ff × P tt.
  /-begin
    apply (equiv_adjointify f g);
    repeat (reflexivity
              || intros []
              || intro
              || apply path_forall).
  end-/
End BoolForall.

/- The type [bool ≃ bool] is equivalent to [bool]. -/

/- The nonidentity equivalence is negation (the flip). -/
definition isequiv_negb [instance] : IsEquiv negb.
/-begin
  refine (@IsEquiv.mk
            _ _
            negb negb
            (λb, if b as b return negb (negb b) ≈ b then idpath else idpath)
            (λb, if b as b return negb (negb b) ≈ b then idpath else idpath)
            _).
  intros []; simpl; exact idpath.
end-/

definition equiv_negb : bool ≃ bool :=
     Equiv.mk bool Bool negb _.

/- Any equivalence [bool ≃ bool] sends [tt] and [ff] to different things. -/
definition eval_bool_isequiv (f : bool → bool) [H : IsEquiv bool Bool f]
: f ff ≈ negb (f tt).
/-begin
  pose proof (eissect f tt).
  pose proof (eissect f ff).
  destruct (f tt), (f ff).
  - etransitivity; try (eassumption || ⟨symmetry, eassumption⟩).
  - simpl. reflexivity.
  - simpl. reflexivity.
  - etransitivity; try (eassumption || ⟨symmetry, eassumption⟩).
end-/

section EquivBoolEquiv

  /- We will identify the constant equivalence with [tt] and the flip equivalence with [ff], and do this by evaluating the equivalence function on [tt]. -/
  Let f : (bool ≃ bool) → bool := λe, e tt.
  Let g : bool → (bool ≃ bool) := λb, if b
                                              then (equiv_idmap bool)
                                              else equiv_negb.

  definition equiv_bool_equiv_bool_bool [H : Funext] : bool ≃ (bool ≃ bool).
  /-begin
    refine (equiv_adjointify g f _ _);
    unfold f, g; clear f g;
    hnf; simpl.
    - intro e.
      destruct e as [e ?].
      apply path_equiv; try assumption.
      apply path_forall.
      intros []; simpl.
      × destruct (e tt); reflexivity.
      × etransitivity; [ | symmetry; apply eval_bool_isequiv; trivial ].
        destruct (e tt); reflexivity.
    - intros []; reflexivity.
  end-/

End EquivBoolEquiv.
