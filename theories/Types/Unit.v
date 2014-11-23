/- -*- mode: coq; mode: visual-line -*- -/
/- Theorems about the unit type -/

Require Import HoTT.Basics.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables A.

/- Eta conversion -/

definition eta_unit (z : unit) : star ≈ z :=
     match z with star => 1 end.

/- Paths -/

/- This is all kind of ridiculous, but it fits the pattern. -/

definition path_unit_uncurried (z z' : unit) : unit → z ≈ z' :=
     λ_, match z, z' with star, star => 1 end.

definition path_unit (z z' : unit) : z ≈ z' :=
     path_unit_uncurried z z' star.

definition eta_path_unit {z z' : unit} (p : z ≈ z') :
  path_unit z z' ≈ p.
/-begin
  destruct p. destruct z. reflexivity.
end-/

definition isequiv_path_unit [instance] (z z' : unit) : IsEquiv (path_unit_uncurried z z') | 0.
  refine (BuildIsEquiv _ _ (path_unit_uncurried z z') (λ_, star)
    (λp:z=z',
      match p in (_ ≈ z') return (path_unit_uncurried z z' star ≈ p) with
        | idpath => match z as z return (path_unit_uncurried z z star ≈ 1) with
                    | star => 1
                  end
      end)
    (λx, match x with star => 1 end) _).
  intros []; destruct z, z'; reflexivity.
Defined.

definition equiv_path_unit (z z' : unit) : unit ≃ (z ≈ z') :=
     BuildEquiv _ _ (path_unit_uncurried z z') _.

/- Transport -/

/- Is a special case of transporting in a constant fibration. -/

/- Universal mapping properties -/

/- The positive universal property -/
Arguments Unit_ind [A] a u : rename.

definition isequiv_unit_ind [instance] [H : Funext] (A : Type) : IsEquiv (@Unit_ind (λ_, A)) | 0 :=
     isequiv_adjointify _
  (λf : unit → A, f star)
  (λf : unit → A, path_Π(@Unit_ind (λ_, A) (f star)) f
                                    (λx, match x with star => 1 end))
  (λ_, 1).

/- For various reasons, it is typically more convenient to define functions out of the unit as constant maps, rather than [Unit_ind]. -/
Notation unit_name x := (λ(_ : unit), x).

definition isequiv_unit_name [instance] [H : Funext] (A : Type)
: IsEquiv (λ(a:A), unit_name a).
/-begin
  refine (isequiv_adjointify _ (λf, f star) _ _).
  - intros f; apply path_forall; intros x.
    apply ap, path_unit.
  - intros a; reflexivity.
end-/

/- The negative universal property -/
definition unit_coind {A : Type} : unit → (A → unit) :=
     λ_ _, star.

definition isequiv_unit_coind [instance] [H : Funext] (A : Type) : IsEquiv (@unit_coind A) | 0 :=
     isequiv_adjointify _
  (λf, star)
  _ _.
/-begin
  - intro f. apply path_forall; intros x; apply path_unit.
  - intro x; destruct x; reflexivity.
end-/

definition equiv_unit_coind [H : Funext] (A : Type)
  : unit ≃ (A → unit) :=
     BuildEquiv _ _ (@unit_coind A) _.

/- Truncation -/

/- The unit type is contractible -/
/- Because [Contr] is a notation, and [Contr_internal] is the record, we need to iota expand to fool Coq's typeclass machinery into accepting supposedly "mismatched" contexts. -/
definition contr_unit [instance] : is_contr unit | 0 := let x := {|
  center := star;
  contr := λt : unit, match t with star => 1 end
|} in x.

/- Equivalences -/

/- A contractible type is equivalent to [unit]. -/
definition equiv_contr_unit [H : is_contr A] : A ≃ unit.
/-begin
  refine (BuildEquiv _ _
    (λ(_ : A), star)
    (BuildIsEquiv _ _ _
      (λ(_ : unit), center A)
      (λt : unit, match t with star => 1 end)
      (λx : A, contr x) _)).
  intro x. symmetry; apply ap_const.
end-/

/- Conversely, a type equivalent to [unit] is contractible. -/
definition contr_equiv_unit [instance] (A : Type) (f : A ≃ unit) : is_contr A | 10000 :=
     BuildContr A (f⁻¹ star)
  (λa, ap f⁻¹ (contr (f a)) ⬝ eissect f a).
