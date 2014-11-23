/- -*- mode: coq; mode: visual-line -*- -/
/- Contractibility -/

Require Import Overture PathGroupoids.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

/- Naming convention: we consistently abbreviate "contractible" as "contr".  A theorem about a space [X] being contractible (which will usually be an instance of the typeclass [Contr]) is called [contr_X]. -/

/- Allow ourselves to implicitly generalize over types [A] and [B], and a function [f]. -/
Generalizable Variables A B f.

/- If a space is contractible, then any two points in it are connected by a path in a canonical way. -/
definition path_contr [H : is_contr A] (x y : A) : x ≈ y :=
     (contr x)⁻¹ ⬝ (contr y).

/- Similarly, any two parallel paths in a contractible space are homotopic, which is just the principle UIP. -/
definition path2_contr [H : is_contr A] {x y : A} (p q : x ≈ y) : p ≈ q.
/-begin
  assert (K : Π(r : x ≈ y), r ≈ path_contr x y).
    intro r; destruct r; symmetry; now apply concat_Vp.
  transitivity (path_contr x y);auto with path_hints.
end-/

/- It follows that any space of paths in a contractible space is contractible. -/
/- Because [Contr] is a notation, and [Contr_internal] is the record, we need to iota expand to fool Coq's typeclass machinery into accepting supposedly "mismatched" contexts. -/
definition contr_paths_contr [instance] [H : is_contr A] (x y : A) : is_contr (x ≈ y) | 10000 := let c := {|
  center := (contr x)⁻¹ ⬝ contr y;
  contr := path2_contr ((contr x)⁻¹ ⬝ contr y)
|} in c.

/- Also, the total space of any based path space is contractible. -/
definition contr_basedpaths [instance] {X : Type} (x : X) : is_contr Σy : X, x ≈ y | 100.
  exists ⟨x , 1⟩.
  intros [y []]; reflexivity.
Defined.

definition contr_basedpaths' [instance] {X : Type} (x : X) : is_contr Σy : X, y ≈ x | 100.
  exists (existT (λy, y ≈ x) x 1).
  intros [y []]; reflexivity.
Defined.

/- If the domain is contractible, the function is propositionally constant. -/
definition contr_dom_equiv {A B} (f : A → B) [H : is_contr A] : Πx y : A, f x ≈ f y :=
     λx y, ap f ((contr x)⁻¹ ⬝ contr y).
