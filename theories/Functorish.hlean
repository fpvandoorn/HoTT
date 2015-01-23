Require Import HoTT.Basics Types.Universe TruncType UnivalenceImpliesfunext.
Open Scope equiv.
Open Scope path.

section Functorish
Context [H : Univalence].
/- We do not need composition to be preserved. -/
Global Class Functorish (F : Type → Type) := {
  fmap {A B} (f : A → B) : F A → F B ;
  fmap_idmap (A:Type) : fmap (idmap : A → A) = idmap
}.

Global Arguments fmap F {FF} {A B} f _ : rename.
Global Arguments fmap_idmap F {FF A} : rename.

Context (F : Type → Type).
Context {FF : Functorish F}.

Proposition isequiv_fmap {A B} (f : A → B) [H : is_equiv _ _ f]
  : is_equiv (fmap F f).
/-begin
  refine (equiv_induction (λA' e, is_equiv (fmap F e)) _ _ (equiv.mk _ _ f _)).
  refine (transport _ (fmap_idmap F)⁻¹ _);
    try apply isequiv_idmap. /- This line may not be needed in a new enough coq. -/
end-/

Proposition fmap_agrees_with_univalence {A B} (f : A → B) [H : is_equiv _ _ f]
  : fmap F f = equiv_path _ _ (ap F (path_universe f)).
/-begin
  refine (equiv_induction
    (λA' e, fmap F e = equiv_path _ _ (ap F (path_universe e)))
    _ _ (equiv.mk _ _ f _)).
  transitivity (idmap : F A → F A).
    apply fmap_idmap.
  change (equiv_idmap A) with (equiv_path A A 1).
  rewrite (@eta_path_universe _ A A 1). exact 1.
end-/

End Functorish.
