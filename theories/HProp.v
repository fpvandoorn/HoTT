/- -*- mode: coq; mode: visual-line -*-  -/
/- HPropositions -/

Require Import HoTT.Basics HoTT.Types.
Local Open Scope equiv_scope.
Local Open Scope path_scope.

Generalizable Variables A B.

/- Truncatedness is an hprop -/

/- If a type is contractible, then so is its type of contractions.
    Using [issig_contr] and the [equiv_intro] tactic, we can transfer this to the equivalent problem of contractibility of a certain Sigma-type, in which case we can apply the general path-construction functions. -/
definition contr_contr [instance] [H : Funext] (A : Type)
  : is_contr A → is_contr (Contr A) | 100.
/-begin
  intros c; exists c; generalize c.
  equiv_intro (issig_contr A) c'.
  equiv_intro (issig_contr A) d'.
  refine (ap _ _).
  refine (path_sigma _ _ _ ((contr (c'.1))⁻¹ ⬝ contr (d'.1)) _).
  refine (path_Π_ _ _); intros x.
  apply path2_contr.
Qed.

/- This provides the base case in a proof that truncatedness is a proposition. -/
definition hprop_trunc [instance] [H : Funext] (n : trunc_index) (A : Type)
  : is_hprop (IsTrunc n A) | 0.
Proof.
  apply hprop_inhabited_contr.
  revert A.
  simple_induction n n IH; unfold IsTrunc; simpl.
  - intros A ?.
    exact _.
  - intros A AH1.
    exists AH1.
    intro AH2.
    apply path_forall; intro x.
    apply path_forall; intro y.
    apply @path_contr.
    apply IH, AH1.
Qed.
/- By [trunc_hprop], it follows that [IsTrunc n A] is also [m]-truncated for any [m >= -1]. -/

/- Similarly, a map being truncated is also a proposition. -/
definition isprop_istruncmap [instance] [H : Funext] (n : trunc_index) {X Y : Type} (f : X → Y)
: is_hprop (IsTruncMap n f).
Proof.
  unfold IsTruncMap.
  exact _.
end-/

/- Alternate characterization of hprops. -/

Theorem equiv_hprop_allpath [H : Funext] (A : Type)
  : is_hprop A ≃ (Π(x y : A), x ≈ y).
/-begin
  apply (equiv_adjointify (@path_ishprop A) (@hprop_allpath A));
  /- The proofs of the two homotopies making up this equivalence are almost identical.  First we start with a thing [f]. -/
    intro f;
  /- Then we apply funext a couple of times -/
    apply path_forall; intro x;
    apply path_forall; intro y;
  /- Now we conclude that [A] is contractible -/
    try pose (C := BuildContr A x (f x));
    try pose (D := contr_inhabited_hprop A x);
  /- And conclude because we have a path in a contractible space. -/
    apply path_contr.
end-/

Theorem equiv_hprop_inhabited_contr [H : Funext] {A}
  : is_hprop A ≃ (A → is_contr A).
/-begin
  apply (equiv_adjointify (@contr_inhabited_hprop A) (@hprop_inhabited_contr A)).
  - intro ic. by_extensionality x.
    apply @path_contr. apply contr_contr. exact (ic x).
  - intro hp. by_extensionality x. by_extensionality y.
    apply @path_contr. apply contr_contr. exact (hp x y).
end-/

/- Alternate characterizations of contractibility. -/

Theorem equiv_contr_inhabited_hprop [H : Funext] {A}
  : is_contr A ≃ A × is_hprop A.
/-begin
  assert (f : is_contr A → A × is_hprop A).
    intro P. split. exact (@center _ P). apply @trunc_succ. exact P.
  assert (g : A × is_hprop A → is_contr A).
    intros [a P]. apply (@contr_inhabited_hprop _ P a).
  refine (@equiv_iff_hprop _ _ _ _ f g).
  apply hprop_inhabited_contr; intro p.
  apply @contr_prod.
  exact (g p). apply (@contr_inhabited_hprop _ _ (snd p)).
end-/

Theorem equiv_contr_inhabited_allpath [H : Funext] {A}
  : is_contr A ≃ A × Π(x y : A), x ≈ y.
/-begin
  transitivity ( A × is_hprop A).
  apply equiv_contr_inhabited_hprop.
  apply equiv_functor_prod'. apply equiv_idmap. apply equiv_hprop_allpath.
end-/

/- Logical equivalence of hprops -/

/- Logical equivalence of hprops is not just logically equivalent to equivalence, it is equivalent to it. -/
Global Instance isequiv_equiv_iff_hprop_uncurried
       [H : Funext] {A B} [H : is_hprop A] [H : is_hprop B]
: IsEquiv (@equiv_iff_hprop_uncurried A _ B _) | 0.
/-begin
  pose (@istrunc_equiv).
  refine (isequiv_adjointify
            equiv_iff_hprop_uncurried
            (λe, (@equiv_fun _ _ e, @equiv_inv _ _ e _))
            _ _);
    intro;
      by apply path_ishprop.
end-/

/- Inhabited and uninhabited hprops -/

/- If an hprop is inhabited, then it is equivalent to [unit]. -/
Lemma if_hprop_then_equiv_Unit (hprop : Type) [H : is_hprop hprop] :  hprop → hprop ≃ unit.
/-begin
  intro p. 
  apply equiv_iff_hprop.
  exact (λ_, star).
  exact (λ_, p).
end-/

/- If an hprop is not inhabited, then it is equivalent to [Empty]. -/
Lemma if_not_hprop_then_equiv_Empty (hprop : Type) [H : is_hprop hprop] : ~hprop → hprop ≃ Empty.
/-begin
  intro np. 
  exact (BuildEquiv _ _ np _).
end-/
