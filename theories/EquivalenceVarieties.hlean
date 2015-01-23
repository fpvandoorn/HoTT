/- -*- mode: coq; mode: visual-line -*- -/
/- Comparing definitions of equivalence -/

Require Import HoTT.Basics HoTT.Types.
Require Import HProp.
Require Import HoTT.Tactics.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables A B f.

section Assumefunext
Context [H : funext].

/- In this file we show that several different definitions of "equivalence" are all equivalent to the one we have chosen.  This also yields alternative proofs that [is_equiv f] is an hprop. -/

/- Contractible maps -/

/- We say a map is "contractible" if all of its homotopy fibers are contractible.  (More generally, a map is n-truncated if all of its homotopy fibers are n-truncated.)  This was Voevodsky's first definition of equivalences in homotopy type theory.

   It is fairly straightforward to show that this definition is *logically* equivalent to the one we have given.
-/

definition fcontr_isequiv `(f : A → B)
  : is_equiv f → (Πb:B, is_contr Σa : A, f a = b).
/-begin
  intros ? b.  exists ⟨f⁻¹ b , retr f b⟩.  intros [a p].
  refine (path_sigma' _ ((ap f⁻¹ p)⁻¹ ⬝ sect f a) _).
  rewrite (transport_compose (λy, y = b) f _ _), transport_paths_l.
  rewrite ap_pp, ap_V, <- ap_compose, inv_Vp, concat_pp_p.
  unfold compose; rewrite (concat_A1p (retr f) p).
  rewrite eisadj.  by apply concat_V_pp.
end-/

definition isequiv_fcontr `(f : A → B)
  : (Πb:B, is_contr Σa : A, f a = b) → is_equiv f.
/-begin
  intros ?. refine (is_equiv.mk _ _ _
    (λb, (center Σa : A, f a = b).1)
    (λb, (center Σa : A, f a = b).2)
    (λa, (@contr Σx : A, f x = f a _ ⟨a,1⟩)..1)
    _).
  intros a. apply moveL_M1.
  rewrite <- transport_paths_l, <- transport_compose.
  exact ((@contr Σx : A, f x = f a _ ⟨a,1⟩)..2).
end-/

/- Therefore, since both are hprops, they are equivalent by [equiv_iff_hprop].  However, we can also use this to *prove* that [is_equiv] is an hprop.  We begin by showing that if [f] is an equivalence, then the type of sections of [f] and the type of retractions of [f] are both contractible. -/

definition contr_sect_equiv `(f : A → B) [H : is_equiv A B f]
  : is_contr Σg : B → A, Sect g f.
/-begin
  /- First we turn homotopies into paths. -/
  refine (contr_equiv' Σg : B → A, f ∘ g = idmap  _).
  apply symmetry.
  refine (equiv_functor_sigma' (equiv_idmap _) _); intros g.
  exact (equiv_path_pi (f ∘ g) idmap).
  /- Now this is just the fiber over [idmap] of postcomposition with [f], and the latter is an equivalence since [f] is. -/
  apply fcontr_isequiv; exact _.
end-/

definition contr_retr_equiv `(f : A → B) [H : is_equiv A B f]
  : is_contr Σg : B → A, Sect f g.
/-begin
  /- This proof is just like the previous one. -/
  refine (contr_equiv' Σg : B → A, g ∘ f = idmap  _).
  apply symmetry.
  refine (equiv_functor_sigma' (equiv_idmap _) _); intros g.
  exact (equiv_path_pi (g ∘ f) idmap).
  apply fcontr_isequiv; exact _.
end-/

/- Using this, we can prove that [is_equiv f] is an h-proposition.  We make this a [Local Definition] since we already have a [Global Instance] of it available in [types/Equiv].  -/

Local definition hprop_isequiv `(f : A → B) : is_hprop (is_equiv f).
/-begin
  apply hprop_inhabited_contr; intros ?.
  /- Get rid of that pesky record. -/
  refine (contr_equiv _ (issig_isequiv f)).
  /- Now we claim that the top two elements, [s] and the coherence relation, taken together are contractible, so we can peel them off. -/
  refine (contr_equiv' Σg : B → A, Sect g f
    (equiv_inverse (equiv_functor_sigma' (equiv_idmap (B → A))
      (λg, (@equiv_sigma_contr (Sect g f)
        (λr, Σs : Sect f g, Πx, r (f x) = ap f (s x) )
        _))))).
  /- What remains afterwards is just the type of sections of [f]. -/
  2:apply contr_sect_equiv; assumption.
  intros r.
  /- Now we claim this is equivalent to a certain space of paths. -/
  refine (contr_equiv'
    (Πx, (existT (λa, f a = f x) x 1) = (g (f x); r (f x)))
    (equiv_inverse _)).
  /- The proof of this equivalence is basically just rearranging quantifiers and paths. -/
  refine (equiv_compose' _ (equiv_sigT_coind (λx, g (f x) = x)
      (λx p, r (f x) = ap f p))).
  refine (equiv_functor_forall' (equiv_idmap A) _); intros a; simpl.
  refine (equiv_compose' (equiv_path_inverse _ _) _).
  refine (equiv_compose' (equiv_path_sigma (λx, f x = f a)
    (g (f a) ; r (f a)) ⟨a , 1⟩) _); simpl.
  refine (equiv_functor_sigma' (equiv_idmap _) _); intros p; simpl.
  rewrite (transport_compose (λy, y = f a) f), transport_paths_l.
  refine (equiv_compose' (equiv_moveR_Vp _ _ _) _).
  by rewrite concat_p1; apply equiv_idmap.
  /- Finally, this is a space of paths in a fiber of [f]. -/
  refine (@contr_pi _ _ _ _); intros a.
  refine (@contr_paths_contr _ _ _ _).
  by refine (fcontr_isequiv f _ _).
Qed.

/- Now since [is_equiv f] and the assertion that its fibers are contractible are both HProps, logical equivalence implies equivalence. -/

definition equiv_fcontr_isequiv `(f : A → B)
  : (Πb:B, is_contr Σa : A, f a = b) ≃ is_equiv f.
Proof.
  apply equiv_iff_hprop.
  by apply isequiv_fcontr.
  by apply fcontr_isequiv.
end-/

/- Alternatively, we could also construct this equivalence directly, and derive the fact that [is_equiv f] is an HProp from that.  -/

Local definition equiv_fcontr_isequiv' `(f : A → B)
  : (Πb:B, is_contr Σa : A, f a = b) ≃ is_equiv f.
/-begin
  /- First we get rid of those pesky records. -/
  refine (equiv_compose' _ (equiv_functor_pi idmap
    (λb, equiv_inverse (issig_contr Σa : A, f a = b)))).
  refine (equiv_compose' (issig_isequiv f) _).
  /- Now we can really get to work.
     First we peel off the inverse function and the [retr]. -/
  refine (equiv_compose' _ (equiv_inverse (equiv_sigT_coind _ _))).
  refine (equiv_compose' _ (equiv_inverse
    (@equiv_functor_sigma' _ _ _ (λf0, Πx y, f0 x = y)
      (equiv_sigT_coind _ _)
      (λfg, equiv_idmap (Πx y,
        (equiv_sigT_coind _ (λb a, f a = b) fg x = y)))))).
  refine (equiv_compose' _ (equiv_inverse (equiv_sigma_assoc
    (λg, Πx, f (g x) = x)
    (λgh, Πx y,
      (λb, ⟨gh.1 b, gh.2 b⟩) x = y)))).
  refine (equiv_functor_sigma' (equiv_idmap _) _). intros g.
  refine (equiv_functor_sigma' (equiv_idmap _) _). intros r. simpl.
  /- Now we use the fact that Paulin-Mohring J is an equivalence. -/
  refine (equiv_compose' _ (equiv_inverse (@equiv_functor_forall' _ _
    (λx, Πa (y : f a = x),
      (existT (λa, f a = x) (g x) (r x)) = ⟨a,y⟩)
    _ _ (equiv_idmap _)
    (λx:B, equiv_sigT_ind
      (λy:exists a:A, f a = x, ⟨g x,r x⟩ = y))))).
  refine (equiv_compose' _ (equiv_flip _)).
  refine (equiv_compose' _ (equiv_inverse (@equiv_functor_forall' _ _
    (λa, existT (λa', f a' = f a) (g (f a)) (r (f a)) = ⟨a,1⟩)
    _ _ (equiv_idmap A)
    (λa, equiv_paths_ind (f a)
      (λb y, (existT (λa, f a = b) (g b) (r b)) = ⟨a,y⟩))))).
  /- We identify the paths in a Sigma-type. -/
  refine (equiv_compose' _ (equiv_inverse (@equiv_functor_forall' _ _
    (λa,
      exists p, transport (λa' : A, f a' = f a) p (r (f a)) = 1)
    _ _ (equiv_idmap A)
    (λa, equiv_path_sigma (λa', f a' = f a)
      (g (f a);r (f a)) ⟨a,1⟩)))).
  /- Now we can peel off the [sect]. -/
  refine (equiv_compose' _ (equiv_inverse (equiv_sigT_coind
    (λa, g (f a) = a)
    (λa p, transport (λa', f a' = f a) p (r (f a)) = 1)))).
  refine (equiv_functor_sigma' (equiv_idmap _) _). intros s.
  /- And what's left is the [adj]. -/
  refine (equiv_functor_forall' (equiv_idmap _) _). intros a; simpl.
  refine (equiv_compose' _ (equiv_concat_l
             (transport_compose (λb, b = f a) f (s a) (r (f a))
              ⬝ transport_paths_l (ap f (s a)) (r (f a)))⁻¹ 1)).
  exact (equiv_compose'
    (equiv_concat_r (concat_p1 _) _)
    (equiv_inverse (equiv_moveR_Vp (r (f a)) 1 (ap f (s a))))).
end-/

/- Bi-invertible maps -/

/- A map is "bi-invertible" if it has both a section and a retraction, not necessarily the same.  This definition of equivalence was proposed by Andre Joyal. -/

definition BiInv `(f : A → B) : Type :=
     Σg : B → A, Sect f g × Σh : B → A, Sect h f.

/- It seems that the easiest way to show that bi-invertibility is equivalent to being an equivalence is also to show that both are h-props and that they are logically equivalent. -/

definition isequiv_biinv `(f : A → B)
  : BiInv f → is_equiv f.
/-begin
  intros [[g s] [h r]].
  exact (isequiv_adjointify f g
    (λx, ap f (ap g (r x)⁻¹ ⬝ s (h x))  ⬝ r x)
    s).
end-/

definition isprop_biinv [instance] `(f : A → B) : is_hprop (BiInv f) | 0.
/-begin
  apply hprop_inhabited_contr.
  intros bif; pose (fe := isequiv_biinv f bif).
  apply @contr_prod.
  /- For this, we've done all the work already. -/
  by apply contr_retr_equiv.
  by apply contr_sect_equiv.
end-/

definition equiv_biinv_isequiv `(f : A → B)
  : BiInv f ≃ is_equiv f.
/-begin
  apply equiv_iff_hprop.
  by apply isequiv_biinv.
  intros ?.  split.
  by exists (f⁻¹); apply eissect.
  by exists (f⁻¹); apply eisretr.
end-/

/- n-Path-split maps.
 
A map is n-path-split if its induced maps on the first n iterated path-spaces are split surjections.  Thus every map is 0-path-split, the 1-path-split maps are the split surjections, and so on.  It turns out that for n>1, being n-path-split is the same as being an equivalence. -/

Fixpoint PathSplit (n : nat) `(f : A → B) : Type :=
     match n with
       | 0 => unit
       | S n => (Πa, hfiber f a) *
                Π(x y : A), PathSplit n (@ap _ _ f x y)
     end.

definition isequiv_pathsplit (n : nat) {f : A → B}
: PathSplit n.+2 f → is_equiv f.
/-begin
  intros [g k].
  pose (h := λx y p, (pr1 (k x y) p).1).
  pose (hs := λx y, (λp, (pr1 (k x y) p).2)
                         : Sect (h x y) (ap f)).
  clearbody hs; clearbody h; clear k.
  apply isequiv_fcontr; intros b.
  apply contr_inhabited_hprop.
  2:exact (g b).
  apply hprop_allpath; intros [a p] [a' p'].
  refine (path_sigma' _ (h a a' (p ⬝ p'⁻¹)) _).
  refine (transport_paths_Fl _ _ ⬝ _).
  refine ((inverse2 (hs a a' (p ⬝ p'⁻¹)) @@ 1) ⬝ _).
  refine ((inv_pp p p'⁻¹ @@ 1) ⬝ _).
  refine (concat_pp_p _ _ _ ⬝ _).
  refine ((1 @@ concat_Vp _) ⬝ _).
  exact ((inv_V p' @@ 1) ⬝ concat_p1 _).
end-/

Global Instance contr_pathsplit_isequiv
           (n : nat) `(f : A → B) [H : is_equiv _ _ f]
: is_contr (PathSplit n f).
/-begin
  generalize dependent B; revert A.
  simple_induction n n IHn; intros A B f ?.
  - exact _.
  - refine contr_prod.
    refine contr_forall.
    intros; apply fcontr_isequiv; exact _.
end-/

definition ishprop_pathsplit [instance] (n : nat) `(f : A → B)
: is_hprop (PathSplit n.+2 f).
/-begin
  apply hprop_inhabited_contr; intros ps.
  pose (isequiv_pathsplit n ps).
  exact _.
end-/

definition equiv_pathsplit_isequiv (n : nat) `(f : A → B)
: PathSplit n.+2 f ≃ is_equiv f.
/-begin
  refine (equiv_iff_hprop _ _).
  - apply isequiv_pathsplit.
  - intros ?; refine (center _).
end-/

/- Path-splitness transfers across commutative squares of equivalences. -/
definition equiv_functor_pathsplit (n : nat) {A B C D}
      (f : A → B) (g : C → D) (h : A ≃ C) (k : B ≃ D)
      (p : g ∘ h ∼ k ∘ f)
: PathSplit n f ≃ PathSplit n g.
/-begin
  destruct n as [|n].
  1:apply equiv_idmap.
  destruct n as [|n].
  - simpl.
    apply equiv_functor_prod'.
    2:apply equiv_contr_contr.
    refine (equiv_functor_forall' (equiv_inverse k) _); intros d.
    unfold hfiber.
    refine (equiv_functor_sigma' h _); intros a.
    refine (equiv_compose' (equiv_concat_l (p a) d) _).
    unfold compose; simpl; apply equiv_moveR_equiv_M.
  - refine (equiv_compose' _ (equiv_pathsplit_isequiv n f)).
    refine (equiv_compose' (equiv_inverse (equiv_pathsplit_isequiv n g)) _).
    apply equiv_iff_hprop; intros e.
    + refine (isequiv_commsq f g h k (λa, (p a)⁻¹)).
    + refine (isequiv_commsq' f g h k p).
end-/

/- A map is oo-path-split if it is n-path-split for all n.  This is also equivalent to being an equivalence. -/

definition ooPathSplit `(f : A → B) : Type :=
     Πn, PathSplit n f.

definition isequiv_oopathsplit {f : A → B}
: ooPathSplit f → is_equiv f :=
     λps, isequiv_pathsplit 0 (ps 2).

Global Instance contr_oopathsplit_isequiv
           `(f : A → B) [H : is_equiv _ _ f]
: is_contr (ooPathSplit f).
/-begin
  apply contr_forall.
end-/

definition ishprop_oopathsplit [instance] `(f : A → B)
: is_hprop (ooPathSplit f).
/-begin
  apply hprop_inhabited_contr; intros ps.
  pose (isequiv_oopathsplit ps).
  exact _.
end-/

definition equiv_oopathsplit_isequiv `(f : A → B)
: ooPathSplit f ≃ is_equiv f.
/-begin
  refine (equiv_iff_hprop _ _).
  - apply isequiv_oopathsplit.
  - intros ?; refine (center _).
end-/

End Assumefunext.
