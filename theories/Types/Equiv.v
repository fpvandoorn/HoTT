/- -*- mode: coq; mode: visual-line -*- -/

Require Import HoTT.Basics.
Require Import Types.Prod Types.Sigma Types.ΠTypes.Arrow Types.Paths Types.Record.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

/- Equivalences -/

section AssumeFunext
  Context [H : Funext].

  /- We begin by showing that, assuming function extensionality, [IsEquiv f] is an hprop. -/
  definition hprop_isequiv [instance] {A B} `(f : A → B)
  : is_hprop (IsEquiv f).
  /-begin
    apply hprop_inhabited_contr; intros feq.
    /- We will show that if [IsEquiv] is inhabited, then it is contractible, because it is equivalent to a sigma of a pointed path-space over a pointed path-space, both of which are contractible. -/
    refine (contr_equiv' Σg : B → A, g ≈ f⁻¹  _).
    equiv_via (Σg:B->A, Σr:g=f⁻¹, Σs:g=f⁻¹, r=s ); apply equiv_inverse.
    1:exact (equiv_functor_sigma' (equiv_idmap _) (λ_, equiv_sigma_contr _ )).
    /- First we apply [issig], peel off the first component, and convert to pointwise paths. -/
    refine (equiv_compose' _ (equiv_inverse (issig_isequiv f))).
    refine (equiv_functor_sigma' (equiv_idmap (B → A)) _); intros g; simpl.
    equiv_via (Σr : g == f⁻¹, Σs : g == f⁻¹, r == s ).
    /- Now the idea is that if [f] is an equivalence, then [g f == 1] and [f g == 1] are both equivalent to [g == f⁻¹]. -/
    { refine (equiv_functor_sigma'
                (equiv_functor_Πidmap (λb p, (ap f)⁻¹ (p ⬝ (eisretr f b)⁻¹)))
                (λr, equiv_functor_sigma'
                            (equiv_inverse (equiv_functor_Πf (λa p, p ⬝ (eissect f a)))) _));
      intros s; simpl.
      /- What remains is to show that under these equivalences, the remaining datum [eisadj] reduces simply to [r == s].  Pleasingly, Coq can compute for us exactly what this means. -/
      apply equiv_inverse;
        refine (equiv_functor_forall' (BuildEquiv _ _ f _) _);
        intros a; simpl; unfold functor_forall.
      rewrite transport_paths_FlFr.
      /- At this point it's just naturality wrangling, potentially automatable.  It's a little unusual because what we have to prove is not just the existence of some path, but that one path-type is equivalent to another one, but we can mostly still use [rewrite]. -/
      Open Scope long_path_scope.
      rewrite ap_pp, !concat_p_pp, eisadj, <- !ap_V, <- !ap_compose.
      unfold compose; rewrite (concat_pA1_p (eissect f) (eissect f a)⁻¹).
      rewrite (concat_A1p s (eissect f a)⁻¹).
      rewrite (concat_pp_A1 (λx, (eissect f x)⁻¹) (eissect f a)).
      /- Here instead of [whiskerR] we have to be a bit fancier. -/
      refine (equiv_compose'
                _ (equiv_inverse (equiv_ap (equiv_concat_r (eissect f a)⁻¹ _) _ _))).
      rewrite concat_pV_p.
      refine (equiv_compose' _ (equiv_ap (ap f) _ _)).
      /- Now we can get rid of the [≃] and reduce the question to constructing some path. -/
      apply equiv_concat_l.
      rewrite !ap_pp, !ap_V, <- !eisadj, <- ap_compose.
      rewrite_moveL_Vp_p.
      symmetry; exact (concat_A1p (eisretr f) (r (f a))).
      Close Scope long_path_scope. }
    /- The leftover goal is just nested applications of funext. -/
    { refine (equiv_functor_sigma' (equiv_path_arrow g f⁻¹)
                                   (λr, equiv_functor_sigma' (equiv_path_arrow g f⁻¹) _));
      intros s; simpl.
      refine (equiv_compose' _ (equiv_path_Πr s)).
      exact (equiv_ap (path_Πg f⁻¹) r s). }
  Qed.

  /- Thus, paths of equivalences are equivalent to paths of functions. -/
  Lemma equiv_path_equiv {A B : Type} (e1 e2 : A ≃ B)
  : (e1 ≈ e2 :> (A → B)) ≃ (e1 ≈ e2 :> (A ≃ B)).
  Proof.
    equiv_via ((issig_equiv A B) ⁻¹ e1 ≈ (issig_equiv A B) ⁻¹ e2).
    2: symmetry; apply equiv_ap; refine _.
    exact (equiv_path_sigma_hprop ((issig_equiv A B)⁻¹ e1) ((issig_equiv A B)⁻¹ e2)).
  end-/

  definition path_equiv {A B : Type} {e1 e2 : A ≃ B}
  : (e1 ≈ e2 :> (A → B)) → (e1 ≈ e2 :> (A ≃ B)) :=
       equiv_path_equiv e1 e2.

  definition isequiv_path_equiv [instance] {A B : Type} {e1 e2 : A ≃ B}
  : IsEquiv (@path_equiv _ _ e1 e2)
    /- Coq can find this instance by itself, but it's slow. -/ :=
       equiv_isequiv (equiv_path_equiv e1 e2).

  /- This implies that types of equivalences inherit truncation.  Note that we only state the theorem for [n.+1]-truncatedness, since it is not tt for contractibility: if [B] is contractible but [A] is not, then [A ≃ B] is not contractible because it is not inhabited.

   Don't confuse this lemma with [trunc_equiv], which says that if [A] is truncated and [A] is equivalent to [B], then [B] is truncated.  It would be nice to find a better pair of names for them. -/
  definition istrunc_equiv [instance] {n : trunc_index} {A B : Type} [H : is_trunc n.+1 B]
  : is_trunc n.+1 (A ≃ B).
  /-begin
    simpl. intros e1 e2.
    apply (trunc_equiv _ (equiv_path_equiv e1 e2)).
  end-/

  /- In the contractible case, we have to assume that *both* types are contractible to get a contractible type of equivalences. -/
  definition contr_equiv_contr_contr [instance] {A B : Type} [H : is_contr A] [H : is_contr B]
  : is_contr (A ≃ B).
  /-begin
    exists equiv_contr_contr.
    intros e. apply path_equiv, path_forall. intros ?; apply contr.
  end-/

  /- Equivalences are functorial under equivalences. -/
  definition functor_equiv {A B C D} (h : A ≃ C) (k : B ≃ D)
  : (A ≃ B) → (C ≃ D) :=
     λf, equiv_compose (equiv_compose' k f) (equiv_inverse h).

  definition isequiv_functor_equiv [instance] {A B C D} (h : A ≃ C) (k : B ≃ D)
  : IsEquiv (functor_equiv h k).
  /-begin
    refine (isequiv_adjointify _
              (functor_equiv (equiv_inverse h) (equiv_inverse k)) _ _).
    - intros f; apply path_equiv, path_arrow; intros x; simpl.
      exact (eisretr k _ ⬝ ap f (eisretr h x)).
    - intros g; apply path_equiv, path_arrow; intros x; simpl.
      exact (eissect k _ ⬝ ap g (eissect h x)).
  end-/

  definition equiv_functor_equiv {A B C D} (h : A ≃ C) (k : B ≃ D)
  : (A ≃ B) ≃ (C ≃ D) :=
     BuildEquiv _ _ (functor_equiv h k) _.  

End AssumeFunext.
