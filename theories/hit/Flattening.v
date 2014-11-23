/- -*- mode: coq; mode: visual-line -*- -/

/- The flattening lemma. -/

Require Import HoTT.Basics UnivalenceImpliesFunext.
Require Import Types.Paths Types.ΠTypes.Sigma Types.Arrow Types.Universe.
Local Open Scope path_scope.
Local Open Scope equiv_scope.


/- First we define the general non-recursive HIT. -/

Module Export BaseHIT.

Private Inductive W (A B : Type) (f g : B → A) : Type :=
| cc : A → W A B f g.

Arguments cc {A B f g} a.

Axiom pp : Π{A B f g} (b:B), @cc A B f g (f b) ≈ cc (g b).

definition W_ind {A B f g} (P : W A B f g → Type)
  (cc' : Πa, P (cc a))
  (pp' : Πb, (pp b) ▹ (cc' (f b)) ≈ cc' (g b))
  : Πw, P w :=
     λw, match w with cc a => λ_, cc' a end pp'.

Axiom W_ind_beta_pp
  : Π{A B f g} (P : W A B f g → Type) (cc' : Πa, P (cc a))
  (pp' : Πb, (pp b) ▹ (cc' (f b)) ≈ cc' (g b)) (b:B),
  apD (W_ind P cc' pp') (pp b) ≈ pp' b.

End BaseHIT.

definition W_rec {A B f g} (P : Type) (cc' : A → P)
  (pp' : Πb, cc' (f b) ≈ cc' (g b))
  : W A B f g → P :=
     W_ind (λ_, P) cc' (λb, transport_const _ _ ⬝ pp' b).

definition W_rec_beta_pp {A B f g} (P : Type) (cc' : A → P)
  (pp' : Πb:B, cc' (f b) ≈ cc' (g b)) (b:B)
  : ap (W_rec P cc' pp') (pp b) ≈ pp' b.
/-begin
  unfold W_rec.
  /- Use [eapply] rather than [refine] so that we don't get evars as goals, and don't have to shelve any goals with [shelve_unifiable]. -/
  eapply (cancelL (transport_const (pp b) _)).
  refine ((apD_const (@W_ind A B f g (λ_, P) cc' _) (pp b))⁻¹ ⬝ _).
  refine (W_ind_beta_pp (λ_, P) _ _ _).
end-/



/- Now we define the flattened HIT which will be equivalent to the total space of a fibration over [W]. -/

Module Export FlattenedHIT.

Private Inductive Wtil (A B : Type) (f g : B → A)
  (C : A → Type) (D : Πb, C (f b) ≃ C (g b))
  : Type :=
| cct : Πa, C a → Wtil A B f g C D.

Arguments cct {A B f g C D} a c.

Axiom ppt : Π{A B f g C D} (b:B) (y:C (f b)),
  @cct A B f g C D (f b) y ≈ cct (g b) (D b y).

definition Wtil_ind {A B f g C D} (Q : Wtil A B f g C D → Type)
  (cct' : Πa x, Q (cct a x))
  (ppt' : Πb y, (ppt b y) ▹ (cct' (f b) y) ≈ cct' (g b) (D b y))
  : Πw, Q w :=
     λw, match w with cct a x => cct' a x end.

Axiom Wtil_ind_beta_ppt
  : Π{A B f g C D} (Q : Wtil A B f g C D → Type)
    (cct' : Πa x, Q (cct a x))
    (ppt' : Πb y, (ppt b y) ▹ (cct' (f b) y) ≈ cct' (g b) (D b y))
    (b:B) (y : C (f b)),
    apD (Wtil_ind Q cct' ppt') (ppt b y) ≈ ppt' b y.

End FlattenedHIT.

definition Wtil_rec {A B f g C} {D : Πb, C (f b) ≃ C (g b)}
  (Q : Type) (cct' : Πa (x : C a), Q)
  (ppt' : Πb (y : C (f b)), cct' (f b) y ≈ cct' (g b) (D b y))
  : Wtil A B f g C D → Q :=
     Wtil_ind (λ_, Q) cct' (λb y, transport_const _ _ ⬝ ppt' b y).

definition Wtil_rec_beta_ppt
  {A B f g C} {D : Πb, C (f b) ≃ C (g b)}
  (Q : Type) (cct' : Πa (x : C a), Q)
  (ppt' : Π(b:B) (y : C (f b)), cct' (f b) y ≈ cct' (g b) (D b y))
  (b:B) (y: C (f b))
  : ap (@Wtil_rec A B f g C D Q cct' ppt') (ppt b y) ≈ ppt' b y.
/-begin
  unfold Wtil_rec.
  eapply (cancelL (transport_const (ppt (C:=C) b y) _)).
  refine ((apD_const
    (@Wtil_ind A B f g C D (λ_, Q) cct' _) (ppt b y))⁻¹ ⬝ _).
  refine (Wtil_ind_beta_ppt (λ_, Q) _ _ _ _).
end-/



/- Now we define the fibration over it that we will be considering the total space of. -/

section AssumeAxioms
Context [H : Univalence].

Context {A B : Type} {f g : B → A}.
Context {C : A → Type} {D : Πb, C (f b) ≃ C (g b)}.

Let W' := W A B f g.

Let P : W' → Type :=
     W_rec Type C (λb, path_universe (D b)).



/- Now we give the total space the same structure as [Wtil]. -/

Let sWtil := Σw:W', P w .

Let scct (a:A) (x:C a) : sWtil := (existT P (cc a) x).

Let sppt (b:B) (y:C (f b)) : scct (f b) y ≈ scct (g b) (D b y) :=
     path_sigma' P (pp b)
       (transport_path_universe' P (pp b) (D b)
         (W_rec_beta_pp Type C (λb0, path_universe (D b0)) b) y).

/- Here is the dependent eliminator -/
definition sWtil_ind (Q : sWtil → Type)
  (scct' : Πa x, Q (scct a x))
  (sppt' : Πb y, (sppt b y) ▹ (scct' (f b) y) ≈ scct' (g b) (D b y))
  : Πw, Q w.
/-begin
  apply sigT_ind.
  refine (W_ind (λw, Πx:P w, Q ⟨w,x⟩)
    (λa x, scct' a x) _).
  intros b.
  apply (dpath_ΠP (λa b, Q ⟨a,b⟩) _ _ (pp b)
    (scct' (f b)) (scct' (g b))).
  intros y.
  set (q := transport_path_universe' P (pp b) (D b)
    (W_rec_beta_pp Type C (λb0 : B, path_universe (D b0)) b) y).
  rewrite transportD_is_transport.
  refine (_ ⬝ apD (scct' (g b)) q⁻¹).
  refine (moveL_transport_V (λx, Q (scct (g b) x)) q _ _ _).
  rewrite transport_compose, <- transport_pp.
  refine (_ ⬝ sppt' b y).
  apply ap10, ap.
  refine (whiskerL _ (ap_existT P (cc (g b)) _ _ q) ⬝ _).
  exact ((path_sigma_p1_1p' _ _ _)⁻¹).
end-/

/- The eliminator computes on the point constructor. -/
definition sWtil_ind_beta_cct (Q : sWtil → Type)
  (scct' : Πa x, Q (scct a x))
  (sppt' : Πb y, (sppt b y) ▹ (scct' (f b) y) ≈ scct' (g b) (D b y))
  (a:A) (x:C a)
  : sWtil_ind Q scct' sppt' (scct a x) ≈ scct' a x :=
     1.

/- This would be its propositional computation rule on the path constructor... -/
(**
<<
definition sWtil_ind_beta_ppt (Q : sWtil → Type)
  (scct' : Πa x, Q (scct a x))
  (sppt' : Πb y, (sppt b y) ▹ (scct' (f b) y) ≈ scct' (g b) (D b y))
  (b:B) (y:C (f b))
  : apD (sWtil_ind Q scct' sppt') (sppt b y) ≈ sppt' b y.
/-begin
  unfold sWtil_ind.
  /- ... but it's a doozy! -/
Abort.
>> *)

/- Fortunately, it turns out to be enough to have the computation rule for the *non-dependent* eliminator! -/

/- We could define that in terms of the dependent one, as usual...
<<
definition sWtil_rec (P : Type)
  (scct' : Πa (x : C a), P)
  (sppt' : Πb (y : C (f b)), scct' (f b) y ≈ scct' (g b) (D b y))
  : sWtil → P :=
     sWtil_ind (λ_, P) scct' (λb y, transport_const _ _ ⬝ sppt' b y).
>> -/

/- ...but if we define it diindly, then it's easier to reason about. -/
definition sWtil_rec (Q : Type)
  (scct' : Πa (x : C a), Q)
  (sppt' : Πb (y : C (f b)), scct' (f b) y ≈ scct' (g b) (D b y))
  : sWtil → Q.
Proof.
  apply sigT_ind.
  refine (W_ind (λw, P w → Q) (λa x, scct' a x) _).
  intros b.
  refine (dpath_arrow P (λ_, Q) _ _ _ _).
  intros y.
  refine (transport_const _ _ ⬝ _).
  refine (sppt' b _ ⬝ ap _ _).
  refine ((transport_path_universe' P (pp b) (D b) _ _)⁻¹).
  exact (W_rec_beta_pp _ _ _ _).
end-/

Open Scope long_path_scope.

definition sWtil_rec_beta_ppt (Q : Type)
  (scct' : Πa (x : C a), Q)
  (sppt' : Πb (y : C (f b)), scct' (f b) y ≈ scct' (g b) (D b y))
  (b:B) (y: C (f b))
  : ap (sWtil_rec Q scct' sppt') (sppt b y) ≈ sppt' b y.
/-begin
  unfold sWtil_rec, sppt.
  refine (@ap_sigT_rec_path_sigma W' P Q _ _ (pp b) _ _ _ _ ⬝ _); simpl.
  rewrite (@W_ind_beta_pp A B f g).
  rewrite (ap10_dpath_arrow P (λ_, Q) (pp b) _ _ _ y).
  repeat rewrite concat_p_pp.
  /- Now everything cancels! -/
  rewrite ap_V, concat_pV_p, concat_pV_p, concat_pV_p, concat_Vp.
  by apply concat_1p.
Qed.

Close Scope long_path_scope.

/- Woot! -/
definition equiv_flattening : Wtil A B f g C D ≃ sWtil.
Proof.
  /- The maps back and forth are obtained easily from the non-dependent eliminators. -/
  refine (equiv_adjointify
    (Wtil_rec _ scct sppt)
    (sWtil_rec _ cct ppt)
    _ _).
  /- The two homotopies are completely symmetrical, using the *dependent* eliminators, but only the computation rules for the non-dependent ones. -/
  refine (sWtil_ind _ (λa x, 1) _). intros b y.
  apply dpath_path_FFlr.
  rewrite concat_1p, concat_p1.
  rewrite sWtil_rec_beta_ppt.
  by symmetry; apply (@Wtil_rec_beta_ppt A B f g C D).
  refine (Wtil_ind _ (λa x, 1) _). intros b y.
  apply dpath_path_FFlr.
  rewrite concat_1p, concat_p1.
  rewrite Wtil_rec_beta_ppt.
  by symmetry; apply sWtil_rec_beta_ppt.
end-/

End AssumeAxioms.
