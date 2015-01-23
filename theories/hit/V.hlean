/- -*- mode: coq; mode: visual-line -*- -/

/- The cumulative hierarchy [V]. -/

Require Import HoTT.Basics.
Require Import Types.unit Types.bool Types.Universe Types.Sigma Types.Arrow Types.Forall.
Require Import HProp HSet UnivalenceImpliesfunext TruncType.
Require Import hit.Truncations hit.quotient.
Local Open Scope path_scope.
Local Open Scope equiv_scope.


/- Pushout with respect to a relation -/

/- This could be implemented using the pushouts in /hit/Pushout.v, where [f] and [g] are [(pr1 ∘ dpr1)] and [(pr2 ∘ dpr1)], with domain Σ(a,b) : A × B, R a b. However, these pushouts weren't implemented when I started this work, and doing it this way is closer to exercise 10.11 of the HoTT book -/

Module Export RPushout.

Private Inductive RPushout {A B : Type} (R : A → B → hProp) : Type :=
| inL : A → RPushout R
| inR : B → RPushout R.

Axiom glue : Π{A B : Type} (R : A → B → hProp)
  (a : A) (b : B) (r : R a b), (inL R a) = (inR R b).

definition RPushout_ind {A B : Type} {R : A → B → hProp}
  (P : RPushout R → Type)
  (i : Πa : A, P (inL R a)) (j : Πb : B, P (inR R b))
  (gl : Π(a : A) (b : B) (r : R a b), (glue R a b r) ▹ (i a) = (j b))
: Π(x : RPushout R), P x :=
   λx, (match x with inL a => (λ_, i a)
                        | inR b => (λ_, j b) end) gl.

Axiom RPushout_comp_glue : Π{A B : Type} {R : A → B → hProp}
  (P : RPushout R → Type)
  (i : Πa : A, P (inL R a)) (j : Πb : B, P (inR R b))
  (gl : Π(a : A) (b : B) (r : R a b), (glue R a b r) ▹ (i a) = (j b))
  (a : A) (b : B) (r : R a b),
apD (RPushout_ind P i j gl) (glue R a b r) = gl a b r.

End RPushout.

/- The non-depentent eliminator -/

definition RPushout_rec {A B : Type} (R : A → B → hProp)
  (P : Type) (i : A → P) (j : B → P)
  (gl : Π(a : A) (b : B) (r : R a b), (i a) = (j b))
: RPushout R → P :=
   RPushout_ind (λ_, P) i j (λa b r, transport_const _ _ ⬝ gl a b r).

definition RPushout_comp_nd_glue {A B : Type} (R : A → B → hProp)
  (P : Type) (i : A → P) (j : B → P)
  (gl : Π(a : A) (b : B) (r : R a b), (i a) = (j b))
  (a : A) (b : B) (r : R a b)
: ap (RPushout_rec R P i j gl) (glue R a b r) = gl a b r.
/-begin
  apply (cancelL (transport_const (glue R a b r) (i a))).
  transitivity (apD (RPushout_rec R P i j gl) (glue R a b r)).
  apply (apD_const (RPushout_rec R P i j gl) (glue R a b r))⁻¹.
  refine (RPushout_comp_glue (λ_, P) _ _ _ _ _ _).
end-/


/- Bitotal relation -/

definition bitotal {A B : Type} (R : A → B → hProp) :=
   (Πa : A, hexists (λ(b : B), R a b))
 × (Πb : B, hexists (λ(a : A), R a b)).

/- The cumulative hierarchy V -/

Module Export CumulativeHierarchy.

Private Inductive V : Type@{U'} :=
| set {A : Type@{U}} (f : A → V) : V.

Axiom setext : Π{A B : Type} (R : A → B → hProp)
  (bitot_R : bitotal R) (h : RPushout R → V),
set (h ∘ (inL R)) = set (h ∘ (inR R)).

Axiom is0trunc_V : is_trunc 0 V.

Fixpoint V_ind (P : V → Type)
  (H_0trunc : Πv : V, is_trunc 0 (P v))
  (H_set : Π(A : Type) (f : A → V) (H_f : Πa : A, P (f a)), P (set f))
  (H_setext : Π(A B : Type) (R : A → B → hProp) (bitot_R : bitotal R)
    (h : RPushout R → V) (H_h : Πx : RPushout R, P (h x)),
    (setext R bitot_R h) ▹ (H_set A (h ∘ inL R) (H_h oD inL R))
      = H_set B (h ∘ inR R) (H_h oD inR R) )
  (v : V)
: P v :=
   (match v with
     | set A f => λ_ _, H_set A f (λa, V_ind P H_0trunc H_set H_setext (f a))
    end) H_setext H_0trunc.

/- We don't need to axiomatize the computation rule because we get it for free thanks to 0-truncation -/

End CumulativeHierarchy.

definition V_comp_setext (P : V → Type)
  (H_0trunc : Πv : V, is_trunc 0 (P v))
  (H_set : Π(A : Type) (f : A → V) (H_f : Πa : A, P (f a)), P (set f))
  (H_setext : Π(A B : Type) (R : A → B → hProp) (bitot_R : bitotal R)
    (h : RPushout R → V) (H_h : Πx : RPushout R, P (h x)),
    (setext R bitot_R h) ▹ (H_set A (h ∘ inL R) (H_h oD inL R))
      = H_set B (h ∘ inR R) (H_h oD inR R) )
  (A B : Type) (R : A → B → hProp) (bitot_R : bitotal R) (h : RPushout R → V)
: apD (V_ind P H_0trunc H_set H_setext) (setext R bitot_R h)
  = H_setext A B R bitot_R h ((V_ind P H_0trunc H_set H_setext) oD h).
/-begin
  apply path_ishprop.
end-/

/- The non-dependent eliminator -/

definition V_rec (P : Type)
  (H_0trunc : is_trunc 0 P)
  (H_set : Π(A : Type), (A → V) → (A → P) → P)
  (H_setext : Π(A B : Type) (R : A → B → hProp) (bitot_R : bitotal R)
    (h : RPushout R → V) (H_h : RPushout R → P),
    H_set A (h ∘ inL R) (H_h ∘ inL R) = H_set B (h ∘ inR R) (H_h ∘ inR R) )
: V → P.
/-begin
  refine (V_ind _ _ H_set _).
  intros. exact (transport_const _ _ ⬝ H_setext A B R bitot_R h H_h).
end-/

definition V_comp_nd_setext (P : Type)
  (H_0trunc : is_trunc 0 P)
  (H_set : Π(A : Type), (A → V) → (A → P) → P)
  (H_setext : Π(A B : Type) (R : A → B → hProp) (bitot_R : bitotal R)
    (h : RPushout R → V) (H_h : RPushout R → P),
    H_set A (h ∘ inL R) (H_h ∘ inL R) = H_set B (h ∘ inR R) (H_h ∘ inR R) )
  (A B : Type) (R : A → B → hProp) (bitot_R : bitotal R) (h : RPushout R → V)
: ap (V_rec P H_0trunc H_set H_setext) (setext R bitot_R h)
  = H_setext A B R bitot_R h ((V_rec P H_0trunc H_set H_setext) ∘ h).
/-begin
  apply path_ishprop.
end-/


/- Alternative induction principle (This is close to the one from the book) -/

definition equal_img {A B C : Type} (f : A → C) (g : B → C) :=
   (Πa : A, hexists (λ(b : B), f a = g b))
 × (Πb : B, hexists (λ(a : A), f a = g b)).

definition setext' {A B : Type} (f : A → V) (g : B → V) (eq_img : equal_img f g)
: set f = set g.
/-begin
  pose (R := λa b, BuildhProp (f a = g b)).
  pose (h := RPushout_rec R V f g (λ_ _ r, r)).
  exact (setext R eq_img h).
end-/

definition V_rec' (P : Type)
  (H_0trunc : is_trunc 0 P)
  (H_set : Π(A : Type), (A → V) → (A → P) → P)
  (H_setext' : Π(A B : Type) (f : A → V) (g : B → V), (equal_img f g) ->
    Π(H_f : A → P) (H_g : B → P), (equal_img H_f H_g) ->
    (H_set A f H_f) = (H_set B g H_g) )
: V → P.
/-begin
  refine (V_rec _ _ H_set _).
  intros A B R bitot_R h H_h.
  apply H_setext'.
  - split.
    + intro a. generalize (pr1 bitot_R a). apply (Trunc_functor -1).
      intros [b r]. exists b. exact (ap h (glue R _ _ r)).
    + intro b. generalize (pr2 bitot_R b). apply (Trunc_functor -1).
      intros [a r]. exists a. exact (ap h (glue R _ _ r)).
  - split.
    + intro a. generalize (pr1 bitot_R a). apply (Trunc_functor -1).
      intros [b r]. exists b. exact (ap H_h (glue R _ _ r)).
    + intro b. generalize (pr2 bitot_R b). apply (Trunc_functor -1).
      intros [a r]. exists a. exact (ap H_h (glue R _ _ r)).
end-/

/- Note that the hypothesis H_setext' differs from the one given in section 10.5 of the HoTT book. -/
definition V_ind' (P : V → Type)
  (H_0trunc : Πv : V, is_trunc 0 (P v))
  (H_set : Π(A : Type) (f : A → V) (H_f : Πa : A, P (f a)), P (set f))
  (H_setext' : Π(A B : Type) (f : A → V) (g : B → V)
    (eq_img: equal_img f g)
    (H_f : Πa : A, P (f a)) (H_g : Πb : B, P (g b))
    (H_eqimg : (Πa : A, hexists (λ(b : B),
                  hexists (λ(p:f a = g b), p ▹ (H_f a) = H_g b)))
             × (Πb : B, hexists (λ(a : A),
                  hexists (λ(p:f a = g b), p ▹ (H_f a) = H_g b))) ),
    (setext' f g eq_img) ▹ (H_set A f H_f) = (H_set B g H_g)
  )
: Πv : V, P v.
/-begin
  apply V_ind with H_set; try assumption.
  intros A B R bitot_R h H_h.
  pose (f := h ∘ inL R : A → V ).
  pose (g := h ∘ inR R : B → V ).
  pose (H_f := H_h oD inL R : Πa : A, P (f a)).
  pose (H_g := H_h oD inR R : Πb : B, P (g b)).
  assert (eq_img : equal_img f g).
  { split.
    - intro a. generalize (pr1 bitot_R a). apply (Trunc_functor -1).
      intros [b r]. exists b. exact (ap h (glue R _ _ r)).
    - intro b. generalize (pr2 bitot_R b). apply (Trunc_functor -1).
      intros [a r]. exists a. exact (ap h (glue R _ _ r)). }
  transitivity (transport P (setext' (h ∘ inL R) (h ∘ inR R) eq_img)
      (H_set A (h ∘ inL R) (H_h oD inL R))).
  { apply (ap (λp, transport P p (H_set A (h ∘ inL R) (H_h oD inL R)))).
    apply path_ishprop. }
  apply (H_setext' A B f g eq_img H_f H_g).  split.
  - intro a.
    set (truncb := pr1 bitot_R a). generalize truncb.
    apply (Trunc_functor -1).
    intros [b Rab]. exists b.
    apply tr.
    exists (ap h (glue R _ _ Rab)).
    apply (concatR (apD H_h (glue R _ _ Rab))).
    apply inverse. unfold f, g, compose. apply transport_compose.
  - intros b.
    set (trunca := pr2 bitot_R b). generalize trunca.
    apply (Trunc_functor -1).
    intros [a Rab]. exists a.
    apply tr.
    exists (ap h (glue R _ _ Rab)).
    apply (concatR (apD H_h (glue R _ _ Rab))).
    apply inverse. unfold f, g, compose. apply transport_compose.
end-/


/- Simpler induction principle when the goal is an hprop -/

definition V_ind_hprop (P : V → Type)
  (H_set : Π(A : Type) (f : A → V) (H_f : Πa : A, P (f a)), P (set f))
  (isHProp_P : Πv : V, is_hprop (P v))
  : Πv : V, P v.
/-begin
  refine (V_ind _ _ H_set _).
  intros. apply path_ishprop.
end-/


section AssumingUA
Context {ua : Univalence}.

/- Membership relation -/

definition mem (x : V) : V → hProp.
/-begin
  refine (V_rec' _ _ _ _). intros A f _.
  exact (hexists (λa : A, f a = x)). simpl.
  intros A B f g eqimg _ _ _.
  apply path_iff_hprop; simpl.
  - intro H. refine (Trunc_rec _ H).
    intros [a p]. generalize (pr1 eqimg a). apply (Trunc_functor -1).
    intros [b p']. exists b. transitivity (f a); auto with path_hints.
  - intro H. refine (Trunc_rec _ H).
    intros [b p]. generalize (pr2 eqimg b). apply (Trunc_functor -1).
    intros [a p']. exists a. transitivity (g b); auto with path_hints.
end-/

Notation "x ∈ v" := (mem x v)
  (at level 30) : set_scope.
Open Scope set_scope.

/- Subset relation -/

definition subset (x : V) (y : V) : hProp :=
   BuildhProp (Πz : V, z ∈ x → z ∈ y).

Notation "x ⊆ y" := (subset x y)
  (at level 30) : set_scope.


/- Bisimulation relation -/
/- The equality in V lives in Type@{U'}. We define the bisimulation relation which is a U-small resizing of the equality in V: it must live in hProp_U : Type{U'}, hence the codomain is hProp@{U'}. We then prove that bisimulation is equality (bisim_equals_id), then use it to prove the key lemma monic_set_present. -/

/- We define bisimulation by double induction on V. We first fix the first argument as set(A,f) and define bisim_aux : V → hProp, by induction. This is the inner of the two inductions. -/
Local definition bisim_aux (A : Type) (f : A → V) (H_f : A → V → hProp) : V → hProp.
/-begin
  apply V_rec' with
    (λB g _, BuildhProp ( (Πa, hexists (λb, H_f a (g b)))
                               × Πb, hexists (λa, H_f a (g b)) )
    ).
  exact _.
  intros B B' g g' eq_img H_g H_g' H_img; simpl.
  apply path_iff_hprop; simpl.
  - intros [H1 H2]; split.
    + intro a. refine (Trunc_rec _ (H1 a)).
      intros [b H3]. generalize (pr1 eq_img b).
      unfold hexists. refine (@Trunc_functor -1 Σb0 : B', g b = g' b0 Σb0 : B', H_f a (g' b0) _).
      intros [b' p]. exists b'. exact (transport (λx, H_f a x) p H3).
    + intro b'. refine (Trunc_rec _ (pr2 eq_img b')).
      intros [b p]. generalize (H2 b). apply (Trunc_functor -1).
      intros [a H3]. exists a. exact (transport (λx, H_f a x) p H3).
  - intros [H1 H2]; split.
    + intro a. refine (Trunc_rec _ (H1 a)).
      intros [b' H3]. generalize (pr2 eq_img b'). apply (Trunc_functor -1).
      intros [b p]. exists b. exact (transport (λx, H_f a x) p⁻¹ H3).
    + intro b. refine (Trunc_rec _ (pr1 eq_img b)).
      intros [b' p]. generalize (H2 b'). apply (Trunc_functor -1).
      intros [a H3]. exists a. exact (transport (λx, H_f a x) p⁻¹ H3).
end-/

/- Then we define bisim : V → (V → hProp) by induction again -/
definition bisimulation : V@{U' U} → V@{U' U} → hProp@{U'}.
/-begin
  refine (V_rec' (V → hProp) _ bisim_aux _).
  intros A B f g eq_img H_f H_g H_img.
  apply path_forall.
  refine (V_ind_hprop _ _ _).
  intros C h _; simpl.
  apply path_iff_hprop; simpl.
  - intros [H1 H2]; split.
    + intro b. refine (Trunc_rec _ (pr2 H_img b)).
      intros [a p]. generalize (H1 a). apply (Trunc_functor -1).
      intros [c H3]. exists c. exact ((ap10 p (h c)) ▹ H3).
    + intro c. refine (Trunc_rec _ (H2 c)).
      intros [a H3]. generalize (pr1 H_img a). apply (Trunc_functor -1).
      intros [b p]. exists b. exact ((ap10 p (h c)) ▹ H3).
  - intros [H1 H2]; split.
    + intro a. refine (Trunc_rec _ (pr1 H_img a)).
      intros [b p]. generalize (H1 b). apply (Trunc_functor -1).
      intros [c H3]. exists c. exact ((ap10 p⁻¹ (h c)) ▹ H3).
    + intro c. refine (Trunc_rec _ (H2 c)).
      intros [b H3]. generalize (pr2 H_img b). apply (Trunc_functor -1).
      intros [a p]. exists a. exact ((ap10 p⁻¹ (h c)) ▹ H3).
end-/

Notation "u ~~ v" := (bisimulation u v)
  (at level 30) : set_scope.

definition reflexive_bisimulation [instance] : Reflexive bisimulation.
/-begin
  refine (V_ind_hprop _ _ _).
  intros A f H_f; simpl. split.
  - intro a; apply tr; exists a; auto.
  - intro a; apply tr; exists a; auto.
end-/

definition bisimulation_equiv_id : Πu v : V, (u = v) ≃ (u ~~ v).
/-begin
  intros u v.
  apply equiv_iff_hprop.
  intro p; exact (transport (λx, u ~~ x) p (reflexive_bisimulation u)).
  generalize u v.
  refine (V_ind_hprop _ _ _); intros A f H_f.
  refine (V_ind_hprop _ _ _); intros B g _.
  simpl; intros [H1 H2].
  apply setext'. split.
  - intro a. generalize (H1 a). apply (Trunc_functor -1).
    intros [b h]. exists b; exact (H_f a (g b) h).
  - intro b. generalize (H2 b). apply (Trunc_functor -1).
    intros [a h]. exists a; exact (H_f a (g b) h).
end-/


/- Canonical presentation of V-sets (definition 10.5.6) -/

/- Using the regular kernel (with = instead of ~~) also works, but this seems to be a Coq bug, it should lead to a universe inconsistency in the monic_set_present lemma later. This version is the right way to do it. -/
definition ker_bisim {A} (f : A → V) (x y : A) := (f x ~~ f y).

definition ker_bisim_is_ker {A} (f : A → V)
  : Π(x y : A), f x = f y ≃ ker_bisim f x y.
/-begin
  intros; apply bisimulation_equiv_id.
end-/
  
section MonicSetPresent_Uniqueness
/- Given u : V, we want to show that the representation u = @set Au mu, where Au is an hSet and mu is monic, is unique. -/

Context {u : V} {Au Au': Type} {h : IsHSet Au} {h' : IsHSet Au'} {mu : Au → V} {mono : IsEmbedding mu}
  {mu' : Au' → V} {mono' : IsEmbedding mu'} {p : u = set mu} {p' : u = set mu'}.

definition eq_img_untrunc : (Πa : Au, Σa' : Au', mu' a' = mu a)
                     × (Πa' : Au', Σa : Au, mu a = mu' a').
/-begin
  split.
  intro a. exact (@untrunc_istrunc -1 _ (mono' (mu a)) (transport (λx, mu a ∈ x) (p⁻¹ ⬝ p') (tr ⟨a, 1⟩))).
  intro a'. exact (@untrunc_istrunc -1 _ (mono (mu' a')) (transport (λx, mu' a' ∈ x) (p'⁻¹ ⬝ p) (tr ⟨a', 1⟩))).
end-/

Let e : Au → Au' := λa, dpr1 (pr1 eq_img_untrunc a).
Let inv_e : Au' → Au := λa', dpr1 (pr2 eq_img_untrunc a').

Let hom1 : Sect inv_e e.
/-begin
  intro a'.
  apply (isinj_embedding mu' mono').
  transitivity (mu (inv_e a')).
  exact (dpr2 (pr1 eq_img_untrunc (inv_e a'))).
  exact (dpr2 (pr2 eq_img_untrunc a')).
end-/

Let hom2 : Sect e inv_e.
/-begin
  intro a.
  apply (isinj_embedding mu mono).
  transitivity (mu' (e a)).
  exact (dpr2 (pr2 eq_img_untrunc (e a))).
  exact (dpr2 (pr1 eq_img_untrunc a)).
end-/

Let path : Au' = Au.
/-begin
  apply path_universe_uncurried.
  apply (equiv_adjointify inv_e e hom2 hom1).
end-/

definition mu_eq_mu' : transport (λA : Type, A → V) path⁻¹ mu = mu'.
/-begin
  apply path_forall. intro a'.
  transitivity (transport (λX, V) path⁻¹ (mu (transport (λX : Type, X) path⁻¹⁻¹ a'))).
  apply (@transport_arrow Type (λX : Type, X) (λX, V) Au Au' path⁻¹ mu a').
  transitivity (mu (transport idmap path⁻¹⁻¹ a')).
  apply transport_const.
  transitivity (mu (inv_e a')).
  2: apply (dpr2 (pr2 eq_img_untrunc a')).
  refine (ap mu _).
  transitivity (transport idmap path a').
  exact (ap (λx, transport idmap x a') (inv_V path)).
  apply transport_path_universe.
end-/

definition monic_set_present_uniqueness : (Au; (mu; (h, mono, p))) = (Au'; (mu'; (h', mono', p'))) :> ΣA : Type, Σm : A → V, IsHSet A × IsEmbedding m × (u = set m).
/-begin
  apply path_sigma_uncurried; simpl.
  exists path⁻¹.
  transitivity (path⁻¹ ▹ mu; transportD (λA, A → V) (λA m, IsHSet A × IsEmbedding m × (u = set m)) path⁻¹ mu (h, mono, p)).
  apply (@transport_sigma Type (λA, A → V) (λA m, IsHSet A × IsEmbedding m × (u = set m)) Au Au' path⁻¹ (mu; (h, mono, p))).
  apply path_sigma_hprop; simpl.
  exact mu_eq_mu'.
end-/

End MonicSetPresent_Uniqueness.

/- This lemma actually says a little more than 10.5.6, i.e., that Au is a hSet -/
definition monic_set_present : Πu : V, exists (Au : Type) (m : Au → V),
  (IsHSet Au) × (IsEmbedding m) × (u = set m).
/-begin
  apply V_ind_hprop.
  - intros A f _.
    destruct (quotient_kernel_factor f (ker_bisim f) (ker_bisim_is_ker f))
      as [Au [eu [mu (((hset_Au, epi_eu), mono_mu), factor)]]].
    exists Au, mu. split. exact (hset_Au, mono_mu).
    apply setext'; split.
    + intro a. apply tr; exists (eu a). exact (ap10 factor a).
    + intro a'. generalize (epi_eu a').
      intros ?; refine (Trunc_functor -1 _ (center _)).
      intros [a p]. exists a. transitivity (mu (eu a)).
      exact (ap10 factor a). exact (ap mu p).
  - intro v. apply hprop_allpath.
    intros [Au [mu ((hset, mono), p)]].
    intros [Au' [mu' ((hset', mono'), p')]].
    apply monic_set_present_uniqueness.
end-/

definition type_of_members (u : V) : Type := dpr1 (monic_set_present u).

Notation "[ u ]" := (type_of_members u)
  (at level 20) : set_scope.

definition func_of_members {u : V} : [u] → V := dpr1 (dpr2 (monic_set_present u)) : [u] → V.

definition is_hset_typeofmembers {u : V} : IsHSet ([u]) := pr1 (pr1 (dpr2 (dpr2 (monic_set_present u)))).

definition IsEmbedding_funcofmembers {u : V} : IsEmbedding func_of_members := pr2 (pr1 (dpr2 (dpr2 (monic_set_present u)))).

definition is_valid_presentation (u : V) : u = set func_of_members := pr2 (dpr2 (dpr2 (monic_set_present u))).


/- Lemmas 10.5.8 (i) & (vii), we put them here because they are useful later -/
definition extensionality : Π{x y : V}, (x ⊆ y × y ⊆ x) <-> x = y.
/-begin
  refine (V_ind_hprop _ _ _). intros A f _.
  refine (V_ind_hprop _ _ _). intros B g _.
  split.
  - intros [H1 H2]. apply setext'. split.
    + intro. refine (Trunc_rec _ (H1 (f a) (tr ⟨a,1⟩))).
      intros [b p]. apply tr. exists b. exact p⁻¹.
    + intro. apply (H2 (g b)). apply tr; exists b; reflexivity.
  - intro p; split.
    + intros z Hz. apply (transport (λx, z ∈ x) p Hz).
    + intros z Hz. apply (transport (λx, z ∈ x) p⁻¹ Hz).
Qed.

definition mem_induction (C : V → hProp)
: (Πv, (Πx, x ∈ v → C x) → C v) → Πv, C v.
Proof.
  intro H.
  refine (V_ind_hprop _ _ _).
  intros A f H_f. apply H. intros x Hx.
  generalize Hx; apply Trunc_rec.
  intros [a p]. exact (transport C p (H_f a)).
end-/

/- Two useful lemmas -/

definition irreflexive_mem [instance] : Irreflexive mem.
/-begin
  refine (mem_induction (λx, BuildhProp (~ x ∈ x)) _); simpl in *.
  intros v H. intro Hv.
  exact (H v Hv Hv).
end-/

definition path_V_eqimg {A B} {f : A → V} {g : B → V} : set f = set g → equal_img f g.
/-begin
  intro p. split.
  - intro a.
    assert (H : f a ∈ set g).
    { apply (pr2 extensionality p).
      apply tr; exists a; reflexivity. }
    generalize H; apply (Trunc_functor -1). intros [b p']. exists b; exact p'⁻¹.
  - intro b.
    assert (H : g b ∈ set f).
    { apply (pr2 extensionality p⁻¹).
      apply tr; exists b; reflexivity. }
    generalize H; apply (Trunc_functor -1). intros [a p']. exists a; exact p'.
end-/


/- Definitions of particular sets in V -/

/- The empty set -/
definition V_empty : V := set (Empty_ind (λ_, V)).

/- The singleton {u} -/
definition V_singleton (u : V) : V@{U' U} := set (Unit_ind u).

definition isequiv_ap_V_singleton [instance] {u v : V}
: is_equiv (@ap _ _ V_singleton u v).
/-begin
  refine (is_equiv.mk _ _ _ _ _ _ _); try solve [ intro; apply path_ishprop ].
  { intro H. specialize (path_V_eqimg H). intros (H1, H2).
    refine (Trunc_rec _ (H1 star)). intros [t p]. destruct t; exact p. }
end-/

/- The pair {u,v} -/
definition V_pair (u : V) (v : V) : V@{U' U} := set (λb : bool, if b then u else v).

definition path_pair {u v u' v' : V@{U' U}} : (u = u') × (v = v') → V_pair u v = V_pair u' v'.
/-begin
  intros (H1, H2). apply setext'. split.
  + apply Bool_ind. apply tr; exists tt. assumption.
    apply tr; exists ff; assumption.
  + apply Bool_ind. apply tr; exists tt; assumption.
    apply tr; exists ff; assumption.
end-/

definition pair_eq_singleton {u v w : V} : V_pair u v = V_singleton w <-> (u = w) × (v = w).
/-begin
  split.
  + intro H. destruct (path_V_eqimg H) as (H1, H2).
    refine (Trunc_rec _ (H1 tt)). intros [t p]; destruct t.
    refine (Trunc_rec _ (H1 ff)). intros [t p']; destruct t.
    split; [exact p| exact p'].
  + intros (p1, p2). apply setext'; split.
    intro a; apply tr; exists star. destruct a; [exact p1 | exact p2].
    intro t; apply tr; exists tt. destruct t; exact p1.
end-/

/- The ordered pair (u,v) -/
definition V_pair_ord (u : V) (v : V) : V := V_pair (V_singleton u) (V_pair u v).

Notation " [ u , v ] " := (V_pair_ord u v)
  (at level 20) : set_scope.

definition path_pair_ord {a b c d : V} : [a, b] = [c, d] <-> (a = c) × (b = d).
/-begin
  split.
  - intro p. assert (p1 : a = c).
    + assert (H : V_singleton a ∈ [c, d]).
      { apply (pr2 extensionality p). simpl.
        apply tr; exists tt; reflexivity. }
      refine (Trunc_rec _ H). intros [t p']; destruct t.
      apply ((ap V_singleton)⁻¹ p'⁻¹).
      apply symmetry. apply (pr1 pair_eq_singleton p').
    + split. exact p1.
      assert (H : hor (b = c) (b = d)).
      { assert (H' : V_pair a b ∈ [c, d]).
        { apply (pr2 extensionality p).
          apply tr; exists ff; reflexivity. }
        refine (Trunc_rec _ H'). intros [t p']; destruct t.
        × apply tr; left. apply (pr1 pair_eq_singleton p'⁻¹).
        × destruct (path_V_eqimg p') as (H1, H2).
          generalize (H2 ff); apply (Trunc_functor -1).
          intros [t p'']; destruct t.
          left; exact p''⁻¹. right; exact p''⁻¹. }
      refine (Trunc_rec _ H). intro case; destruct case as [p'| p'].
      2: assumption.
      assert (H' : [a, b] = V_singleton (V_singleton b)).
      { apply (pr2 pair_eq_singleton).
        split. apply ap; exact (p1 ⬝ p'⁻¹).
        apply (pr2 pair_eq_singleton).
        split; [exact (p1 ⬝ p'⁻¹) | reflexivity]. }
      assert (H'' : V_pair c d = V_singleton b)
        by apply (pr1 pair_eq_singleton (p⁻¹ ⬝ H')).
      apply symmetry. apply (pr1 pair_eq_singleton H'').
- intros (p, p').
  apply path_pair. split. apply ap; exact p.
  apply path_pair. split; assumption; assumption.
end-/

/- The cartesian product a × b -/
definition V_cart_prod (a : V) (b : V) : V :=
   set (λx : [a] × [b], [func_of_members (pr1 x), func_of_members (pr2 x)]).

Notation " a × b " := (V_cart_prod a b)
  (at level 25) : set_scope.

/- f is a function with domain a and codomain b -/
definition V_is_func (a : V) (b : V) (f : V) := f ⊆ a × b
 × (Πx, x ∈ a → hexists (λy, y ∈ b × [x,y] ∈ f))
 × (Πx y y', [x,y] ∈ f × [x,y'] ∈ f → y = y').

/- The set of functions from a to b -/
definition V_func (a : V) (b : V) : V :=
   @set ([a] → [b]) (λf, set (λx, [func_of_members x, func_of_members (f x)] )).

/- The union of a set Uv -/
definition V_union (v : V) :=
  @set (Σx : [v], [func_of_members x]) (λz, func_of_members (dpr2 z)).

/- The ordinal successor x ∪ {x} -/
definition V_succ : V → V.
/-begin
  refine (V_rec' _ _ _ _). intros A f _.
  exact (set (λ(x : A + unit), match x with inl a => f a
                                          | inr star => set f end)).
  simpl; intros A B f g eq_img _ _ _. apply setext'. split.
  - intro. destruct a.
    + generalize (pr1 eq_img a). apply (Trunc_functor -1).
      intros [b p]. exists (inl b); exact p.
    + apply tr; exists (inr star). destruct u. apply setext'; auto.
  - intro. destruct b.
    + generalize (pr2 eq_img b). apply (Trunc_functor -1).
      intros [a p]. exists (inl a); exact p.
    + apply tr; exists (inr star). destruct u. apply setext'; auto.
end-/

/- The set of finite ordinals -/
definition V_omega : V :=
   set (fix I n := match n with 0   => V_empty
                              | S n => V_succ (I n) end).


/- Axioms of set theory (theorem 10.5.8) -/

definition not_mem_Vempty : Πx, ~ (x ∈ V_empty).
Proof.
  intros x Hx. generalize Hx; apply Trunc_rec.
  intros [ff _]. exact ff.
Qed.

definition pairing : Πu v, hexists (λw, Πx, x ∈ w <-> hor (x = u) (x = v)).
Proof.
  intros u v. apply tr. exists (V_pair u v).
  intro; split; apply (Trunc_functor -1).
  - intros [[|] p]; [left|right]; exact p⁻¹.
  - intros [p | p]; [exists tt | exists ff]; exact p⁻¹.
Qed.

definition infinity : (V_empty ∈ V_omega) × (Πx, x ∈ V_omega → V_succ x ∈ V_omega).
Proof.
  split. apply tr; exists 0; auto.
  intro. apply (Trunc_functor -1).
  intros [n p]. exists (S n). rewrite p; auto.
Qed.

definition union : Πv, hexists (λw, Πx, x ∈ w <-> hexists (λu, x ∈ u × u ∈ v)).
Proof.
  intro v. apply tr; exists (V_union v).
  intro x; split.
  - intro H. simpl in H. generalize H; apply (Trunc_functor -1).
    intros [[u' x'] p]; simpl in p.
    exists (func_of_members u'); split.
    + refine (transport (λz, x ∈ z) (is_valid_presentation (func_of_members u'))⁻¹ _).
      simpl. apply tr; exists x'. exact p.
    + refine (transport (λz, func_of_members u' ∈ z) (is_valid_presentation v)⁻¹ _).
      simpl. apply tr; exists u'; reflexivity.
  - apply Trunc_rec. intros [u (Hx, Hu)].
    generalize (transport (λz, u ∈ z) (is_valid_presentation v) Hu).
    apply Trunc_rec. intros [u' pu].
    generalize (transport (λz, x ∈ z) (is_valid_presentation (func_of_members u')) (transport (λz, x ∈ z) pu⁻¹ Hx)).
    apply Trunc_rec. intros [x' px].
    apply tr. exists ⟨u', x'⟩. exact px.
Qed.

definition function : Πu v, hexists (λw, Πx, x ∈ w <-> V_is_func u v x).
Proof.
  intros u v. apply tr; exists (V_func u v).
  assert (memb_u : u = set (@func_of_members u)) by exact (is_valid_presentation u).
  assert (memb_v : v = set (@func_of_members v)) by exact (is_valid_presentation v).
  intro phi; split.
  - intro H. split. split.
    + intros z Hz. simpl in *. generalize H. apply Trunc_rec.
      intros [h p_phi]. generalize (transport (λx, z ∈ x) p_phi⁻¹ Hz). apply (Trunc_functor -1).
      intros [a p]. exists (a, h a). assumption.
    + intros x Hx. generalize (transport (λy, x ∈ y) memb_u Hx).
      apply Trunc_rec. intros [a p]. generalize H; apply (Trunc_functor -1).
      intros [h p_phi]. exists (func_of_members (h a)). split.
      exact (transport (λz, func_of_members (h a) ∈ z) memb_v⁻¹ (tr ⟨h a, 1⟩)).
      apply (transport (λy, [x, func_of_members (h a)] ∈ y) p_phi).
      apply tr; exists a. rewrite p; reflexivity.
    + intros x y y' (Hy, Hy'). generalize H; apply Trunc_rec. intros [h p_phi].
      generalize (transport (λz, [x, y] ∈ z) p_phi⁻¹ Hy). apply Trunc_rec. intros [a p].
      generalize (transport (λz, [x, y'] ∈ z) p_phi⁻¹ Hy'). apply Trunc_rec. intros [a' p'].
      destruct (pr1 path_pair_ord p) as (px, py). destruct (pr1 path_pair_ord p') as (px', py').
      transitivity (func_of_members (h a)); auto with path_hints. transitivity (func_of_members (h a'));auto with path_hints.
      refine (ap func_of_members _). refine (ap h _).
      apply (isinj_embedding func_of_members IsEmbedding_funcofmembers a a' (px ⬝ px'⁻¹)).
  - intros ((H1, H2), H3). simpl.
    assert (h : Πa : [u], Σb : [v], [func_of_members a, func_of_members b] ∈ phi).
    { intro a. pose (x := func_of_members a).
      transparent assert (H : Σy : V, y ∈ v × [x, y] ∈ phi).
      refine (@untrunc_istrunc -1 Σy : V, y ∈ v × [x, y] ∈ phi _
                                 (H2 x (transport (λz, x ∈ z) memb_u⁻¹ (tr ⟨a, 1⟩)))).
      { apply hprop_allpath. intros [y (H1_y, H2_y)] [y' (H1_y', H2_y')].
        apply path_sigma_uncurried; simpl.
        exists (H3 x y y' (H2_y, H2_y')).
        apply path_ishprop. }
      destruct H as [y (H1_y, H2_y)].
      destruct (@untrunc_istrunc -1 _ (IsEmbedding_funcofmembers y) (transport (λz, y ∈ z) memb_v H1_y)) as [b Hb].
      exists b. exact (transport (λz, [x, z] ∈ phi) Hb⁻¹ H2_y). }
    apply tr; exists (λa, dpr1 (h a)). apply extensionality. split.
    + intros z Hz. generalize Hz; apply Trunc_rec. intros [a Ha].
      exact (transport (λw, w ∈ phi) Ha (dpr2 (h a))).
    + intros z Hz. simpl.
      generalize (H1 z Hz). apply (Trunc_functor -1). intros [(a,b) p]. simpl in p.
      exists a. transitivity ([func_of_members a, func_of_members b]); auto with path_hints.
      apply ap.
      apply H3 with (func_of_members a). split.
      exact (dpr2 (h a)).
      exact (transport (λw, w ∈ phi) p⁻¹ Hz).
Qed.

definition replacement : Π(r : V → V) (x : V),
  hexists (λw, Πy, y ∈ w <-> hexists (λz, z ∈ x × (r z = y))).
Proof.
  intro r. refine (V_ind_hprop _ _ _).
  intros A f _. apply tr. exists (set (r ∘ f)). split.
  - apply (Trunc_functor -1).
    intros [a p]. exists (f a). split. apply tr; exists a; auto. assumption.
  - apply Trunc_rec.
    intros [z [h p]]. generalize h. apply (Trunc_functor -1).
    intros [a p']. exists a. transitivity (r z); auto with path_hints. exact (ap r p').
Qed.

definition separation (C : V → hProp) : Πa : V,
  hexists (λw, Πx, x ∈ w <-> x ∈ a × (C x)).
Proof.
  refine (V_ind_hprop _ _ _).
  intros A f _. apply tr. exists (set (λz : Σa : A, C (f a), f (dpr1 z))). split.
  - apply Trunc_rec.
    intros [[a h] p]. split. apply tr; exists a; assumption. exact (transport C p h).
  - intros [H1 H2]. generalize H1. apply (Trunc_functor -1).
    intros [a p]. exists ⟨a, transport C p⁻¹ H2⟩. exact p.
Qed.

End AssumingUA.
