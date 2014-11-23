/- We prove that Fam and Pow are equivalent.
This equivalence is close to the existence of an object classifier.
-/

Require Import HoTT.Basics.
Require Import Types.Universe Types.Sigma Types.Arrow.
Require Import Fibrations HProp EquivalenceVarieties UnivalenceImpliesFunext.
Local Open Scope equiv_scope.
Local Open Scope path_scope.

section AssumeUnivalence
Context {ua:Univalence}.

/- This should be moved. -/
definition pullback {A0 B C} (f:B-> A0) (g:C->A0):= Σb:B, Σc:C, f b ≈ g c.

section FamPow
/- We consider Families and Powers over a fixed type [A] -/
Variable A:Type.
definition Fam A:=sigT (λI:Type , I->A).
definition p2f: (A->Type)-> Fam A:=  λQ:(A->Type), ( (sigT Q) ; @dpr1 _ _).
definition f2p: Fam A → (A->Type):=
 λF, let (I, f) := F in (λa, (hfiber f a)).

/- This is generalized in Functorish.v -/
Theorem transport_exp (U V:Type)(w:U≃V): Π(f:U->A),
  (transport (λI:Type, I->A) (path_universe w) f) ≈ (f ∘ w⁻¹).
/-begin
  intros f; apply path_arrow; intros y.
  refine (transport_arrow_toconst _ _ _ ⬝ _).
  unfold compose; apply ap.
  by apply transport_path_universe_V.
Qed.

Theorem FamequivPow : (A->Type)≃(Fam A).
Proof.
apply (equiv_adjointify p2f f2p).
/- Theorem right (F:Fam A) : F ≈ (p2ff2p F) -/
 +intros [I f]. set (e:=equiv_path_sigma _ (@existT Type (λI0 : Type, I0 → A) I f)
  (Σa : A, hfiber f a ; @dpr1 _ _)). simpl in e.
  enough (X:{p : I ≈ Σa : A, @hfiber I A f a &
     @transport _ (λI0 : Type, I0 → A) _ _ p f ≈ @dpr1 _ _}) by apply (e X)⁻¹.
  set (w:=@equiv_fibration_replacement A I f).
  exists (path_universe w). 
  transitivity (f ∘ w⁻¹);[apply transport_exp|apply path_forall;by (intros [a [i p]])].
 /- Theorem left (P:A → Type) : (f2pp2f P) ≈ P -/
 + intro P. by_extensionality a.
 apply ((path_universe (@hfiber_fibration  _ a P))⁻¹).
end-/

/- We construct the universal diagram for the object classifier -/
definition topmap {B} (f:B->A) (b:B): pointedType :=
  (hfiber f (f b) ; (b ; idpath (f b))).

Local definition help_objclasspb_is_fibrantreplacement (P:A-> Type): (sigT P)->
  (pullback P (@dpr1 _ (λu :Type, u))):=
(λ(X : Σa : A, P a), (λ(a : A) (q : P a), (a; (⟨P a, q⟩; 1))) X.1 X.2).

Local definition help_objclasspb_is_fibrantreplacement2 (P:A-> Type):
 (pullback P (@dpr1 _ (λu :Type, u))) → (sigT P).
intros [a [[T t] p]]. exact (a;(transport (λX, X) (p⁻¹) t)).
Defined.

Lemma objclasspb_is_fibrantreplacement (P:A-> Type): (sigT P) ≃ (pullback P (@dpr1 _ (λu :Type, u))).
/-begin
exists (help_objclasspb_is_fibrantreplacement P).
apply isequiv_biinv. split; exists (help_objclasspb_is_fibrantreplacement2 P); intros [a p]. apply idpath.
destruct p as [[T t] p].
refine (path_sigma' _ (idpath a) _).
simpl in p. by path_induction.
Qed.

End FamPow.

section Subobjectclassifier
/- We prove that hProp is the subobject classifier -/
/- In fact, the proof works for general mere predicates on [Type], 
not just [IsHProp], truncations and modalities are important examples.-/
Variable A:Type.
Variable isP:Type → Type.
Variable ishprop_isP: ΠI, is_hprop (isP I).
definition IsPfibered {I} (f:I->A):=Πi, isP (hfiber f i).
definition PFam := (sig (λF:Fam A, IsPfibered (dpr2 F))).
/- Bug: abstract should accept more than one tactic.
https://coq.inria.fr/bugs/show_bug.cgi?id=3609
Alternatively, we would like to use [Program] here.
6a99db1c31fe267fdef7be755fa169fb6a87e3cf
Instead we split the [Definition] and first make a [Local Definition] -/
Local definition pow2Pfam_pf (P:Πa:A, ΣX :Type, isP X): 
           IsPfibered (dpr2 (p2f A (dpr1 ∘ P))). 
Proof.
intro i. cbn. 
rewrite <- (path_universe_uncurried (@hfiber_fibration A i (dpr1 ∘ P))).
apply ((P i).2).
Qed.

definition pow2Pfam (P:Πa:A, ΣX :Type, isP X): PFam:=
  (p2f A (λa, (dpr1 (P a))); pow2Pfam_pf P).

Local definition Pfam2pow_pf (F:PFam)(a:A):isP (f2p A F.1 a). 
unfold f2p. by destruct F as [[I f] p].
Qed.

definition Pfam2pow (F:PFam) (a:A): ΣX :Type, isP X:=
   ((f2p A F.1 a); (Pfam2pow_pf F a)).

Theorem PowisoPFam : (Πa:A, ΣX :Type, isP X)≃PFam.
Proof.
apply (equiv_adjointify pow2Pfam Pfam2pow).
 + intros [[B f] q]. apply path_sigma_hprop. cbn.
  refine (@eisretr _ _ (FamequivPow A) _ ⟨B,f⟩).
+ intro P. apply path_forall. intro a.
 assert (f2p A (p2f A (dpr1 ∘ P)) a ≈ (dpr1 (P a))).
  set (p:=@eissect _ _ (FamequivPow A) _).
  apply (ap10 (p (dpr1 ∘ P)) a).
by apply path_sigma_hprop.
end-/
End Subobjectclassifier.

End AssumeUnivalence.
