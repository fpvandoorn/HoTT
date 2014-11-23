/- -*- mode: coq; mode: visual-line -*- -/
/- Varieties of function extensionality -/

Require Import Overture PathGroupoids Contractible Equivalences UniverseLevel.
Local Open Scope path_scope.

/- In the Overture, we defined function extensionality to be the assertion that the map [apD10] is an equivalence.   We now prove that this follows from a couple of weaker-looking forms of function extensionality.  We do require eta conversion, which Coq 8.4+ has judgmentally.

   This proof is originally due to Voevodsky; it has since been simplified by Peter Lumsdaine and Michael Shulman. -/

/- Naive funext is the simple assertion that pointwise equal functions are equal. -/

definition NaiveFunext :=
  Π(A : Type) (P : A → Type) (f g : Πx, P x),
    (Πx, f x ≈ g x) → (f ≈ g).

/- Weak funext says that a product of contractible types is contractible. -/

definition WeakFunext :=
  Π(A : Type) (P : A → Type),
    (Πx, is_contr (P x)) → is_contr (Πx, P x).

/- We define a variant of [Funext] which does not invoke an axiom. -/
definition Funext_type :=
  Π(A : Type) (P : A → Type) f g, IsEquiv (@apD10 A P f g).

/- The obvious implications are
   Funext → NaiveFunext → WeakFunext
   -/

definition Funext_implies_NaiveFunext : Funext_type → NaiveFunext.
/-begin
  intros fe A P f g h.
  unfold Funext_type in *.
  exact ((@apD10 A P f g)⁻¹ h)%equiv.
end-/

definition NaiveFunext_implies_WeakFunext : NaiveFunext → WeakFunext.
/-begin
  intros nf A P Pc.
  exists (λx, center (P x)).
  intros f; apply nf; intros x.
  apply contr.
end-/

/- The less obvious direction is that WeakFunext implies Funext (and hence all three are logically equivalent).  The point is that under weak funext, the space of "pointwise homotopies" has the same universal property as the space of paths. -/

section Homotopies

  Context (wf : WeakFunext).
  Context {A:Type} {B : A → Type}.

  Context (f : Πx, B x).

  /- Recall that [f == g] is the type of pointwise paths (or "homotopies") from [f] to [g]. -/
  Let idhtpy : f == f := λx, idpath (f x).

  /- Weak funext implies that the "based homotopy space" of the Pi-type is contractible, just like the based path space. -/
  /- Use priority 1, so we don't override [Contr unit]. -/
  definition contr_basedhtpy [instance] : is_contr Σg : Πx, B x, f == g  | 1.
  /-begin
    exists ⟨f,idhtpy⟩. intros [g h].
    /- The trick is to show that the type [Σg : Πx, B x, f == g ] is a retract of [Πx, Σy : B x, f x ≈ y], which is contractible due to J and weak funext.  Here are the retraction and its section. -/
    pose (r := λk, existT (λg, f == g)
      (λx, (k x).1) (λx, (k x).2)).
    pose (s := λ(g : Πx, B x) (h : f == g) x, ⟨g x , h x⟩).
    /- Because of judgemental eta-conversion, the retraction is actually definitional, so we can just replace the goal. -/
    change (r (λx, (f x ; idpath (f x))) ≈ r (s g h)).
    apply ap; refine (@path_contr _ _ _ _).
    apply wf. intros x; exact (contr_basedpaths (f x)).
  end-/

  /- This enables us to prove that pointwise homotopies have the same elimination rule as the identity type. -/

  Context (Q : Πg (h : f == g), Type).
  Context (d : Q f idhtpy).

  definition htpy_ind g h : Q g h :=
       @transport _ (λgh, Q gh.1 gh.2) ⟨f,idhtpy⟩ ⟨g,h⟩
         (@path_contr _ _ _ _) d.

  /- The computation rule, of course, is only propositional. -/
  definition htpy_ind_beta : htpy_ind f idhtpy ≈ d :=
       transport (λp : ⟨f,idhtpy⟩ ≈ ⟨f,idhtpy⟩,
                    transport (λgh, Q gh.1 gh.2) p d ≈ d)
         (@path2_contr _ _ _ _
           (path_contr ⟨f,idhtpy⟩ ⟨f,idhtpy⟩) (idpath _))⁻¹
         (idpath _).

End Homotopies.

/- Now the proof is fairly easy; we can just use the same induction principle on both sides. -/
definition WeakFunext_implies_Funext : WeakFunext → Funext_type.
/-begin
  intros wf; hnf; intros A B f g.
  refine (isequiv_adjointify (@apD10 A B f g)
    (htpy_ind wf f (λg' _, f ≈ g') idpath g) _ _).
  revert g; refine (htpy_ind wf _ _ _).
    refine (ap _ (htpy_ind_beta wf _ _ _)).
  intros h; destruct h.
    refine (htpy_ind_beta wf _ _ _).
end-/

/- We add some hints to the typeclass database, so if we happen to have hypotheses of [WeakFunext] or [NaiveFunext] floating around, we get [Funext] automatically. -/
definition NaiveFunext_implies_Funext : NaiveFunext → Funext_type :=
     WeakFunext_implies_Funext ∘ NaiveFunext_implies_WeakFunext.

/- Functional extensionality is downward closed -/
/- If universe [U_i] is functionally extensional, then so are universes [U_j] for [j ≤ i]. -/
definition Funext_downward_closed {H : Funext_type} : Funext_type.
/-begin
  apply @NaiveFunext_implies_Funext.
  apply Funext_implies_NaiveFunext in H.
  hnf in *.
  intros A P f g H'.
  /- We want to just use [H] here.  But we need to adjust the universe level in four places: for [A], for [P], for the input path, and for the output path. -/
  case (H (Lift A) (λx, Lift (P x)) f g (λx, ap lift (H' x))).
  exact idpath.
end-/
