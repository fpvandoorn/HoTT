Require Import HoTT.Basics Types.Universe Types.Paths Types.unit.

Generalizable All Variables.

/- Univalence Implies Functional Extensionality -/

/- Here we prove that univalence implies function extensionality. -/

/- We define an axiom-free variant of [Univalence] -/
definition Univalence_type := Π(A B : Type), is_equiv (equiv_path A B).

section UnivalenceImpliesfunext
  Context {ua : Univalence_type}.

  /- Exponentiation preserves equivalences, i.e., if [e] is an equivalence then so is post-composition by [e]. -/

  /- Should this go somewhere else? -/

  definition univalence_isequiv_postcompose {H0 : is_equiv A B w} C : is_equiv (@compose C A B w).
  /-begin
    unfold Univalence_type in *.
    refine (isequiv_adjointify
              (@compose C A B w)
              (@compose C B A w⁻¹)%equiv
              _
              _);
    intro;
    pose (equiv.mk _ _ w _) as w';
    change H0 with (@equiv_isequiv _ _ w');
    change w with (@equiv_fun _ _ w');
    clearbody w'; clear H0 w;
    rewrite <- (@retr _ _ (@equiv_path A B) (ua A B) w');
    generalize ((@equiv_inv _ _ (equiv_path A B) (ua A B)) w')%equiv;
    intro p;
    clear w';
    destruct p;
    reflexivity.
  end-/

  /- We are ready to prove functional extensionality, starting with the naive non-dependent version. -/

  Local Instance isequiv_src_compose A B
  : @is_equiv (A → Σxy : B × B, pr1 xy = pr2 xy)
             (A → B)
             (compose (pr1 ∘ dpr1)).
  /-begin
    apply @univalence_isequiv_postcompose.
    refine (isequiv_adjointify
              (pr1 ∘ dpr1) (λx, ((x, x); refl))
              (λ_, refl)
              _);
      let p := fresh in
      intros [[? ?] p];
        simpl in p; destruct p;
        reflexivity.
  end-/


  Local Instance isequiv_tgt_compose A B
  : @is_equiv (A → Σxy : B × B, pr1 xy = pr2 xy)
             (A → B)
             (compose (pr2 ∘ dpr1)).
  /-begin
    apply @univalence_isequiv_postcompose.
    refine (isequiv_adjointify
              (pr2 ∘ dpr1) (λx, ((x, x); refl))
              (λ_, refl)
              _);
      let p := fresh in
      intros [[? ?] p];
        simpl in p; destruct p;
        reflexivity.
  end-/

  definition Univalence_implies_funextNondep (A B : Type)
  : Πf g : A → B, f ∼ g → f = g.
  /-begin
    intros f g p.
    /- Consider the following maps. -/
    pose (d := λx : A, existT (λxy, pr1 xy = pr2 xy) (f x, f x) (refl (f x))).
    pose (e := λx : A, existT (λxy, pr1 xy = pr2 xy) (f x, g x) (p x)).
    /- If we compose [d] and [e] with [free_path_target], we get [f] and [g], respectively. So, if we had a path from [d] to [e], we would get one from [f] to [g]. -/
    change f with ((pr2 ∘ dpr1) ∘ d).
    change g with ((pr2 ∘ dpr1) ∘ e).
    apply ap.
    /- Since composition with [src] is an equivalence, we can freely compose with [src]. -/
    pose (λA B x y, @equiv_inv _ _ _ (@isequiv_ap _ _ _ (@isequiv_src_compose A B) x y)) as H'.
    apply H'.
    reflexivity.
  end-/
End UnivalenceImpliesfunext.

section UnivalenceImpliesWeakfunext
  Context {ua1 : Univalence_type, ua2 : Univalence_type}.
  /- Now we use this to prove weak funext, which as we know implies (with dependent eta) also the strong dependent funext. -/

  definition Univalence_implies_Weakfunext : Weakfunext.
  Proof.
    intros A P allcontr.
    /- We are going to replace [P] with something simpler. -/
    pose (U := (λ(_ : A), unit)).
    assert (p : P = U).
    - apply (@Univalence_implies_funextNondep ua2).
      intro x.
      apply (@equiv_inv _ _ _ (ua1 _ _)).
      apply equiv_contr_unit.
    - /- Now this is much easier. -/
      rewrite p.
      unfold U; simpl.
      exists (λ_, star).
      intro f.
      apply (@Univalence_implies_funextNondep ua2).
      intro x.
      destruct (@contr unit _ (f x)).
      reflexivity.
  Qed.
End UnivalenceImpliesWeakfunext.

definition Univalence_type_implies_funext_type {ua1 : Univalence_type, ua2 : Univalence_type} : funext_type :=
     Weakfunext_implies_funext (@Univalence_implies_Weakfunext ua1 ua2).

/- As justified by the above proof, we may assume [Univalence → funext]. -/
definition Univalence_implies_funext [instance] [H : Univalence] : funext.
Admitted.
