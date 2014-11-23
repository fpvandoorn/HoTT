/- Grothendieck Construction of a pseudofunctor to Cat -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Pseudofunctor.Core Pseudofunctor.RewriteLaws.
Require Import Category.Morphisms NaturalTransformation.Isomorphisms Cat.Morphisms.
Require Import Functor.Composition.Core Functor.Composition.Laws.
Require Import Functor.Identity.
Require Import FunctorCategory.Core.
Require Import Types.Sigma HoTT.Tactics PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

section Grothendieck
  Context [H : Funext].

  Variable C : PreCategory.
  Variable F : Pseudofunctor C.

  Record Pair :=
    {
      c : C;
      x : object (F c)
    }.

  Local Notation morphism s d :=
    { f : morphism C s.(c) d.(c)
    | morphism _ (p_morphism_of F f s.(x)) d.(x) }.

  definition compose s d d'
             (m1 : morphism d d')
             (m2 : morphism s d)
  : morphism s d'.
  /-begin
    exists (m1.1 ∘ m2.1).
    refine (m1.2 ∘ ((p_morphism_of F m1.1) _1 m2.2 ∘ _)).
    apply (p_composition_of F).
  end-/

  definition identity s : morphism s s.
  /-begin
    exists 1.
    apply (p_identity_of F).
  end-/

  Global Arguments identity _ / .
  Global Arguments compose _ _ _ _ _ / .

  Local Ltac try_associativity_f_ap :=
    first [ f_ap; []
          | repeat (etransitivity; [ apply Category.Core.associativity | ]);
            repeat (etransitivity; [ | symmetry; apply Category.Core.associativity ]);
            f_ap; []
          | repeat (etransitivity; [ symmetry; apply Category.Core.associativity | ]);
            repeat (etransitivity; [ | apply Category.Core.associativity ]);
            f_ap; [] ].

  Local Ltac assoc_before_commutes_tac :=
    rewrite !composition_of;
    rewrite <- !Category.Core.associativity;
    etransitivity; [ | symmetry; apply compose4associativity_helper ].

  Local Ltac assoc_fin_tac :=
    repeat match goal with
             | _ => reflexivity
             | _ => progress rewrite ?Category.Core.left_identity, ?Category.Core.right_identity
             | [ |- context[components_of ?T ?x ∘ components_of ?T⁻¹ ?x] ]
               => simpl rewrite (@iso_compose_pV _ _ _ (T x) _)
             | _ => try_associativity_quick
                      first [ f_ap; []
                            | apply concat_left_identity
                            | apply concat_right_identity ]
             | _ => rewrite <- ?identity_of, <- ?composition_of;
                   progress repeat ⟨f_ap, []⟩;
                   rewrite ?identity_of, ?composition_of
             | _ => try_associativity_quick rewrite compose4associativity_helper
           end.

  Local Ltac helper_t before_commutes_tac :=
    repeat intro;
    symmetry;
    apply path_sigma_uncurried;
    simpl in *;
    let ex_hyp := match goal with
                    | [ H : ?A ≈ ?B |- @sigT (?B ≈ ?A) _ ] => constr:(H)
                  end in
    (exists (inverse ex_hyp));
      simpl;
      rewrite ?transport_Fc_to_idtoiso, ?transport_cF_to_idtoiso;
      rewrite ?idtoiso_inv, ?ap_V, ?inv_V;
      simpl;
      let rew_hyp := match goal with
                       | [ H' : context[ex_hyp] |- _ ] => constr:(H')
                     end in
      rewrite rew_hyp;
        clear rew_hyp ex_hyp;
        before_commutes_tac;
        repeat first [ reflexivity
                     | progress rewrite ?Category.Core.left_identity, ?Category.Core.right_identity
                     | try_associativity_quick ⟨f_ap, []⟩ ];
        match goal with
          | _ => reflexivity
          | [ |- context[morphism_of ?F ?m ∘ components_of ?T ?x] ]
            => simpl rewrite <- (commutes T _ _ m);
              try reflexivity
          | [ |- context[components_of ?T ?x ∘ morphism_of ?F ?m] ]
            => simpl rewrite (commutes T _ _ m);
              try reflexivity
        end.

  /- The goal for, e.g., the following associativity helper was made
  with the following code:
<<
intros a b c d [f f'] [g g'] [h h']; simpl.
    pose proof (apD10 (ap components_of (p_composition_ofCoherent_for_rewrite F _ _ _ _ f g h))) as rew_hyp.
    revert rew_hyp.
    generalize dependent (Category.Core.associativity C _ _ _ _ f g h). intros fst_hyp ?.

    simpl in *.
    hnf in rew_hyp.
    simpl in *.

    Local Ltac gen_x x :=
      generalize dependent (X x);
      generalize dependent (C x);
      repeat (let x1 := fresh "x" in intro x1).
    gen_x a.
    gen_x b.
    gen_x c.
    gen_x d.
    repeat match goal with
             | [ |- context[p_identity_of ?F ?x] ]
               => generalize dependent (p_identity_of F x)
             | [ |- context[p_composition_of ?F ?x ?y ?z ?f ?g] ]
               => generalize dependent (p_composition_of F x y z f g)
             | [ |- context[p_morphism_of ?F ?m] ]
               => generalize dependent (p_morphism_of F m)
             | [ |- context[p_object_of ?F ?x] ]
               => generalize dependent (p_object_of F x)
             | [ H : context[p_morphism_of ?F ?m] |- _ ]
               => generalize dependent (p_morphism_of F m)
             | [ |- context[@p_morphism_of _ _ ?F ?x ?y] ]
               => generalize dependent (@p_morphism_of _ _ F x y)
           end.
    simpl.

    intros.

    lazymatch goal with
      | [ H : context[ap ?f ?H'] |- _ ]
        => rename H' into fst_hyp;
          rename H into rew_hyp;
          move rew_hyp at top
    end.

    generalize dependent fst_hyp.
    clear.
    intros.
    move rew_hyp at top.

    move H at top.

    repeat match goal with
             | [ H : Isomorphic _ _ |- _ ]
               => let x := fresh "x" in
                  let H' := fresh "H" in
                  destruct H as [x H'];
                    simpl in *
           end.
    move rew_hyp at top.
    repeat match goal with
             | [ H : _ |- _ ] => revert H
           end.

    intro H.
    intro C.
>> -/

  Lemma pseudofunctor_to_cat_assoc_helper
  : Π{x x0 : C} {x2 : Category.Core.morphism C x x0} {x1 : C}
           {x5 : Category.Core.morphism C x0 x1} {x4 : C} {x7 : Category.Core.morphism C x1 x4}
           {p p0 : PreCategory} {f : Category.Core.morphism C x x4 → Functor p0 p}
           {p1 p2 : PreCategory} {f0 : Functor p2 p} {f1 : Functor p1 p2}
           {f2 : Functor p0 p2} {f3 : Functor p0 p1} {f4 : Functor p1 p}
           {x16 : Category.Core.morphism (_ → _) (f (x7 ∘ x5 ∘ x2)) (f4 ∘ f3)%functor}
           {x15 : Category.Core.morphism (_ → _) f2 (f1 ∘ f3)%functor} {H2 : IsIsomorphism x15}
           {x11 : Category.Core.morphism (_ → _) (f (x7 ∘ (x5 ∘ x2))) (f0 ∘ f2)%functor}
           {H1 : IsIsomorphism x11} {x9 : Category.Core.morphism (_ → _) f4 (f0 ∘ f1)%functor}
           {fst_hyp : x7 ∘ x5 ∘ x2 ≈ x7 ∘ (x5 ∘ x2)}
           (rew_hyp : Πx3 : p0,
                        (idtoiso (p0 → p) (ap f fst_hyp) : Category.Core.morphism _ _ _) x3 =
                        x11⁻¹ x3 ∘ (f0 _1 (x15⁻¹ x3) ∘ (1 ∘ (x9 (f3 x3) ∘ x16 x3))))
           {H0' : IsIsomorphism x16}
           {H1' : IsIsomorphism x9}
           {x13 : p} {x3 : p0} {x6 : p1} {x10 : p2}
           {x14 : Category.Core.morphism p (f0 x10) x13} {x12 : Category.Core.morphism p2 (f1 x6) x10}
           {x8 : Category.Core.morphism p1 (f3 x3) x6},
      existT (λf5 : Category.Core.morphism C x x4, Category.Core.morphism p ((f f5) x3) x13)
             (x7 ∘ x5 ∘ x2)
             (x14 ∘ (f0 _1 x12 ∘ x9 x6) ∘ (f4 _1 x8 ∘ x16 x3)) =
      (x7 ∘ (x5 ∘ x2); x14 ∘ (f0 _1 (x12 ∘ (f1 _1 x8 ∘ x15 x3)) ∘ x11 x3)).
  /-begin
    helper_t assoc_before_commutes_tac.
    assoc_fin_tac.
  Qed.

  Lemma pseudofunctor_to_cat_left_identity_helper
  : Π{x1 x2 : C} {f : Category.Core.morphism C x2 x1} {p p0 : PreCategory}
           {f0 : Category.Core.morphism C x2 x1 → Functor p0 p} {f1 : Functor p p}
           {x0 : Category.Core.morphism (_ → _) (f0 (1 ∘ f)) (f1 ∘ f0 f)%functor}
           {x : Category.Core.morphism (_ → _) f1 1%functor}
           {fst_hyp : 1 ∘ f ≈ f}
           (rewrite_hyp : Πx3 : p0,
                            (idtoiso (p0 → p) (ap f0 fst_hyp) : Category.Core.morphism _ _ _) x3
                            ≈ 1 ∘ (x ((f0 f) x3) ∘ x0 x3))
           {H0' : IsIsomorphism x0}
           {H1' : IsIsomorphism x}
           {x3 : p} {x4 : p0} {f' : Category.Core.morphism p ((f0 f) x4) x3},
      existT (λf2 : Category.Core.morphism C x2 x1, Category.Core.morphism p ((f0 f2) x4) x3)
             (1 ∘ f)
             (x x3 ∘ (f1 _1 f' ∘ x0 x4))
      ≈ ⟨f, f'⟩.
  Proof.
    helper_t idtac.
  Qed.

  Lemma pseudofunctor_to_cat_right_identity_helper
  : Π{x1 x2 : C} {f : Category.Core.morphism C x2 x1} {p p0 : PreCategory}
           {f0 : Category.Core.morphism C x2 x1 → Functor p0 p} {f1 : Functor p0 p0}
           {x0 : Category.Core.morphism (_ → _) (f0 (f ∘ 1)) (f0 f ∘ f1)%functor}
           {H0' : IsIsomorphism x0}
           {x : Category.Core.morphism (_ → _) f1 1%functor}
           {H1' : IsIsomorphism x}
           {fst_hyp : f ∘ 1 ≈ f}
           (rew_hyp : Πx3 : p0,
                        (idtoiso (p0 → p) (ap f0 fst_hyp) : Category.Core.morphism _ _ _) x3
                        ≈ 1 ∘ ((f0 f) _1 (x x3) ∘ x0 x3))
           {x3 : p} {x4 : p0} {f' : Category.Core.morphism p ((f0 f) x4) x3},
        existT (λf2 : Category.Core.morphism C x2 x1, Category.Core.morphism p ((f0 f2) x4) x3)
               (f ∘ 1)
               (f' ∘ ((f0 f) _1 (x x4) ∘ x0 x4))
        ≈ ⟨f, f'⟩.
  Proof.
    helper_t idtac.
  Qed.

  /- Category of elements -/
  definition category : PreCategory.
  Proof.
    refine (@Build_PreCategory
              Pair
              (λs d, morphism s d)
              identity
              compose
              _
              _
              _
              _);
    [ abstract (
          intros ? ? ? ? [f ?] [g ?] [h ?];
          exact (pseudofunctor_to_cat_assoc_helper
                   (apD10
                      (ap components_of
                          (p_composition_of_coherent_for_rewrite F _ _ _ _ f g h))))
        )
    | abstract (
          intros ? ? [f ?];
          exact (pseudofunctor_to_cat_left_identity_helper
                   (apD10
                      (ap components_of
                          (p_left_identity_of_coherent_for_rewrite F _ _ f))))
        )
    | abstract (
          intros ? ? [f ?];
          exact (pseudofunctor_to_cat_right_identity_helper
                   (apD10
                      (ap components_of
                          (p_right_identity_of_coherent_for_rewrite F _ _ f))))
    ) ].
  end-/

  /- First projection functor -/
  definition dpr1 : Functor category C :=
       Build_Functor category C
                     c
                     (λs d, @dpr1 _ _)
                     (λ_ _ _ _ _, idpath)
                     (λ_, idpath).
End Grothendieck.
