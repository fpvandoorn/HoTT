/- -*- mode: coq; mode: visual-line -*-  -/
/- Localization -/

Require Import HoTT.Basics HoTT.Types.
Require Import Extensions ReflectiveSubuniverse Modality EquivalenceVarieties.
Local Open Scope equiv_scope.
Local Open Scope path_scope.

/- Suppose given a family of maps [f : Π(i:I), S i → T i].  A type [X] is said to be [f]-local if for all [i:I], the map [(T i → X) → (S i → X)] given by precomposition with [f i] is an equivalence.  Our goal is to show that the [f]-local types form a reflective subuniverse, with a reflector constructed by localization.  That is, morally we want to say

<<
Inductive Localize f (X : Type) : Type :=
| loc : X → Localize X
| islocal_localize : Πi, IsEquiv (λ(g : T i → X), g ∘ f i).
>>

This is not a valid HIT by the usual rules, but if we expand out the definition of [IsEquiv] and apply [path_sigma] and [path_forall], then it becomes one.  We get a simpler definition (no 2-path constructors) if we do this with [BiInv] rather than [IsEquiv]:

<<
Inductive Localize f (X : Type) : Type :=
| loc : X → Localize X
| lsect : Πi (g : S i → X), T i → X
| lissect : Πi (g : S i → X) (s : S i), lsect i g (f i s) ≈ g s
| lretr : Πi (g : S i → X), T i → X
| lisretr : Πi (h : T i → X) (t : T i), lretr i (h ∘ f i) t ≈ h t.
>>

This definition works, and from it one can prove that the [f]-local types form a reflective subuniverse.  However, the proof inextricably involves [Funext].  We can avoid [Funext] in the same way that we did in the definition of a [ReflectiveSubuniverse], by using pointwise path-split precomposition equivalences.  Observe that the assertion [ExtendableAlong n f C] consists entirely of points, paths, and higher paths in [C].  Therefore, for any [n] we might choose, we can define [Localize f X] as a HIT to universally force [ExtendableAlong n (f i) (λ_, Localize f X)] to hold for all [i].  For instance, when [n] is 2 (the smallest value which will ensure that [Localize f X] is actually [f]-local), we get

<<
Inductive Localize f (X : Type) : Type :=
| loc : X → Localize X
| lrec : Πi (g : S i → X), T i → X
| lrec_beta : Πi (g : S i → X) (s : T i), lrec i g (f i s) ≈ g s
| lindpaths : Πi (h k : T i → X) (p : h ∘ f i == k ∘ f i) (t : T i), h t ≈ k t
| lindpaths_beta : Πi (h k : T i → X) (p : h ∘ f i == k ∘ f i) (s : S i),
                     lindpaths i h k p (f i s) ≈ p s.
>>

However, just as for [ReflectiveSubuniverse], in order to completely avoid [Funext] we need the [oo]-version of path-splitness.  Written out as above, this would involve infinitely many constructors (but it would not otherwise be problematic, so for instance it can be constructed semantically in model categories).  We can't actually write out infinitely many constructors in Coq, of course, but since we have a finite definition of [ooExtendableAlong], we can just assert directly that [ooExtendableAlong (f i) (λ_, Localize f X)] holds for all [i].

Then, however, we have to express the hypotheses of the induction principle.  We know what these should be for each path-constructor and higher path-constructor, so all we need is a way to package up those infinitely many hypotheses into a single one, analogously to [ooExtendableAlong].  Thus, we begin this file by defining a "dependent" version of [ooExtendableAlong], and of course we start this with a version for finite [n].  -/

/- Dependent extendability -/

Fixpoint ExtendableAlong_Over
         (n : nat) {A B : Type} (f : A → B) (C : B → Type)
         (ext : ExtendableAlong n f C) (D : Πb, C b → Type)
: Type :=
     match n return ExtendableAlong n f C → Type with
       | 0 => λ_, unit
       | S n => λext',
                (Π(g : Πa, C (f a)) (g' : Πa, D (f a) (g a)),
                  {rec : Πb, D b ((fst ext' g).1 b) &
                         Πa, (fst ext' g).2 a ▹ rec (f a) ≈ g' a }) *
                Π(h k : Πb, C b)
                       (h' : Πb, D b (h b)) (k' : Πb, D b (k b)),
                  ExtendableAlong_Over n f (λb, h b ≈ k b)
                    (snd ext' h k) (λb c, c ▹ h' b ≈ k' b)
     end ext.

/- Like [ExtendableAlong], these can be postcomposed with known equivalences. -/
definition extendable_over_postcompose' (n : nat)
           {A B : Type} (C : B → Type) (f : A → B)
           (ext : ExtendableAlong n f C)
           (D E : Πb, C b → Type)
           (g : Πb c, D b c ≃ E b c)
: ExtendableAlong_Over n f C ext D
  → ExtendableAlong_Over n f C ext E.
/-begin
  revert C ext D E g; simple_induction n n IHn; intros C ext D E g; simpl.
  1:by apply idmap.
  intros ext'.
  split.
  - intros h k.
    exists (λb, g b ((fst ext h).1 b)
                     ((fst ext' h (λa, (g _ _)⁻¹ (k a))).1 b)).
    intros a.
    refine ((ap_transport ((fst ext h).2 a) (g (f a)) _)⁻¹ ⬝ _).
    apply moveR_equiv_M.
    exact ((fst ext' h (λa, (g _ _)⁻¹ (k a))).2 a).
  - intros p q p' q'.
    refine (IHn (λb, p b ≈ q b) _
                (λb, λc, transport (D b) c ((g b (p b))⁻¹ (p' b))
                                   ≈ ((g b (q b))⁻¹ (q' b)))
                _ _
                (snd ext' p q (λb, (g b (p b))⁻¹ (p' b))
                              (λb, (g b (q b))⁻¹ (q' b)))).
    intros b c.
    refine (equiv_compose' _ (equiv_moveR_equiv_M _ _)).
    apply equiv_concat_l.
    refine (_ ⬝ (ap_transport c (g b) _)⁻¹).
    apply ap, symmetry, eisretr.
end-/

definition extendable_over_postcompose (n : nat)
           {A B : Type} (C : B → Type) (f : A → B)
           (ext : ExtendableAlong n f C)
           (D E : Πb, C b → Type)
           (g : Πb c, D b c → E b c)
           [H : Πb c, IsEquiv (g b c)]
: ExtendableAlong_Over n f C ext D
  → ExtendableAlong_Over n f C ext E :=
   extendable_over_postcompose' n C f ext D E
     (λb c, BuildEquiv _ _ (g b c) _).

/- And if the dependency is trivial, we obtain them from an ordinary [ExtendableAlong]. -/
definition extendable_over_const
           (n : nat) {A B : Type} (C : B → Type) (f : A → B)
           (ext : ExtendableAlong n f C) (D : B → Type)
: ExtendableAlong n f D
  → ExtendableAlong_Over n f C ext (λb _, D b).
/-begin
  revert C ext D.
  simple_induction n n IHn; intros C ext D ext'.
  1:exact star.
  split.
  - intros g g'.
    exists ((fst ext' g').1).
    exact (λa, transport_const ((fst ext g).2 a) _
                                    ⬝ (fst ext' g').2 a).
  - intros h k h' k'.
    refine (extendable_over_postcompose' _ _ _ _ _ _ _
              (IHn (λb, h b ≈ k b) (snd ext h k)
                   (λb, h' b ≈ k' b) (snd ext' h' k'))).
    exact (λb c, equiv_concat_l (transport_const c (h' b)) (k' b)).
end-/

/- This lemma will be used in stating the computation rule for localization. -/
Fixpoint apD_extendable_eq (n : nat) {A B : Type} (C : B → Type) (f : A → B)
         (ext : ExtendableAlong n f C) (D : Πb, C b → Type)
         (g : Πb c, D b c)
         (ext' : ExtendableAlong_Over n f C ext D)
         {struct n}
: Type.
/-begin
  destruct n.
  - exact unit.
  - apply prod.
    + exact (Π(h : Πa, C (f a)) (b : B),
               g b ((fst ext h).1 b) ≈ (fst ext' h (λa, g (f a) (h a))).1 b).
    + exact (Πh k, apD_extendable_eq
                           n A B (λb, h b ≈ k b) f (snd ext h k)
                           (λb c, c ▹ g b (h b) ≈ g b (k b))
                           (λb c, apD (g b) c)
                           (snd ext' h k _ _)).
end-/

/- Here's the [oo]-version. -/
definition ooExtendableAlong_Over
         {A B : Type} (f : A → B) (C : B → Type)
         (ext : ooExtendableAlong f C) (D : Πb, C b → Type) :=
     Πn, ExtendableAlong_Over n f C (ext n) D.

/- The [oo]-version for trivial dependency. -/
definition ooextendable_over_const
           {A B : Type} (C : B → Type) (f : A → B)
           (ext : ooExtendableAlong f C) (D : B → Type)
: ooExtendableAlong f D
  → ooExtendableAlong_Over f C ext (λb _, D b) :=
   λext' n, extendable_over_const n C f (ext n) D (ext' n).

/- A crucial fact: the [oo]-version is inherited by types of homotopies. -/
definition ooextendable_over_homotopy
           {A B : Type} (C : B → Type) (f : A → B)
           (ext : ooExtendableAlong f C)
           (D : Πb, C b → Type)
           (r s : Πb c, D b c)
: ooExtendableAlong_Over f C ext D
  → ooExtendableAlong_Over f C ext (λb c, r b c ≈ s b c).
/-begin
  intros ext' n.
  revert C ext D r s ext'.
  simple_induction n n IHn; intros C ext D r s ext'.
  1:exact star.
  split.
  - intros g g'.
    refine ⟨_,_⟩; simpl.
    + intros b.
      refine (_ ⬝ (fst (snd (ext' 2) _ _
                            (λb', r b' ((fst (ext n.+1) g).1 b'))
                            (λb', s b' ((fst (ext n.+1) g).1 b')))
                       (λ_, 1) _).1 b).
      × refine (transport2 (D b) (p := 1) _ _).
        refine ((fst (snd (snd (ext 3) _ _) (λb', 1)
                          ((fst (snd (ext 2) _ _) (λa : A, 1)).1)
                ) _).1 b); intros a.
        symmetry; refine ((fst (snd (ext 2) _ _) (λa', 1)).2 a).
      × intros a; simpl.
        refine (_ @
          ap (transport (D (f a)) ((fst (ext n.+1) g).2 a)⁻¹) (g' a)
          ⬝ _);
        [ symmetry; by apply apD
        | by apply apD ].
    + intros a; simpl.
      set (h := (fst (ext n.+1) g).1).
      match goal with
          |- context[   (fst (snd (ext' 2) _ _ ?k1 ?k2) (λ_, 1) ?l).1 ]
          => pose (p := (fst (snd (ext' 2) _ _  k1  k2) (λ_, 1) l).2 a);
            simpl in p
      end.
      rewrite transport_paths_Fl in p.
      apply moveL_Mp in p.
      refine (ap (transport _ _) (1 @@ p) ⬝ _); clear p.
      unfold transport2; rewrite concat_p_pp.
      match goal with
          |- transport ?P ?p ((ap ?f ?q ⬝ ap ?f ?r) ⬝ ?s) ≈ ?t
          => refine (ap (transport P p) ((ap_pp f q r)⁻¹ @@ (idpath s)) ⬝ _)
      end.
      pose (p := (fst (snd (snd (ext 3) h h) (λb' : B, 1)
                           ((fst (snd (ext 2) h h) (λa0 : A, 1)).1))
                      (λa' : A, ((fst (snd (ext 2) h h)
                                           (λa' : A, 1)).2 a')⁻¹)).2 a);
        simpl in p.
      refine (ap (transport _ _) (ap (ap _) (p @@ 1) @@ 1) ⬝ _); clear p.
      rewrite concat_Vp; simpl; rewrite concat_1p.
      refine (transport_paths_FlFr_D _ _ ⬝ _).
      Open Scope long_path_scope.
      rewrite !ap_pp, !concat_p_pp, ap_transport_pV, !concat_p_pp.
      refine ((((_  @@ 1) ⬝ concat_1p _) @@ 1 @@ 1 @@ 1) ⬝ _).
      × rewrite ap_V, concat_pp_p.
        do 2 apply moveR_Vp.
        rewrite concat_p1.
        symmetry; apply transport_pV_ap.
      × rewrite !concat_pp_p.
        refine ((1 @@ _) ⬝ (concat_p1 _)).
        apply moveR_Vp; rewrite concat_p1.
        apply transport_pV_ap.
      Close Scope long_path_scope.
  - intros h k h' k'.
    refine (extendable_over_postcompose' _ _ _ _ _ _
             (λb c, equiv_cancelL (apD (r b) c) _ _) _).
    refine (IHn _ _ _ _ _
                (λn, snd (ext' n.+1) h k
                              (λb, r b (h b)) (λb, s b (k b)))).
Qed.

/- Local types -/

Import IsLocal_Internal.

definition islocal_equiv_islocal (f : LocalGenerators@{a})
           (X : Type@{i}) {Y : Type@{i}}
           (Xloc : IsLocal@{i i a} f X)
           (g : X → Y) [H : IsEquiv@{i j] _ _ g}
: IsLocal@{j j a} f Y :=
     λi, ooextendable_postcompose _ _ (f i) (λ_, g) (Xloc i).


/- Localization as a HIT -/

Module Export LocalizationHIT.

  Private Inductive Localize (f : LocalGenerators) (X : Type) : Type :=
  | loc : X → Localize f X.

  Arguments loc {f X} x.

  /- TODO: Force [Localize f X] to have size influenced by [f] in addition to [X]. -/

  section Localization

    Context (f : LocalGenerators) (X : Type).

    /- Note that the following axiom actually contains a point-constructor.  We could separate out that point-constructor and make it an actual argument of the private inductive type, thereby getting a judgmental computation rule for it.  However, since locality is an hprop, there seems little point to this. -/
    Axiom islocal_localize : IsLocal@{i i u} f (Localize f X).

    section LocalizeInd

      Context (P : Localize f X → Type)
      (loc' : Πx, P (loc x))
      (islocal' : Πi, ooExtendableAlong_Over
                              (f i) (λ_, Localize f X)
                              (islocal_localize i) (λ_, P)).

      Fixpoint Localize_ind (z : Localize f X) {struct z}
      : P z :=
           match z with
             | loc x => λ_, loc' x
           end islocal'.

      /- We now state the computation rule for [islocal_localize].  Since locality is an hprop, we never actually have any use for it, but the fact that we can state it is a reassuring check that we have defined a meaningful HIT. -/
      Axiom Localize_ind_islocal_localize_beta :
        Πi n, apD_extendable_eq n (λ_, Localize f X) (f i)
                                      (islocal_localize i n) (λ_, P)
                                      (λ_, Localize_ind)
                                      (islocal' i n).

    End LocalizeInd.
  End Localization.
End LocalizationHIT.

/- Now we prove that localization is a reflective subuniverse. -/

section Localization

  Context (f : LocalGenerators).

  /- The induction principle is an equivalence. -/
  definition ext_localize_ind (X : Type)
      (P : Localize f X → Type)
      (Ploc : Πi, ooExtendableAlong_Over
                          (f i) (λ_, Localize f X)
                          (islocal_localize f X i) (λ_, P))
  : ooExtendableAlong loc P.
  Proof.
    intros n; generalize dependent P.
    simple_induction n n IHn; intros P Ploc.
    1:exact star.
    split.
    - intros g.
      exists (Localize_ind f X P g Ploc).
      intros x; reflexivity.
    - intros h k; apply IHn; intros i m.
      apply ooextendable_over_homotopy.
      exact (Ploc i).
  end-/

End Localization.

/- We define a wrapper around [LocalGenerators].  See the comments in hit/Truncations for an explanation.  Unlike there, here we make the wrapper a [Record] rather than a [Definition], so that a projection has to be inserted to convert one to the other.  This forces us to write [Loc f] as a parameter to all reflective-subuniverse functions, which is really entirely reasonable; we only allowed ourselves to write [n] rather than [Tr n] in the case of truncations because things like connectedness are traditionally defined only for the truncation modality, so users may prefer not to have to think about the fact that there is a modality present. -/
Record Localization_ReflectiveSubuniverse := Loc { unLoc : LocalGenerators }.

Module Localization_ReflectiveSubuniverses <: ReflectiveSubuniverses.

  /- Here we have to use the extra universe parameter that we built into the definition of [ReflectiveSubuniverse]: a set of localization generators is parametrized by the universe that it lives in, but also by the universe that the *generators* live in, which must be smaller. -/
  definition ReflectiveSubuniverse : Type@{u} := Localization_ReflectiveSubuniverse@{a}.
  Check ReflectiveSubuniverse@{u a}.

  definition O_reflector : ReflectiveSubuniverse@{u a} → Type@{i} → Type@{i} :=
       λO, Localize@{a i} (unLoc O).

  definition inO_internal : ReflectiveSubuniverse@{u a} → Type@{i} → Type@{i} :=
       λO X, IsLocal@{i i a} (unLoc O) X.

  definition O_inO_internal :
    Π(O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
      inO_internal ∘ (O_reflector ∘ T) :=
       λO, islocal_localize@{a i i} (unLoc O).

  definition to :
    Π(O : ReflectiveSubuniverse@{u a}) (T : Type@{i}), T → O_reflector ∘ T :=
       λO, @loc@{a i} (unLoc O).

  definition inO_equiv_inO_internal :
    Π(O : ReflectiveSubuniverse@{u a}) (T U : Type@{i}),
      inO_internal@{u a i} ∘ T → Πf : T → U, IsEquiv f → inO_internal@{u a i} ∘ U :=
       λO, islocal_equiv_islocal@{a i i} (unLoc O).

  definition hprop_inO_internal [H : Funext]
             (O : ReflectiveSubuniverse@{u a}) (T : Type@{i})
  : is_hprop (inO_internal@{u a i} ∘ T).
  /-begin
    apply (@trunc_forall@{a i i} _); intros i.
    apply ishprop_ooextendable@{a a i i i i i}.
  end-/

  definition extendable_to_O_internal
             (O : ReflectiveSubuniverse@{u a}) {P : Type@{i}}
             {Q : Type@{j}} {Q_inO : inO_internal@{u a j} ∘ Q}
  : ooExtendableAlong@{i i j j} (to ∘ P) (λ_, Q).
  /-begin
    apply ext_localize_ind@{a i j j i j j j j}; intros ?.
    apply ooextendable_over_const.
    apply Q_inO.
  end-/

End Localization_ReflectiveSubuniverses.


/- If you import the following module [LocM], then you can call all the reflective subuniverse functions with a [LocalGenerators] as the parameter. -/
Module Import LocM := ReflectiveSubuniverses_Theory Localization_ReflectiveSubuniverses.
/- If you don't import it, then you'll need to write [LocM.function_name]. -/
Export LocM.Coercions.

Coercion Localization_ReflectiveSubuniverse_to_ReflectiveSubuniverse := idmap
  : Localization_ReflectiveSubuniverse → ReflectiveSubuniverse.

/- Here is the "real" definition of the notation [IsLocal].  Defining it this way allows it to inherit typeclass inference from [In], unlike (for instance) the slightly annoying case of [IsTrunc n] versus [In (Tr n)]. -/
Notation IsLocal f := (In (Loc f)).

section LocalTypes
  Context (f : LocalGenerators).

  definition ooextendable_islocal {X : Type} {Xloc : IsLocal f X} i
  : ooExtendableAlong (f i) (λ_, X) :=
     Xloc i.

  definition islocal_loc [instance] (X : Type) : IsLocal f (Localize f X) :=
       islocal_localize f X.

  definition isequiv_precomp_islocal [instance] [H : Funext]
         {X : Type} [H : IsLocal f X] i
  : IsEquiv (λg, g ∘ f i) :=
     isequiv_ooextendable (λ_, X) (f i) (ooextendable_islocal i).

  /- The non-dependent eliminator -/
  definition Localize_rec {X Z : Type} [H : IsLocal f Z] (g : X → Z)
  : Localize f X → Z.
  /-begin
    refine (Localize_ind f X (λ_, Z) g _); intros i.
    apply ooextendable_over_const.
    apply ooextendable_islocal.
  end-/

  definition local_rec {X} [H : IsLocal f X] {i} (g : lgen_domain f i → X)
  : lgen_codomain f i → X :=
     (fst (ooextendable_islocal i 1%nat) g).1.

  definition local_rec_beta {X} [H : IsLocal f X] {i} (g : lgen_domain f i → X) s
  : local_rec g (f i s) ≈ g s :=
       (fst (ooextendable_islocal i 1%nat) g).2 s.

  definition local_indpaths {X} [H : IsLocal f X] {i} {h k : lgen_codomain f i → X}
             (p : h ∘ f i == k ∘ f i)
  : h == k :=
       (fst (snd (ooextendable_islocal i 2) h k) p).1.

  definition local_indpaths_beta {X} [H : IsLocal f X] {i} (h k : lgen_codomain f i → X)
             (p : h ∘ f i == k ∘ f i) s
  : local_indpaths p (f i s) ≈ p s :=
       (fst (snd (ooextendable_islocal i 2) h k) p).2 s.

End LocalTypes.

Arguments local_rec : simpl never.
Arguments local_rec_beta : simpl never.
Arguments local_indpaths : simpl never.
Arguments local_indpaths_beta : simpl never.

/- Localization and accessibility -/

/- Localization subuniverses are accessible, essentially by definition. -/
Module Accessible_Localization
  <: Accessible_ReflectiveSubuniverses Localization_ReflectiveSubuniverses.

  Import Localization_ReflectiveSubuniverses.

  definition acc_gen : ReflectiveSubuniverse → LocalGenerators :=
       unLoc.

  definition inO_iff_islocal_internal
             (O : ReflectiveSubuniverse@{u a}) (X : Type@{i})
  : iff@{i i i} (inO_internal ∘ X) (IsLocal (acc_gen O) X) :=
       (idmap , idmap).

End Accessible_Localization.

/- Conversely, if a reflective subuniverse is accessible, then it can be "nudged" to an equivalent localization.  The nudged version has the advantages of satisfying its computation rules judgmentally. -/

Module Nudge_ReflectiveSubuniverses
       (Os : ReflectiveSubuniverses)
       (Acc : Accessible_ReflectiveSubuniverses Os).

  /- Once again, we are annoyed that "application of modules is restricted to paths". -/
  Module Data <: ReflectiveSubuniverses_Restriction_Data
                   Localization_ReflectiveSubuniverses.
    definition New_ReflectiveSubuniverse := Os.ReflectiveSubuniverse.
    definition ReflectiveSubuniverses_restriction
    : New_ReflectiveSubuniverse → Localization_ReflectiveSubuniverses.ReflectiveSubuniverse :=
         λO, Loc (Acc.acc_gen O).
  End Data.
  
  Module Nudged <: ReflectiveSubuniverses :=
       ReflectiveSubuniverses_Restriction Localization_ReflectiveSubuniverses Data.

End Nudge_ReflectiveSubuniverses.
