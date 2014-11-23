/- -*- mode: coq; mode: visual-line -*-  -/
/- Nullification -/

Require Import HoTT.Basics HoTT.Types.
Require Import Extensions Modality.
Require Import hit.Localization.
Local Open Scope equiv_scope.
Local Open Scope path_scope.

/- Nullification is the special case of localization where the codomains of the generating maps are all [unit].  In this case, we get a modality and not just a reflective subuniverse. -/

/- The hypotheses of this lemma may look slightly odd (why are we bothering to talk about type families dependent over [unit]?), but they seem to be the most convenient to make the induction go through.  We define it as a [Fixpoint] rather than as a [Definition] with [induction], because the latter would introduce an undesired extra universe parameter (the size of the inductive motive, which must be strictly larger than the size of [C] and [D] since it is generalized over them). -/
Fixpoint extendable_over_unit (n : nat)
  (A : Type@{a}) (C : unit@{a} → Type@{i}) (D : Πu, C u → Type@{j})
  (ext : ExtendableAlong@{a a i i} n (@const A unit star) C)
  (ext' : Π(c : Πu, C u),
            ExtendableAlong@{a a j j} n (@const A unit star) (λu, (D u (c u))))
  {struct n}
: ExtendableAlong_Over@{a a i i j j i j j j} n (@const A unit star) C ext D.
/-begin
  destruct n as [|n]; [exact star | split].
  - intros g g'.
    exists ((fst (ext' (fst ext g).1)
                 (λa, ((fst ext g).2 a)⁻¹ ▹ (g' a))).1);
      intros a; simpl.
    apply moveR_transport_p.
    exact ((fst (ext' (fst ext g).1)
                (λa, ((fst ext g).2 a)⁻¹ ▹ (g' a))).2 a).
  - intros h k h' k'.
    apply extendable_over_unit; intros g.
    exact (snd (ext' k) (λu, g u ▹ h' u) k').
end-/

definition ooextendable_over_unit
  (A : Type@{a}) (C : unit@{a} → Type@{i}) (D : Πu, C u → Type@{j})
  (ext : ooExtendableAlong@{a a i i} (@const A unit star) C)
  (ext' : Π(c : Πu, C u),
            ooExtendableAlong@{a a j j} (@const A unit star) (λu, (D u (c u))))
: ooExtendableAlong_Over (@const A unit star) C ext D :=
     λn, extendable_over_unit n A C D (ext n) (λc, ext' c n).

/- We define a wrapper, as before. -/
Record Nullification_Modality := Nul { unNul : NullGenerators }.

Module Nullification_Modalities <: Modalities.

  definition Modality : Type@{u} := Nullification_Modality@{a}.

  /- We use the localization reflective subuniverses for most of the necessary data. -/
  Module LocRSU_Data <: ReflectiveSubuniverses_Restriction_Data Localization_ReflectiveSubuniverses.
    definition New_ReflectiveSubuniverse : let enforce := Type@{u'} : Type@{u} in Type@{u} :=
         Nullification_Modality@{u'}.
    definition ReflectiveSubuniverses_restriction
    : New_ReflectiveSubuniverse@{u a}
      → Localization_ReflectiveSubuniverses.ReflectiveSubuniverse@{u a} :=
         λO, Loc (null_to_local_generators (unNul O)).
  End LocRSU_Data.

  Module LocRSU := ReflectiveSubuniverses_Restriction Localization_ReflectiveSubuniverses LocRSU_Data.

  Module LocRSUTh := ReflectiveSubuniverses_Theory LocRSU.

  definition O_reflector := LocRSU.O_reflector.
  definition inO_internal := LocRSU.inO_internal.
  definition O_inO_internal := LocRSU.O_inO_internal.
  definition to := LocRSU.to.
  definition inO_equiv_inO_internal := LocRSU.inO_equiv_inO_internal.
  definition hprop_inO_internal := LocRSU.hprop_inO_internal.

  definition O_ind_internal (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} ∘ A → Type@{j})
             (B_inO : Πoa : O_reflector@{u a i} ∘ A, inO_internal@{u a j} ∘ (B oa))
             (g : Πa : A, B (to@{u a i} ∘ A a))
  : Πx, B x.
  /-begin
    refine (Localize_ind@{a i j i j i j j}
             (null_to_local_generators@{a a} (unNul O)) A B g _); intros i.
    apply (ooextendable_over_unit@{a i j}); intros c.
    refine (ooextendable_postcompose@{a a j j j j j j j j j}
              (λ(_:unit), B (c star)) _ _
              (λu, transport B (ap c (path_unit star u))) _).
    refine (ooextendable_islocal _ i).
    apply B_inO.
  end-/

  definition O_ind_beta_internal (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} ∘ A → Type@{j})
             (B_inO : Πoa : O_reflector ∘ A, inO_internal@{u a j} ∘ (B oa))
             (f : Πa : A, B (to ∘ A a)) (a : A)
  : O_ind_internal@{u a i j} ∘ A B B_inO f (to ∘ A a) ≈ f a :=
       1.

  definition minO_paths (O : Modality@{u a}) (A : Type@{i})
             (A_inO : inO_internal@{u a i} ∘ A) (z z' : A)
  : inO_internal@{u a i} ∘ (z ≈ z').
  /-begin
    apply (LocRSUTh.inO_paths@{u a i i}); assumption.
  end-/

End Nullification_Modalities.

/- If you import the following module [NulM], then you can call all the reflective subuniverse functions with a [NullGenerators] as the parameter. -/
Module Import NulM := Modalities_Theory Nullification_Modalities.
/- If you don't import it, then you'll need to write [NulM.function_name]. -/
Export NulM.Coercions.
Export NulM.RSU.Coercions.

Coercion Nullification_Modality_to_Modality := idmap
  : Nullification_Modality → Modality.

/- And here is the "real" definition of the notation [IsNull]. -/
Notation IsNull f := (In (Nul f)).

/- Nullification and Accessibility -/

/- Nullification modalities are accessible, essentially by definition. -/
Module Accessible_Nullification
  <: Accessible_Modalities Nullification_Modalities.

  Import Nullification_Modalities.

  definition acc_gen : Modality → NullGenerators :=
       unNul.

  definition inO_iff_isnull_internal (O : Modality@{u a}) (X : Type@{i})
  : iff@{i i i} (inO_internal@{u a i} ∘ X) (IsNull (acc_gen O) X) :=
       (idmap , idmap).

End Accessible_Nullification.


/- And accessible modalities can be nudged into nullifications. -/

Module Nudge_Modalities
       (Os : Modalities)
       (Acc : Accessible_Modalities Os).

  /- Application of modules is still "restricted to paths". -/
  Module Data <: Modalities_Restriction_Data Nullification_Modalities.
    definition New_Modality := Os.Modality.
    definition Modalities_restriction
    : New_Modality → Nullification_Modalities.Modality :=
         Nul ∘ Acc.acc_gen.
  End Data.
  
  Module Nudged <: Modalities :=
       Modalities_Restriction Nullification_Modalities Data.

End Nudge_Modalities.
