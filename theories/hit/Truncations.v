/- -*- mode: coq; mode: visual-line -*- -/

/- Truncations of types, in all dimensions. -/

Require Import HoTT.Basics Types.Sigma ReflectiveSubuniverse Modality TruncType HProp.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables A X n.

/- Definition. -/

/- The definition of [Trunc n], the n-truncation of a type.

If Coq supported higher inductive types natively, we would construct this as somthing like:

   Inductive Trunc n (A : Type) : Type :=
   | tr : A → Trunc n A
   | istrunc_truncation : Π(f : Sphere n.+1 → Trunc n A)
       (x : Sphere n.+1), f x ≈ f North.

However, while we are faking our higher-inductives anyway, we can take some shortcuts, rather than translating the definition above.  Firstly, we directly posit a “constructor” giving truncatedness, rather than rephrasing it in terms of maps of spheres.  Secondly, we omit the “computation rule” for this constructor, since it is implied by truncatedness of the result type (and, for essentially that reason, is never wanted in practice anyway).
-/

Module Export Trunc.
Delimit Scope trunc_scope with trunc.

Private Inductive Trunc (n : trunc_index) (A :Type) : Type :=
  tr : A → Trunc n A.
Bind Scope trunc_scope with Trunc.
Arguments tr {n A} a.

/- Without explicit universe parameters, this instance is insufficiently polymorphic. -/
definition istrunc_truncation [instance] (n : trunc_index) (A : Type@{i})
: IsTrunc@{j} n (Trunc@{i} n A).
Admitted.

definition Trunc_ind {n A}
  (P : Trunc n A → Type) {Pt : Πaa, is_trunc n (P aa)}
  : (Πa, P (tr a)) → (Πaa, P aa) :=
   (λf aa, match aa with tr a => λ_, f a end Pt).

End Trunc.

/- The non-dependent version of the eliminator. -/

definition Trunc_rec {n A X} [H : is_trunc n X]
  : (A → X) → (Trunc n A → X) :=
   Trunc_ind (λ_, X).

/- [Trunc] is a modality -/

/- We will define a truncation modality to be parametrized by a [trunc_index].  However, as described in Modality.v, we don't want to simply define [Truncation_Modalities.Modality] to *be* [trunc_index]; we want to think of the truncation modality as being *derived from* rather than *identical to* its truncation index.  In particular, there is a coercion [O_reflector] from [Modality] to [Funclass], but we don't want Coq to print things like [2 X] to mean [Trunc 2 X].  However, in the special case of truncation, it is nevertheless convenient for [Truncation_Modalities.Modality] to be definitionally equal to [trunc_index], so that we can call modality functions (particularly connectedness functions) passing a truncation index directly.

These may seem like contradictory requirements, but it appears to be possible to satisfy them because coercions don't unfold definitions.  Thus, rather than a record wrapper, we define a *definitional* wrapper [Truncation_Modality] around [trunc_index], and a notation [Tr] for the identity.  We will define [Truncation_Modalities.Modality] to be [Truncation_Modality] and declare the identity as a coercion; thus a [Truncation_Modality] can be used as a modality and therefore also as a function (via the [O_reflector] coercion).  However, the identity from [trunc_index] to [Truncation_Modality] is not a coercion, so we don't get notation like [2 X]. -/
definition Truncation_Modality := trunc_index.
definition Tr : trunc_index → Truncation_Modality := idmap.

Module Truncation_Modalities <: Modalities.

  definition Modality : Type2@{u a} := Truncation_Modality.

  definition O_reflector (n : Modality@{u u'}) A := Trunc n A.

  definition inO_internal (n : Modality@{u u'}) A := is_trunc n A.

  definition O_inO_internal (n : Modality@{u u'}) A : inO_internal n (O_reflector n A).
  /-begin
    unfold inO_internal, O_reflector; exact _.
  end-/

  definition to (n : Modality@{u u'}) A := @tr n A.

  definition inO_equiv_inO_internal (n : Modality@{u u'})
             (A B : Type@{i}) Atr f feq :=
     @trunc_equiv A B f n Atr feq.

  definition hprop_inO_internal [H : Funext] (n : Modality@{u u'}) A
  : is_hprop (inO_internal n A).
  /-begin
    unfold inO_internal; exact _.
  end-/

  definition O_ind_internal (n : Modality@{u u'}) A B Btr f :=
       @Trunc_ind n A B Btr f.

  definition O_ind_beta_internal (n : Modality@{u u'})
             A B Btr f a
  : O_ind_internal n A B Btr f (to n A a) ≈ f a :=
       1.

  definition minO_paths (n : Modality@{u a})
             (A : Type@{i}) (Atr : inO_internal@{u a i} n A) (a a' : A)
  : inO_internal@{u a i} n (a ≈ a').
  /-begin
    unfold inO_internal in *; exact _.
  end-/

End Truncation_Modalities.

/- If you import the following module [TrM], then you can call all the modality functions with a [trunc_index] as the modality parameter, since we defined [Truncation_Modalities.Modality] to be [trunc_index]. -/
Module Import TrM := Modalities_Theory Truncation_Modalities.
/- If you don't import it, then you'll need to write [TrM.function_name] or [TrM.RSU.function_name] depending on whether [function_name] pertains only to modalities or also to reflective subuniverses.  (Having to know this is a bit unfortunate, but apparently the fact that [TrM] [Export]s reflective subuniverses still doesn't make the fields of the latter accessible as [TrM.field].) -/
Export TrM.Coercions.
Export TrM.RSU.Coercions.

/- Here is the additional coercion promised above. -/
Coercion Truncation_Modality_to_Modality := idmap : Truncation_Modality → Modality.

section TruncationModality
  Context (n : trunc_index).

  definition trunc_iff_isequiv_truncation (A : Type)
  : is_trunc n A <-> IsEquiv (@tr n A) :=
     inO_iff_isequiv_to_O n A.

  definition isequiv_tr [instance] A [H : is_trunc n A] : IsEquiv (@tr n A) :=
     fst (trunc_iff_isequiv_truncation A) _.

  definition equiv_tr (A : Type) [H : is_trunc n A]
  : A ≃ Tr n A :=
     BuildEquiv _ _ (@tr n A) _.

  definition untrunc_istrunc {A : Type} [H : is_trunc n A]
  : Tr n A → A :=
     (@tr n A)⁻¹.

  /- Functoriality -/

  definition Trunc_functor {X Y : Type} (f : X → Y)
  : Tr n X → Tr n Y :=
     O_functor n f.

  definition Trunc_functor_compose {X Y Z} (f : X → Y) (g : Y → Z)
  : Trunc_functor (g ∘ f) == Trunc_functor g ∘ Trunc_functor f :=
     O_functor_compose n f g.

  definition Trunc_functor_idmap (X : Type)
  : @Trunc_functor X X idmap == idmap :=
     O_functor_idmap n X.

  definition isequiv_Trunc_functor {X Y} (f : X → Y) [H : IsEquiv _ _ f]
  : IsEquiv (Trunc_functor f) :=
     isequiv_O_functor n f.

  definition equiv_Trunc_prod_cmp [H : Funext] {X Y}
  : Tr n (X × Y) ≃ Tr n X × Tr n Y :=
     equiv_O_prod_cmp n X Y.

End TruncationModality.

/- We have to teach Coq to translate back and forth between [IsTrunc n] and [In (Tr n)]. -/
definition inO_tr_istrunc [instance] {n : trunc_index} (A : Type) [H : is_trunc n A]
: In (Tr n) A.
/-begin
  assumption.
end-/

/- Having both of these as [Instance]s would cause infinite loops. -/
definition istrunc_inO_tr {n : trunc_index} (A : Type) [H : In (Tr n) A]
: is_trunc n A.
/-begin
  assumption.
end-/

/- Instead, we make the latter an immediate instance. -/
Hint Immediate istrunc_inO_tr : typeclass_instances.

/- Unfortunately, this isn't perfect; Coq still can't always find [In n] hypotheses in the context when it wants [IsTrunc]. -/


/- It's sometimes convenient to use "infinity" to refer to the identity modality in a similar way.  This clashes with some uses in higher topos theory, where "oo-truncated" means instead "hypercomplete", but this has not yet been a big problem. -/
Notation oo := purely.
/- Unfortunately, we can't import two or more copies of [Modalities_Theory] at the same time (the most recently imported shadows the other(s)).  If we ever want to talk about truncation and include [oo], we may want to define a "union" instance of [Modality]. -/

/- A few special things about the (-1)-truncation. -/

Local Open Scope trunc_scope.

/- We define [merely A] to be an inhabitant of the universe [hProp] of hprops, rather than a type.  We can always treat it as a type because there is a coercion, but this means that if we need an element of [hProp] then we don't need a separate name for it. -/

definition merely (A : Type@{i}) : hProp@{i} := BuildhProp (Trunc -1 A).

/- Note that we define [merely] using [Trunc -1] rather than [Tr -1].  These are of course judgmentally equal, but our choice introduces fewer universe parameters, resulting in faster compilation times.  The other choice might in theory give Coq an easier time applying general modality theorems to [merely], but currently things seem to be transparent enough that it doesn't matter. -/

definition hexists {X} (P : X → Type) : hProp := merely (sigT P).

definition hor (P Q : Type) : hProp := merely (P + Q).

definition contr_inhab_prop {A} [H : is_hprop A] (ma : merely A) : is_contr A.
/-begin
  refine (@contr_trunc_conn -1 A _ _); try assumption.
  refine (contr_inhabited_hprop _ ma).
end-/

/- Surjections are the (-1)-connected maps, but they can be characterized more simply since an inhabited hprop is automatically contractible. -/
Notation IsSurjection := (IsConnMap -1).

definition BuildIsSurjection {A B} (f : A → B) :
  (Πb, merely (hfiber f b)) → IsSurjection f.
/-begin
  intros H b; refine (contr_inhabited_hprop _ _).
  apply H.
end-/

definition isequiv_surj_emb {A B} (f : A → B)
           [H : IsSurjection f] [H : IsEmbedding f]
: IsEquiv f.
/-begin
  apply (@isequiv_conn_ino_map -1); assumption.
end-/


/- Tactic to remove truncations in hypotheses if possible. -/
Ltac strip_truncations :=
  /- search for truncated hypotheses -/
  progress repeat match goal with
                    | [ T : _ |- _ ]
                      => revert T;
                        refine (@Trunc_ind _ _ _ _ _);
                        /- ensure that we didn't generate more than one subgoal, i.e. that the goal was appropriately truncated -/
                        [];
                        intro T
                  end.
