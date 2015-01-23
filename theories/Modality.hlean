/- -*- mode: coq; mode: visual-line -*- -/
Require Import HoTT.Basics HoTT.Types.
Require Import Fibrations EquivalenceVarieties Extensions Factorization NullHomotopy.
Require Export ReflectiveSubuniverse. /- [Export] because many of the lemmas and facts about reflective subuniverses are equally important for modalities. -/
Require Import HoTT.Tactics.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

/- Modalities -/

Module Type Modalities.

  Parameter Modality : Type2@{u a}.

  /- These are the same as for a reflective subuniverse. -/

  Parameter O_reflector : Π(O : Modality@{u a}),
                            Type2le@{i a} → Type2le@{i a}.
  Check O_reflector@{u a i}.    /- Verify that we have the right number of universes -/

  Parameter inO_internal : Π(O : Modality@{u a}),
                            Type2le@{i a} → Type2le@{i a}.
  Check inO_internal@{u a i}.

  Parameter O_inO_internal : Π(O : Modality@{u a}) (T : Type@{i}),
                               inO_internal@{u a i} ∘ (O_reflector@{u a i} ∘ T).
  Check O_inO_internal@{u a i}.

  Parameter to : Π(O : Modality@{u a}) (T : Type@{i}),
                   T → O_reflector@{u a i} ∘ T.
  Check to@{u a i}.

  Parameter inO_equiv_inO_internal :
      Π(O : Modality@{u a}) (T U : Type@{i})
             (T_inO : inO_internal@{u a i} ∘ T) (f : T → U) (feq : is_equiv f),
        inO_internal@{u a i} ∘ U.
  Check inO_equiv_inO_internal@{u a i}.

  Parameter hprop_inO_internal
  : funext → Π(O : Modality@{u a}) (T : Type@{i}),
                is_hprop (inO_internal@{u a i} ∘ T).
  Check hprop_inO_internal@{u a i}.

  /- Now instead of [extendable_to_O], we have an ordinary induction principle. -/

  Parameter O_ind_internal
  : Π(O : Modality@{u a})
           (A : Type2le@{i a}) (B : O_reflector ∘ A → Type2le@{j a})
           (B_inO : Πoa, inO_internal@{u a j} ∘ (B oa)),
      (Πa, B (to ∘ A a)) → Πa, B a.
  Check O_ind_internal@{u a i j}.

  Parameter O_ind_beta_internal
  : Π(O : Modality@{u a})
           (A : Type@{i}) (B : O_reflector ∘ A → Type@{j})
           (B_inO : Πoa, inO_internal@{u a j} ∘ (B oa))
           (f : Πa : A, B (to ∘ A a)) (a:A),
      O_ind_internal@{u a i j} ∘ A B B_inO f (to ∘ A a) = f a.
  Check O_ind_beta_internal@{u a i j}.

  Parameter minO_paths
  : Π(O : Modality@{u a})
           (A : Type2le@{i a}) (A_inO : inO_internal@{u a i} ∘ A) (z z' : A),
      inO_internal@{u a i} ∘ (z = z').
  Check minO_paths@{u a i}.

End Modalities.

/- Modalities are reflective subuniverses -/

/- We show that modalities have underlying reflective subuniverses.  It is important in some applications, such as [Trunc], that this construction uses the general [O_ind] given as part of the modality data.  For instance, this ensures that [O_functor] reduces to simply an application of [O_ind].

  Note also that our choice of how to define reflective subuniverses differently from the book, using [ooExtendableAlong] enables us to prove this without using funext. -/

Module Modalities_to_ReflectiveSubuniverses
       (Os : Modalities) <: ReflectiveSubuniverses.

  Import Os.

  Fixpoint O_extendable (O : Modality@{u a})
           (A : Type@{i}) (B : O_reflector ∘ A → Type@{j})
           (B_inO : Πa, inO_internal@{u a j} ∘ (B a)) (n : nat)
  : ExtendableAlong@{i i j k} n (to ∘ A) B.
  /-begin
    destruct n as [|n].
    - exact star.
    - split.
      + intros g.
        exists (O_ind_internal@{u a i j} ∘ A B B_inO g); intros x.
        apply O_ind_beta_internal.
      + intros h k.
        apply O_extendable; intros x.
        apply minO_paths; trivial.
  end-/

  definition ReflectiveSubuniverse := Modality.

  definition O_reflector := O_reflector.
  /- Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3807 -/
  definition inO_internal := inO_internal@{u a i}.
  definition O_inO_internal := O_inO_internal@{u a i}.
  definition to := to.
  definition inO_equiv_inO_internal := inO_equiv_inO_internal@{u a i}.
  definition hprop_inO_internal := hprop_inO_internal@{u a i}.

  /- Corollary 7.7.8, part 1 -/
  definition extendable_to_O_internal (O : ReflectiveSubuniverse@{u a})
    {P : Type@{i}} {Q : Type@{j}} {Q_inO : inO_internal@{u a j} ∘ Q}
  : ooExtendableAlong@{i i j k} (to ∘ P) (λ_, Q) :=
       λn, O_extendable ∘ P (λ_, Q) (λ_, Q_inO) n.

End Modalities_to_ReflectiveSubuniverses.


/- Conversely, if a reflective subuniverse is closed under sigmas, it is a modality.  This is a bit annoying to state using modules, and in fact with our current definitions there doesn't seem to be a way to actually convince Coq to accept it.  However, this is not really a problem in practice: in most or all examples, constructing [O_ind] directly is just as easy, and preferable because it sometimes gives a judgmental computation rule.  However, for the sake of completeness, we include here the code that almost works. -/

Module Type SigmaClosed (Os : ReflectiveSubuniverses).

  Import Os.

  Parameter inO_sigma
  : Π(O : ReflectiveSubuniverse@{u a})
           (A:Type@{i}) (B:A → Type@{j})
           (A_inO : inO_internal@{u a i} ∘ A)
           (B_inO : Πa, inO_internal@{u a j} ∘ (B a)),
      inO_internal@{u a k} ∘ Σx:A, B x.
  Check inO_sigma@{u a i j k}.    /- Verify that we have the right number of universes -/

End SigmaClosed.

/- We omit the module type, because Coq won't actually accept it (see below for why). -/
Module ReflectiveSubuniverses_to_Modalities
       (Os : ReflectiveSubuniverses) (OsSigma : SigmaClosed Os).
/- <: Modalities. -/

  Import Os OsSigma.
  Module Import Os_Theory := ReflectiveSubuniverses_Theory Os.

  definition Modality := ReflectiveSubuniverse.

  definition O_reflector := O_reflector.
  /- Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3807 -/
  definition inO_internal := inO_internal@{u a i}.
  definition O_inO_internal := O_inO_internal@{u a i}.
  definition to := to.
  definition inO_equiv_inO_internal := inO_equiv_inO_internal@{u a i}.
  definition hprop_inO_internal := hprop_inO_internal@{u a i}.

  /- The reason Coq won't actually accept this as a module of type [Modalities] is that the following definitions of [O_ind_internal] and [O_ind_beta_internal] have an extra universe parameter [k] that's at least as large as both [i] and [j].  This is because [extendable_to_O_internal] has such a parameter, which in turn is because [ooExtendableAlong] does.  Unfortunately, we can't directly instantiate [k] to [max(i,j)] because Coq doesn't allow "algebraic universes" in arbitrary position.  We could probably work around it by defining [ExtendableAlong] inductively rather than recursively, but given the non-usefulness of this construction in practice, that doesn't seem to be worth the trouble at the moment. -/
  definition O_ind_internal (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} ∘ A → Type@{j})
             (B_inO : Πoa, inO_internal@{u a j} ∘ (B oa))
  : (Πa, B (to ∘ A a)) → Πa, B a :=
     λg, dpr1 ((O_ind_from_inO_sigma@{u a i j k k j} ∘ (inO_sigma O))
                     A B B_inO g).

  definition O_ind_beta_internal (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} ∘ A → Type@{j})
             (B_inO : Πoa, inO_internal@{u a j} ∘ (B oa))
             (f : Πa : A, B (to ∘ A a)) (a:A)
  : O_ind_internal ∘ A B B_inO f (to ∘ A a) = f a :=
     dpr2 ((O_ind_from_inO_sigma@{u a i j k k j} ∘ (inO_sigma O))
                     A B B_inO f) a.

  definition minO_paths (O : Modality@{u a})
             (A : Type@{i}) (A_inO : inO_internal@{u a i} ∘ A) (z z' : A)
  : inO_internal ∘ (z = z') :=
     @inO_paths@{u a i i} ∘ A A_inO z z'.

End ReflectiveSubuniverses_to_Modalities.


/- Easy modalities -/

/- Our definition of modality is slightly different from the one in the book, which requires an induction principle only into families of the form [λoa, ∘ (B oa)], and similarly only that path-spaces of types [O A] are modal, where "modal" means that the unit is an equivalence.  This is equivalent, roughly since every modal type [A] (in this sense) is equivalent to [O A].

However, our definition is more convenient in formalized applications because in some examples (such as [Trunc] and closed modalities), there is a naturally occurring [O_ind] into all modal types that is not judgmentally equal to the one that can be constructed by passing through [O] and back again.  Thus, when we apply general theorems about modalities to a particular modality such as [Trunc], the proofs will reduce definitionally to "the way we would have proved them directly" if we didn't know about general modalities.

On the other hand, in other examples (such as [~~] and open modalities) it is easier to construct the latter weaker induction principle.  Thus, we now show how to get from that to our definition of modality. -/

Module Type EasyModalities.

  Parameter Modality : Type2@{u a}.
  Check Modality@{u a}.    /- Verify that we have the right number of universes -/

  Parameter O_reflector : Π(O : Modality@{u a}),
                            Type2le@{i a} → Type2le@{i a}.
  Check O_reflector@{u a i}.

  Parameter to : Π(O : Modality@{u a}) (T : Type@{i}),
                   T → O_reflector@{u a i} ∘ T.
  Check to@{u a i}.

  Parameter O_indO
  : Π(O : Modality@{u a}) (A : Type@{i})
           (B : O_reflector@{u a i} ∘ A → Type@{j}),
      (Πa, O_reflector@{u a j} ∘ (B (to ∘ A a)))
      → Πz, O_reflector@{u a j} ∘ (B z).
  Check O_indO@{u a i j}.

  Parameter O_indO_beta
  : Π(O : Modality@{u a}) (A : Type@{i})
           (B : O_reflector@{u a i} ∘ A → Type@{j})
           (f : Πa, O_reflector@{u a j} ∘ (B (to ∘ A a))) a,
      O_indO ∘ A B f (to ∘ A a) = f a.
  Check O_indO_beta@{u a i j}.

  Parameter minO_pathsO
  : Π(O : Modality@{u a}) (A : Type@{i})
           (z z' : O_reflector@{u a i} ∘ A),
      is_equiv (to@{u a i} ∘ (z = z')).
  Check minO_pathsO@{u a i}.

End EasyModalities.

Module EasyModalities_to_Modalities (Os : EasyModalities)
<: Modalities.

  Import Os.

  definition Modality := Modality.
  /- Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3807 -/
  definition O_reflector := O_reflector@{u a i}.
  definition to := to@{u a i}.

  definition inO_internal
  : Π(O : Modality@{u a}), Type@{i} → Type@{i} :=
     λO A, is_equiv@{i i} (to ∘ A).

  definition hprop_inO_internal [H : funext] (O : Modality@{u a})
             (T : Type@{i})
  : is_hprop (inO_internal@{u a i} ∘ T).
  /-begin
    unfold inO_internal.
    exact (hprop_isequiv (to ∘ T)).
  end-/

  definition O_ind_internal (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} ∘ A → Type@{j})
             (B_inO : Πoa, inO_internal@{u a j} ∘ (B oa))
             (f : Πa, B (to@{u a i} ∘ A a)) (oa : O_reflector@{u a i} ∘ A)
  : B oa.
  /-begin
    pose (H := B_inO oa); unfold inO_internal in H.
    apply ((to ∘ (B oa))⁻¹).
    apply O_indO.
    intros a; apply to, f.
  end-/

  definition O_ind_beta_internal (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} ∘ A → Type@{j})
             (B_inO : Πoa, inO_internal@{u a j} ∘ (B oa))
             (f : Πa : A, B (to ∘ A a)) (a:A)
  : O_ind_internal ∘ A B B_inO f (to ∘ A a) = f a.
  /-begin
    unfold O_ind_internal.
    apply moveR_equiv_V.
    apply @O_indO_beta with (f := λx, to ∘ _ (f x)).
  Qed.

  definition O_inO_internal (O : Modality@{u a}) (A : Type@{i})
  : inO_internal@{u a i} ∘ (O_reflector@{u a i} ∘ A).
  Proof.
    refine (isequiv_adjointify (to ∘ (O_reflector ∘ A))
             (O_indO ∘ (O_reflector ∘ A) (λ_, A) idmap) _ _).
    - intros x; pattern x; apply O_ind_internal.
      + intros oa; apply minO_pathsO.
      + intros a; apply ap.
        exact (O_indO_beta ∘ (O_reflector ∘ A) (λ_, A) idmap a).
    - intros a.
      exact (O_indO_beta ∘ (O_reflector ∘ A) (λ_, A) idmap a).
  end-/

  /- It seems to be surprisingly hard to show repleteness (without univalence).  We basically have to manually develop enough functoriality of [O] and naturality of [to O]. -/
  definition inO_equiv_inO_internal (O : Modality@{u a}) (A B : Type@{i})
    (A_inO : inO_internal@{u a i} ∘ A) (f : A → B) (feq : is_equiv f)
  : inO_internal@{u a i} ∘ B.
  /-begin
    refine (isequiv_commsq (to ∘ A) (to ∘ B) f
             (O_ind_internal ∘ A (λ_, O_reflector ∘ B) _ (λa, to ∘ B (f a))) _).
    - intros; apply O_inO_internal.
    - intros a; refine (O_ind_beta_internal ∘ A (λ_, O_reflector ∘ B) _ _ a).
    - apply A_inO.
    - refine (isequiv_adjointify _
               (O_ind_internal ∘ B (λ_, O_reflector ∘ A) _ (λb, to ∘ A (f⁻¹ b))) _ _);
        intros x.
      + apply O_inO_internal.
      + pattern x; refine (O_ind_internal ∘ B _ _ _ x); intros.
        × apply minO_pathsO.
        × unfold compose; simpl;
            abstract (repeat rewrite O_ind_beta_internal; apply ap, retr).
      + pattern x; refine (O_ind_internal ∘ A _ _ _ x); intros.
        × apply minO_pathsO.
        × unfold compose; simpl;
            abstract (repeat rewrite O_ind_beta_internal; apply ap, sect).
  end-/

  definition minO_paths (O : Modality@{u a})
             (A : Type@{i}) (A_inO : inO_internal@{u a i} ∘ A) (a a' : A)
  : inO_internal ∘ (a = a').
  /-begin
    refine (inO_equiv_inO_internal ∘ (to ∘ A a = to ∘ A a') _ _
                          (@ap _ _ (to ∘ A) a a')⁻¹ _).
    - apply minO_pathsO.
    - refine (@isequiv_ap _ _ _ A_inO _ _).
    - apply isequiv_inverse.
  end-/

End EasyModalities_to_Modalities.

/- We now move on to the general theory of modalities. -/

Module Modalities_Theory (Os : Modalities).

Export Os.
Module Export Os_ReflectiveSubuniverses :=
     Modalities_to_ReflectiveSubuniverses Os.
Module Export RSU :=
     ReflectiveSubuniverses_Theory Os_ReflectiveSubuniverses.

/- As with reflective subuniverses, we put this in a module so it can be exported separately (and it should be). -/
Module Export Coercions.
  Coercion modality_to_reflective_subuniverse :=
       idmap : Modality → ReflectiveSubuniverse.
End Coercions.

definition O_ind {O : Modality@{u a}}
           {A : Type@{i}} (B : ∘ A → Type@{j})
           {B_inO : Πoa, In ∘ (B oa)}
           (f : Πa, B (to ∘ A a)) (oa : ∘ A)
: B oa :=
   O_ind_internal ∘ A B B_inO f oa.

definition O_ind_beta {O : Modality@{u a}}
           {A : Type@{i}} (B : ∘ A → Type@{j})
           {B_inO : Πoa, In ∘ (B oa)}
           (f : Πa : A, B (to ∘ A a)) (a : A)
: @O_ind ∘ A B B_inO f (to ∘ A a) = f a :=
   O_ind_beta_internal ∘ A B B_inO f a.

/- Corollary 7.7.8, part 2 -/
definition inO_sigma [instance] {O : Modality} (A:Type) (B:A → Type)
       [H : In ∘ A] [H : Πa, In ∘ (B a)]
: In ∘ Σx:A, B x.
/-begin
  generalize dependent A.
  refine (inO_sigma_from_O_ind _ _).
  intros A B ? g.
  exists (O_ind B g).
  apply O_ind_beta.
end-/

/- definition 7.3.9: The reflector [O] can be discarded inside a reflected sum. -/
definition equiv_O_sigma_O {O : Modality} {A} (P : A → Type)
: ∘ Σx:A, ∘ (P x) ≃ ∘ Σx:A, P x.
/-begin
  refine (equiv_adjointify _ _ _ _).
  - apply O_rec; intros [a op]; revert op.
    apply O_rec; intros p.
    exact (to ∘ _ ⟨a,p⟩).
  - apply O_rec; intros [a p].
    exact (to ∘ _ ⟨a , to ∘ _ p⟩).
  - unfold Sect; apply O_ind; try exact _.
    intros [a p]; simpl.
    abstract (repeat (simpl rewrite @O_rec_beta); reflexivity).
  - unfold Sect; apply O_ind; try exact _.
    intros [a op]; revert op; apply O_ind; try exact _; intros p; simpl.
    abstract (repeat (simpl rewrite @O_rec_beta); reflexivity).
end-/

/- Corollary 7.3.10 -/
Corollary equiv_sigma_inO_O {O : Modality} {A} [H : In ∘ A] (P : A → Type)
: Σx:A, ∘ (P x) ≃ ∘ Σx:A, P x.
/-begin
  transitivity (O Σx:A, ∘ (P x)).
  - apply equiv_to_O; exact _.
  - apply equiv_O_sigma_O.
end-/

/- The induction principle [O_ind], like most induction principles, is an equivalence. -/
section OIndEquiv
  Context {fs : funext} (O : Modality).

  section OIndEquivData

    Context {A : Type} (B : ∘ A → Type) [H : Πa, In ∘ (B a)].

    definition isequiv_O_ind [instance] : is_equiv (O_ind B).
    /-begin
      apply isequiv_adjointify with (g := λh, h oD to ∘ A).
      - intros h. apply path_forall.
        refine (O_ind (λoa, O_ind B (h oD to ∘ A) oa = h oa) _).
        exact (O_ind_beta B (h oD to ∘ A)).
      - intros f. apply path_forall.
        exact (O_ind_beta B f).
    end-/

    definition equiv_O_ind
    : (Πa, B (to ∘ A a)) ≃ (Πoa, B oa) :=
       equiv.mk _ _ (O_ind B) _.

    /- definition 7.7.7 -/
    definition isequiv_oD_to_O
    : is_equiv (λ(h : Πoa, B oa), h oD to ∘ A) :=
       equiv_isequiv (equiv_inverse equiv_O_ind).

  End OIndEquivData.

  Local definition isequiv_o_to_O (A B : Type) (B_inO : In ∘ B)
  : is_equiv (λ(h : ∘ A → B), h ∘ to ∘ A) :=
       isequiv_oD_to_O (λ_, B).

End OIndEquiv.

/- Modally connected types -/

/- Connectedness of a type, relative to a modality, can be defined in two equivalent ways: quantifying over all maps into modal types, or by considering just the universal case, the modal reflection of the type itself.  The former requires only core Coq, but blows up the size (universe level) of [IsConnected], since it quantifies over types; moreover, it is not even quite correct since (at least with a polymorphic modality) it should really be quantified over all universes.  Thus, we use the latter, although in most examples it requires HITs to define the modal reflection.

Question: is there a definition of connectedness (say, for n-types) that neither blows up the universe level, nor requires HIT's? -/

Class IsConnected (O : Modality) (A : Type) :=
     isconnected_contr_O : is_contr (O A).

Global Existing Instance isconnected_contr_O.

section ConnectedTypes
  Context (O : Modality).

  /- Being connected is an hprop -/
  definition ishprop_isconnected [instance] [H : funext] A
  : is_hprop (IsConnected ∘ A).
  /-begin
    unfold IsConnected; exact _.
  end-/

  /- Anything equivalent to a connected type is connected. -/
  definition isconnected_equiv (A : Type) {B : Type} (f : A → B) [H : is_equiv _ _ f]
  : IsConnected ∘ A → IsConnected ∘ B.
  /-begin
    intros ?; refine (contr_equiv (O A) (O_functor ∘ f)).
  end-/

  definition isconnected_equiv' (A : Type) {B : Type} (f : A ≃ B)
  : IsConnected ∘ A → IsConnected ∘ B :=
       isconnected_equiv A f.

  /- Connectedness of a type [A] can equivalently be characterized by the fact that any map to an [O]-type [C] is nullhomotopic.  Here is one direction of that equivalence. -/
  definition isconnected_elim {A : Type} [H : IsConnected ∘ A] (C : Type) [H : In ∘ C] (f : A → C)
  : NullHomotopy f.
  /-begin
    set (ff := @O_rec ∘ _ _ _ f).
    exists (ff (center _)).
    intros a. apply symmetry.
    refine (ap ff (contr (to ∘ _ a)) ⬝ _).
    apply O_rec_beta.
  end-/

  /- For the other direction of the equivalence, it's sufficient to consider the case when [C] is [O A]. -/
  definition isconnected_from_elim_to_O {A : Type}
  : NullHomotopy (to ∘ A) → IsConnected ∘ A.
  /-begin
    intros nh.
    exists (nh .1).
    apply O_ind; try exact _.
    intros; apply symmetry. apply (nh .2).
  end-/

  /- Now the general case follows. -/
  definition isconnected_from_elim {A : Type}
  : (Π(C : Type) [H : In ∘ C] (f : A → C), NullHomotopy f)
    → IsConnected ∘ A.
  /-begin
    intros H.
    exact (isconnected_from_elim_to_O (H (O A) (O_inO A) (to ∘ A))).
  end-/

  /- A type which is both connected and truncated is contractible. -/

  definition contr_trunc_conn {A : Type} [H : In ∘ A] [H : IsConnected ∘ A]
  : is_contr A.
  /-begin
    apply (contr_equiv _ (to ∘ A)⁻¹).
  end-/

  /- Here's another way of stating the universal property for mapping out of connected types into modal ones. -/
  definition extendable_const_isconnected_inO (n : nat)
             (A : Type@{i}) [H : IsConnected@{u a i] ∘ A}
             (C : Type@{j}) [H : In@{u a j] ∘ C}
  : ExtendableAlong@{i i j j} n (@const A unit@{i} star) (λ_, C).
  /-begin
    generalize dependent C;
      simple_induction n n IHn; intros C ?;
      [ exact star | split ].
    - intros f.
      exists (λ_, (isconnected_elim C f).1); intros a.
      apply symmetry. apply ((isconnected_elim C f).2).
    - intros h k.
      refine (extendable_postcompose' n _ _ _ _ (IHn (h star = k star) _)).
      intros []; apply equiv_idmap.
  end-/

  definition ooextendable_const_isconnected_inO
             (A : Type@{i}) [H : IsConnected@{u a i] ∘ A}
             (C : Type@{j}) [H : In@{u a j] ∘ C}
  : ooExtendableAlong (@const A unit star) (λ_, C) :=
       λn, extendable_const_isconnected_inO@{i j k j} n A C.

  definition isequiv_const_isconnected_inO [H : funext]
             {A : Type} [H : IsConnected ∘ A] (C : Type) [H : In ∘ C]
  : is_equiv (@const A C).
  /-begin
    refine (@isequiv_compose _ _ (λc u, c) _ _ _
              (isequiv_ooextendable (λ_, C) (@const A unit star)
                                    (ooextendable_const_isconnected_inO A C))).
  end-/

End ConnectedTypes.

/- Modally truncated maps -/

/- A map is "in [O]" if each of its fibers is. -/

Class MapIn (O : Modality) {A B : Type} (f : A → B) :=
     inO_hfiber_ino_map : Π(b:B), In ∘ (hfiber f b).

Global Existing Instance inO_hfiber_ino_map.

section ModalMaps
  Context (O : Modality).

  /- Any equivalence is modal -/
  definition mapinO_isequiv [instance] {A B : Type} (f : A → B) [H : is_equiv _ _ f]
  : MapIn ∘ f.
  /-begin
    intros b.
    pose (fcontr_isequiv f _ b).
    exact _.
  end-/

  /- Any map between modal types is modal. -/
  definition mapinO_between_inO {A B : Type} (f : A → B)
             [H : In ∘ A] [H : In ∘ B]
  : MapIn ∘ f.
  /-begin
    intros b; exact _.
  end-/

  /- Anything homotopic to a modal map is modal. -/
  definition mapinO_homotopic {A B : Type} (f : A → B) {g : A → B}
             (p : f ∼ g) [H : MapIn ∘ _ _ f]
  : MapIn ∘ g.
  /-begin
    intros b.
    refine (inO_equiv_inO (hfiber f b)
                          (equiv_hfiber_homotopic f g p b)).
  end-/

  /- Being modal is an hprop -/
  definition ishprop_mapinO [instance] [H : funext] {A B : Type} (f : A → B)
  : is_hprop (MapIn ∘ f).
  /-begin
    apply trunc_forall.
  end-/

  /- The composite of modal maps is modal -/
  definition mapinO_compose [instance] {A B C : Type} (f : A → B) (g : B → C)
         [H : MapIn ∘ _ _ f] [H : MapIn ∘ _ _ g]
  : MapIn ∘ (g ∘ f).
  /-begin
    intros c.
    refine (inO_equiv_inO _ (hfiber_compose f g c)⁻¹).
  end-/

End ModalMaps.

/- Modally connected maps -/

/- Connectedness of a map can again be defined in two equivalent ways: by connectedness of its fibers (as types), or by the lifting property/elimination principle against truncated types.  We use the former; the equivalence with the latter is given below in [conn_map_elim], [conn_map_comp], and [conn_map_from_extension_elim]. -/

Class IsConnMap (O : Modality) {A B : Type} (f : A → B) :=
     isconnected_hfiber_conn_map : Πb:B, IsConnected ∘ (hfiber f b).

Global Existing Instance isconnected_hfiber_conn_map.

section ConnectedMaps
  Context [H : Univalence] [H : funext].
  Context (O : Modality).

  /- Any equivalence is connected -/
  definition conn_map_isequiv [instance] {A B : Type} (f : A → B) [H : is_equiv _ _ f]
  : IsConnMap ∘ f.
  /-begin
    intros b.
    pose (fcontr_isequiv f _ b).
    unfold IsConnected; exact _.
  end-/

  /- Anything homotopic to a connected map is connected. -/
  definition conn_map_homotopic {A B : Type} (f g : A → B) (h : f ∼ g)
  : IsConnMap ∘ f → IsConnMap ∘ g.
  /-begin
    intros ? b.
    exact (isconnected_equiv ∘ (hfiber f b)
                             (equiv_hfiber_homotopic f g h b) _).
  end-/

  /- Being connected is an hprop -/
  definition ishprop_isconnmap [instance] [H : funext] {A B : Type} (f : A → B)
  : is_hprop (IsConnMap ∘ f).
  /-begin
    apply trunc_forall.
  end-/

  /- n-connected maps are orthogonal to n-truncated maps (i.e. familes of n-truncated types). -/
  definition conn_map_elim
             {A B : Type} (f : A → B) [H : IsConnMap ∘ _ _ f]
             (P : B → Type) {Πb:B, In ∘ (P b)}
             (d : Πa:A, P (f a))
  : Πb:B, P b.
  /-begin
    intros b.
    refine (dpr1 (isconnected_elim ∘ _ _)).
    2:exact b.
    intros [a p].
    exact (transport P p (d a)).
  end-/

  definition conn_map_comp
             {A B : Type} (f : A → B) [H : IsConnMap ∘ _ _ f]
             (P : B → Type) {Πb:B, In ∘ (P b)}
             (d : Πa:A, P (f a))
  : Πa:A, conn_map_elim f P d (f a) = d a.
  /-begin
    intros a. unfold conn_map_elim.
    set (fibermap := (fun a0p : hfiber f (f a)
                      => let (a0, p) := a0p in transport P p (d a0))).
    destruct (isconnected_elim ∘ (P (f a)) fibermap) as [x e].
    change (d a) with (fibermap ⟨a,1⟩).
    apply inverse, e.
  end-/

  definition isequiv_conn_ino_map {A B : Type} (f : A → B)
             [H : IsConnMap ∘ _ _ f] [H : MapIn ∘ _ _ f]
  : is_equiv f.
  /-begin
    apply isequiv_fcontr. intros b.
    apply (contr_trunc_conn O).
  end-/

  /- We can re-express this in terms of extensions. -/
  definition extension_conn_map_elim
        {A B : Type} (f : A → B) [H : IsConnMap ∘ _ _ f]
        (P : B → Type) {Πb:B, In ∘ (P b)}
        (d : Πa:A, P (f a))
  : ExtensionAlong f P d.
  /-begin
    exists (conn_map_elim f P d).
    apply conn_map_comp.
  end-/

  definition allpath_extension_conn_map
        {A B : Type} (f : A → B) [H : IsConnMap ∘ _ _ f]
        (P : B → Type) {Πb:B, In ∘ (P b)}
        (d : Πa:A, P (f a))
        (e e' : ExtensionAlong f P d)
  : e = e'.
  /-begin
    apply path_extension.
    refine (extension_conn_map_elim _ _ _).
  end-/

  /- It follows that [conn_map_elim] is actually an equivalence. -/
  definition isequiv_o_conn_map 
          {A B : Type} (f : A → B) [H : IsConnMap ∘ _ _ f]
          (P : B → Type) {Πb:B, In ∘ (P b)}
  : is_equiv (λ(g : Πb:B, P b), g oD f).
  /-begin
    apply isequiv_fcontr; intros d.
    apply contr_inhabited_hprop.
    - refine (@trunc_equiv' Σg : Πb, P b, g oD f ∼ d _ _ _ _).
      { refine (equiv_functor_sigma' (equiv_idmap _) _); intros g.
        apply equiv_path_forall. }
      apply hprop_allpath. intros g h.
      exact (allpath_extension_conn_map f P d g h).
    - exists (conn_map_elim f P d).
      apply path_forall; intros x; apply conn_map_comp.
  end-/

  /- Conversely, if a map satisfies this elimination principle (expressed via extensions), then it is connected.  This completes the proof of definition 7.5.7 from the book. -/
  definition conn_map_from_extension_elim {A B : Type} (f : A → B)
  : (Π(P : B → Type) {P_inO : Πb:B, In ∘ (P b)}
            (d : Πa:A, P (f a)),
       ExtensionAlong f P d)
    → IsConnMap ∘ f.
  /-begin
    intros Hf b. apply isconnected_from_elim_to_O.
    assert (e := Hf (λb, ∘ (hfiber f b)) _ (λa, to ∘ _ ⟨a,1⟩)).
    exists (e.1 b).
    intros [a p]. destruct p.
    apply symmetry. apply (e.2).
  end-/

  /- Corollary 7.5.8: It follows that the unit maps [to ∘ A] are connected. -/
  definition conn_map_to_O [instance] (A : Type) : IsConnMap ∘ (to ∘ A).
  /-begin
    apply conn_map_from_extension_elim; intros P ? d.
    exists (O_ind P d); intros a.
    apply O_ind_beta.
  end-/

  /- definition 7.5.6: Connected maps compose and cancel on the right. -/
  definition conn_map_compose [instance] {A B C : Type} (f : A → B) (g : B → C)
         [H : IsConnMap ∘ _ _ f] [H : IsConnMap ∘ _ _ g]
  : IsConnMap ∘ (g ∘ f).
  /-begin
    apply conn_map_from_extension_elim; intros P ? d.
    exists (conn_map_elim g P (conn_map_elim f (P ∘ g) d)); intros a.
    exact (conn_map_comp g P _ _ ⬝ conn_map_comp f (P ∘ g) d a).
  end-/      

  definition cancelR_conn_map {A B C : Type} (f : A → B) (g : B → C)
         [H : IsConnMap ∘ _ _ f] [H : IsConnMap ∘ _ _ (g ∘ f)]
  :  IsConnMap ∘ g.
  /-begin
    apply conn_map_from_extension_elim; intros P ? d.
    exists (conn_map_elim (g ∘ f) P (d oD f)); intros b.
    pattern b; refine (conn_map_elim f _ _ b); intros a.
    exact (conn_map_comp (g ∘ f) P (d oD f) a).
  end-/

  /- definition 7.5.10: A map to a type in [O] exhibits its codomain as the [O]-reflection of its domain if (and only if) it is [O]-connected. -/
  definition isequiv_O_rec_conn_map {A B : Type} [H : In ∘ B]
             (f : A → B) [H : IsConnMap ∘ _ _ f]
  : is_equiv (O_rec f).
  /-begin
    apply isequiv_conn_ino_map.
    - refine (cancelR_conn_map (to ∘ A) (O_rec f)).
      refine (conn_map_homotopic f _ _ _).
      intros a; apply symmetry. apply O_rec_beta.
    - apply mapinO_between_inO; exact _.
  end-/

  /- definition 7.5.12 -/
  section ConnMapFunctorSigma

    Context {A B : Type} {P : A → Type} {Q : B → Type}
            (f : A → B) (g : Πa, P a → Q (f a))
            [H : Πa, IsConnMap ∘ (g a)].

    definition equiv_O_hfiber_functor_sigma (b:B) (v:Q b)
    : ∘ (hfiber (functor_sigma f g) ⟨b,v⟩) ≃ ∘ (hfiber f b).
    /-begin
      equiv_via (O Σw : hfiber f b, hfiber (g w.1) ((w.2)⁻¹ ▹ v)).
      { apply equiv_O_functor, hfiber_functor_sigma. }
      equiv_via (O Σw : hfiber f b, ∘ (hfiber (g w.1) ((w.2)⁻¹ ▹ v))).
      { apply symmetry. apply equiv_O_sigma_O. }
      apply equiv_O_functor.
      apply equiv_sigma_contr; intros [a p]; simpl; exact _.
    end-/

    definition conn_map_functor_sigma [instance] [H : IsConnMap ∘ _ _ f]
    : IsConnMap ∘ (functor_sigma f g).
    /-begin
      intros [b v].
      /- Why is this so slow? -/
      refine (contr_equiv _ (equiv_inverse (equiv_O_hfiber_functor_sigma b v))).
    end-/

    definition conn_map_base_inhabited (inh : Πb, Q b)
               [H : IsConnMap ∘ _ _ (functor_sigma f g)]
    : IsConnMap ∘ f.
    /-begin
      intros b.
      refine (contr_equiv _ (equiv_O_hfiber_functor_sigma b (inh b))).
    end-/

  End ConnMapFunctorSigma.

  /- definition 7.5.13.  The "if" direction is a special case of [conn_map_functor_sigma], so we prove only the "only if" direction. -/
  definition conn_map_fiber
             {A : Type} {P Q : A → Type} (f : Πa, P a → Q a)
             [H : IsConnMap ∘ _ _ (functor_sigma idmap f)]
  : Πa, IsConnMap ∘ (f a).
  /-begin
    intros a q.
    refine (isconnected_equiv' ∘ (hfiber (functor_sigma idmap f) ⟨a,q⟩) _ _).
    exact (hfiber_functor_sigma_idmap P Q f a q).
  end-/

  /- definition 7.5.14: Connected maps are inverted by [O]. -/
  definition O_inverts_conn_map [instance] {A B : Type} (f : A → B)
         [H : IsConnMap ∘ _ _ f]
  : is_equiv (O_functor ∘ f).
  /-begin
    refine (isequiv_adjointify _ _ _ _).
    - apply O_rec; intros y.
      exact (O_functor ∘ dpr1 (center (O (hfiber f y)))).
    - unfold Sect; apply O_ind; try exact _; intros b.
      refine (ap (O_functor ∘ f) (O_rec_beta _ b) ⬝ _).
      refine ((O_functor_compose _ _ _ _)⁻¹ ⬝ _).
      set (x := (center (O (hfiber f b)))).
      clearbody x; revert x; apply O_ind; try exact _; intros [a p].
      refine (O_rec_beta (to ∘ B ∘ (f ∘ dpr1)) ⟨a,p⟩ ⬝ _).
      exact (ap (to ∘ B) p).
    - unfold Sect; apply O_ind; try exact _; intros a.
      refine (ap (O_rec _) (to_O_natural ∘ f a) ⬝ _).
      unfold compose; refine (O_rec_beta _ _ ⬝ _).
      transitivity (O_functor ∘ dpr1 (to ∘ (hfiber f (f a)) ⟨a,1⟩)).
      + apply ap, contr.
      + refine (to_O_natural _ _ _).
  end-/

End ConnectedMaps.

/- The modal factorization system -/

section ModalFact
  Context {fs : funext} (O : Modality).

  /- definition 7.6.4 -/
  definition image {A B : Type} (f : A → B)
  : Factorization (@IsConnMap O) (@MapIn O) f.
  /-begin
    refine (Build_Factorization Σb : B, ∘ (hfiber f b)
                                (λa, (f a ; to ∘ _ ⟨a,1⟩))
                                dpr1
                                (λa, 1)
                                _ _).
    - exact (conn_map_compose O
              (equiv_fibration_replacement f)
              (functor_sigma idmap (λb, to ∘ (hfiber f b)))).
    - intros b.
      exact (inO_equiv_inO _ (hfiber_fibration b (O ∘ (hfiber f)))).
  end-/

  /- This is the composite of the three displayed equivalences at the beginning of the proof of definition 7.6.5.  Note that it involves only a single factorization of [f]. -/
  definition O_hfiber_O_fact {A B : Type} {f : A → B}
        (fact : Factorization (@IsConnMap O) (@MapIn O) f) (b : B)
  : ∘ (hfiber (factor2 fact ∘ factor1 fact) b)
      ≃ hfiber (factor2 fact) b.
  /-begin
    refine (equiv_compose' _
             (equiv_O_functor O
               (hfiber_compose (factor1 fact) (factor2 fact) b))).
    refine (equiv_compose'
             (equiv_sigma_contr (λw, ∘ (hfiber (factor1 fact) w.1)))
             _).
    - intros w; exact (inclass1 fact w.1).
    - refine (equiv_inverse
                (equiv_sigma_inO_O (λw, hfiber (factor1 fact) w.1))).
      exact (inclass2 fact b).
  end-/

  /- This is the corresponding first three of the displayed "mapsto"s in proof of definition 7.6.5, and also the last three in reverse order, generalized to an arbitrary path [p].  Note that it is much harder to prove than in the book, because we are working in the extra generality of a modality where [O_ind_beta] is only propositional. -/
  definition O_hfiber_O_fact_inverse_beta {A B : Type} {f : A → B}
        (fact : Factorization (@IsConnMap O) (@MapIn O) f)
        (a : A) (b : B) (p : factor2 fact (factor1 fact a) = b)
  : (O_hfiber_O_fact fact b)⁻¹
      ⟨factor1 fact a , p⟩ = to ∘ _ ⟨a , p⟩.
  /-begin
    set (g := factor1 fact); set (h := factor2 fact).
    apply moveR_equiv_V.
    unfold O_hfiber_O_fact.
    ev_equiv.
    apply moveL_equiv_M.
    transitivity (existT (λ(w : hfiber h b), ∘ (hfiber g w.1))
                         ⟨g a, p⟩ (to ∘ (hfiber g (g a)) ⟨a , 1⟩)).
    - apply moveR_equiv_V; reflexivity.
    - apply moveL_equiv_V.
      transitivity (to ∘ _ (existT (λ(w : hfiber h b), (hfiber g w.1))
                         ⟨g a, p⟩ ⟨a , 1⟩)).
      + simpl; unfold compose.
        repeat (simpl rewrite @O_rec_beta); reflexivity.
      + apply symmetry. apply to_O_natural.
  Qed.

  section TwoFactorizations
    Context {A B : Type} (f : A → B)
            (fact fact' : Factorization (@IsConnMap O) (@MapIn O) f).

    Let H := λx, fact_factors fact x ⬝ (fact_factors fact' x)⁻¹.

    /- definition 7.6.5, part 1. -/
    definition equiv_O_factor_hfibers (b:B)
    : hfiber (factor2 fact) b ≃ hfiber (factor2 fact') b.
    Proof.
      refine (equiv_compose' (O_hfiber_O_fact fact' b) _).
      refine (equiv_compose' _ (equiv_inverse (O_hfiber_O_fact fact b))).
      apply equiv_O_functor.
      apply equiv_hfiber_homotopic.
      exact H.
    end-/

    /- definition 7.6.5, part 2. -/
    definition equiv_O_factor_hfibers_beta (a : A)
    : equiv_O_factor_hfibers (factor2 fact (factor1 fact a))
                             ⟨factor1 fact a , 1⟩
      = (factor1 fact' a ; (H a)⁻¹).
    /-begin
      unfold equiv_O_factor_hfibers.
      ev_equiv.
      apply moveR_equiv_M.
      do 2 rewrite O_hfiber_O_fact_inverse_beta.
      unfold equiv_fun, equiv_O_functor.
      transitivity (to ∘ _
                       (equiv_hfiber_homotopic
                          (factor2 fact ∘ factor1 fact)
                          (factor2 fact' ∘ factor1 fact') H
                          (factor2 fact (factor1 fact a)) ⟨a,1⟩)).
      - refine (to_O_natural ∘ _ _).
      - apply ap.
        simpl.
        apply ap; auto with path_hints.
    Qed.

  End TwoFactorizations.

  /- definition 7.6.6.  Recall that a lot of hard work was done in [Factorization.path_factorization]. -/
  definition O_factsys : FactorizationSystem.
  Proof.
    refine (Build_FactorizationSystem
              (@IsConnMap O) _ _ _
              (@MapIn O) _ _ _
              (@image) _).
    intros A B f fact fact'.
    refine (Build_PathFactorization fact fact' _ _ _ _).
    - refine (equiv_compose' _ (equiv_fibration_replacement (factor2 fact))).
      refine (equiv_compose' (equiv_inverse (equiv_fibration_replacement (factor2 fact'))) _).
      refine (equiv_functor_sigma' (equiv_idmap B) _); intros b; simpl.
      apply equiv_O_factor_hfibers.
    - intros a; exact (pr1_path (equiv_O_factor_hfibers_beta f fact fact' a)).
    - intros x.
      exact ((equiv_O_factor_hfibers f fact fact' (factor2 fact x) ⟨x , 1⟩).2 ⁻¹).
    - intros a.
      apply moveR_pM.
      refine ((inv_V _)⁻¹ ⬝ _ ⬝ inv_V _); apply inverse2.
      refine (_ ⬝ pr2_path (equiv_O_factor_hfibers_beta f fact fact' a)).
      refine (_ ⬝ (transport_paths_Fl _ _)⁻¹).
      /- Apparently Coq needs a little help to see that these paths are the same. -/
      match goal with
          |- ((?p)⁻¹ ⬝ ?q)⁻¹ = _ ⬝ _ => change ((p⁻¹ ⬝ q)⁻¹ = q⁻¹ ⬝ p)
      end.
      refine (inv_pp _ _ ⬝ (1 @@ inv_V _)).
  end-/

End ModalFact.

End Modalities_Theory.

/- Restriction of a family of modalities -/

/- This is just like restriction of reflective subuniverses. -/
Module Type Modalities_Restriction_Data (Os : Modalities).

  Parameter New_Modality : Type2@{u a}.

  Parameter Modalities_restriction
  : New_Modality → Os.Modality.

End Modalities_Restriction_Data.

Module Modalities_Restriction
       (Os : Modalities)
       (Res : Modalities_Restriction_Data Os)
<: Modalities.

  definition Modality := Res.New_Modality.

  definition O_reflector (O : Modality@{u a}) :=
       Os.O_reflector@{u a i} (Res.Modalities_restriction O).
  definition inO_internal (O : Modality@{u a}) :=
       Os.inO_internal@{u a i} (Res.Modalities_restriction O).
  definition O_inO_internal (O : Modality@{u a}) :=
       Os.O_inO_internal@{u a i} (Res.Modalities_restriction O).
  definition to (O : Modality@{u a}) :=
       Os.to@{u a i} (Res.Modalities_restriction O).
  definition inO_equiv_inO_internal (O : Modality@{u a}) :=
       Os.inO_equiv_inO_internal@{u a i} (Res.Modalities_restriction O).
  definition hprop_inO_internal (H : funext) (O : Modality@{u a}) :=
       Os.hprop_inO_internal@{u a i} H (Res.Modalities_restriction O).
  definition O_ind_internal (O : Modality@{u a}) :=
       Os.O_ind_internal@{u a i j} (Res.Modalities_restriction O).
  definition O_ind_beta_internal (O : Modality@{u a}) :=
       Os.O_ind_beta_internal@{u a i j} (Res.Modalities_restriction O).
  definition minO_paths (O : Modality@{u a}) :=
       Os.minO_paths@{u a i} (Res.Modalities_restriction O).

End Modalities_Restriction.

/- Accessible modalities -/

/- A modality is accessible just when its underlying reflective (or unit-) subuniverse is accessible.  However, for modalities we have a simpler characterization in terms of families of generating connected objects rather than families of generating inverted maps.  We call an object [S]-null if it is local with respect to the maps [S i → unit]. -/

Record NullGenerators :=
  { ngen_indices : Type@{a} ;
    ngen_type : ngen_indices → Type@{a}
  }.

Coercion ngen_type : NullGenerators >-> Funclass.

definition null_to_local_generators : NullGenerators@{a1} → LocalGenerators@{a2} :=
     λS, Build_LocalGenerators (ngen_indices S) (ngen_type S) (λ_, unit@{a2}) (λ_ _, star).

/- We recall the nonce definition [IsLocal] from [ReflectiveSubuniverse]. -/
Import IsLocal_Internal.
/- Similarly, the real version of this notation will be defined in hit/Localizations. -/
Local definition IsNull (S : NullGenerators@{a}) (X : Type@{i}) :=
     IsLocal@{i i a} (null_to_local_generators@{a a} S) X.


/- A central fact: if a type [X] is null for all the fibers of a map [f], then it is [f]-local.  (NB: the converse is *not* generally tt.) -/
definition extendable_isnull_fibers (n : nat)
           {A B} (f : A → B) (C : B → Type)
: (Πb, ooExtendableAlong (@const (hfiber f b) unit star)
                               (λ_, C b))
  → ExtendableAlong n f C.
/-begin
  revert C.
  simple_induction n n IHn; intros C null; [exact star | split].
  - intros g.
    exists (λb, (pr1 (null b 1%nat) (λx, x.2 ▹ g x.1)).1 star).
    intros a.
    rewrite (path_unit star (const star a)).
    exact ((pr1 (null (f a) 1%nat) _).2 ⟨a , 1⟩).
  - intros h k.
    apply IHn; intros b.
    apply ooextendable_homotopy, null.
end-/

definition ooextendable_isnull_fibers {A B} (f : A → B) (C : B → Type)
: (Πb, ooExtendableAlong (@const (hfiber f b) unit star)
                               (λ_, C b))
  → ooExtendableAlong f C :=
   λnull n, extendable_isnull_fibers n f C null.

/- We define a modality to be accessible if it consists of the null types for some family of generators as above. -/
Module Type Accessible_Modalities (Os : Modalities).
  Import Os.

  /- See comment in [Accessible_ReflectiveSubuniverses] about collapsing universes. -/
  Parameter acc_gen : Modality@{u a} → NullGenerators@{a}.
  Check acc_gen@{u a}.    /- Verify that we have the right number of universes -/

  Parameter inO_iff_isnull_internal
  : Π(O : Modality@{u a}) (X : Type@{i}),
      iff@{i i i}
         (inO_internal@{u a i} ∘ X)
         (IsNull@{a i} (acc_gen@{u a} O) X).
  Check inO_iff_isnull_internal@{u a i}.

End Accessible_Modalities.

/- We will now show that a modality is accessible in this sense if and only if its underlying reflective subuniverse is accessible in the sense previously defined.  These proofs involve a bit of annoying module wrangling.  Fortunately, we (almost?) never need to actually use them; in practice accessible modalities usually seem to be given to us with the appropriate sort of generators. -/

/- One direction of this implication is trivial. -/
Module Accessible_Modalities_to_ReflectiveSubuniverses
       (Os : Modalities) (Acc : Accessible_Modalities Os).

  /- Coq won't let us write [<: Accessible_ReflectiveSubuniverses (Modalities_to_ReflectiveSubuniverses Os)]; it says "Application of modules is restricted to paths" (a "path" being something like [Foo.Bar.Baz]).  Thus, every intermediate module has to be given its own name. -/
  Module Os_RSU := Modalities_to_ReflectiveSubuniverses Os.
  Module AccRSU <: Accessible_ReflectiveSubuniverses Os_RSU.

    Import Os_RSU Acc.

    definition acc_gen : ReflectiveSubuniverse@{u a} → LocalGenerators@{a} :=
         λ(O : ReflectiveSubuniverse@{u a}),
           (null_to_local_generators (acc_gen O)).

    definition inO_iff_islocal_internal
    : Π(O : ReflectiveSubuniverse@{u a}) (X : Type@{i}),
      iff@{i i i}
         (inO_internal@{u a i} ∘ X)
         (IsLocal@{i i a} (acc_gen@{u a} O) X) :=
         inO_iff_isnull_internal@{u a i}.

  End AccRSU.
End Accessible_Modalities_to_ReflectiveSubuniverses.

/- The converse is less trivial. -/
Module Accessible_Modalities_from_ReflectiveSubuniverses
       (Os : Modalities).

  Module Os_RSU := Modalities_to_ReflectiveSubuniverses Os.
  Module AccMod (Acc : Accessible_ReflectiveSubuniverses Os_RSU)
    <: Accessible_Modalities Os.

    Import Os Acc.
    Module Import Os_Theory := Modalities_Theory Os.
    Module Import Acc_Theory := Accessible_ReflectiveSubuniverses_Theory Os_RSU Acc.

    /- The idea is as follows.  By [ooextendable_isnull_fibers], we can detect locality with respect to a map by nullity with respect to its fibers.  Therefore, our first thought might be to just consider all the fibers of all the maps that we are localizing at.  However, this doesn't quite work because [ooextendable_isnull_fibers] is not an if-and-only-if, so not every modal type would necessarily be null for that type family.

     We do know, however, that if [f] is an [O]-connected map, then any [O]-modal type is null for its fibers (since they are [O]-connected types).  There is no *a priori* why all the maps we localize at should end up being connected for the modality; they will always be inverted, but not every inverted map is connected (unless the modality is lex).  But if [f : A → B] is [O]-inverted, then the [O]-connected map [to ∘ A] is (up to equivalence) the composite of [f] with the [O]-connected map [to ∘ B].  Thus, if [X] is null for the fibers of [to ∘ A] and [to ∘ B], it will be [f]-local and hence [O]-modal, while all [O]-modal types will be null for these fibers since they are connected. -/

    definition acc_gen (O : Modality@{u a}) : NullGenerators@{a}.
    /-begin
      refine (Build_NullGenerators
                (  { i : lgen_indices@{a} (acc_gen O)
                     & ∘ (lgen_domain@{a} (acc_gen O) i) }
                 + { i : lgen_indices@{a} (acc_gen O)
                     & ∘ (lgen_codomain@{a} (acc_gen O) i) })
                _).
      intros [ [i x] | [i x] ]; exact (hfiber (to ∘ _) x).
    end-/

    definition inO_iff_isnull_internal (O : Modality@{u a}) (X : Type@{i})
    : iff@{i i i} (In@{u a i} ∘ X) (IsNull@{a i} (acc_gen O) X).
    /-begin
      split.
      - intros X_inO [ [i x] | [i x] ];
          exact (ooextendable_const_isconnected_inO@{u a a i i} ∘ _ _ ).
      - intros Xnull.
        apply (pr2 (inO_iff_islocal_internal ∘ X)); intros i.
        refine (cancelL_ooextendable@{a a a i i i i i i i}
                  (λ_, X) (Acc.acc_gen ∘ i)
                  (to ∘ (lgen_codomain (Acc.acc_gen O) i)) _ _).
        + apply ooextendable_isnull_fibers@{a a i i a a i}; intros x.
          exact (Xnull (inr ⟨i,x⟩)).
        + refine (ooextendable_homotopic _
                   (O_functor ∘ (Acc.acc_gen ∘ i)
                              ∘ to ∘ (lgen_domain (Acc.acc_gen O) i)) _ _).
          1:apply to_O_natural.
          apply ooextendable_compose@{a a a i i i i}.
          × apply ooextendable_equiv, O_inverts_generators.
          × apply ooextendable_isnull_fibers; intros x.
            exact (Xnull (inl ⟨i,x⟩)).
    end-/
    
  End AccMod.
End Accessible_Modalities_from_ReflectiveSubuniverses.

/- The construction of the nullification modality for any family of types will be in [hit/Localization]. -/


/- Examples -/

/- Double negation -/

/- Finally, we give one nontrivial example of a modality.  This is Exercise 7.12 in the book.  Note that it is (apparently) *not* accessible unless we assume propositional resizing. -/

/- We are defining only one modality, but it depends on funext.  Therefore, we let the family of modalities be the type [funext].  However, since there is a coercion [O_reflector] from [Modality] to [Funclass], we don't want to simply *define* [Modality] to be [funext], or else we could start applying [funext] hypotheses to types and having it act as double negation.

Instead, we define a [Record] wrapper around it.  This is the recommended best practice for all modules (with one exception, see Truncations.v).  The constructor of the record should generally be a short name (here [Notnot]) that makes sense as the reflector. -/

Record Notnot_Modality := Notnot { unNotnot : funext }.

Module Notnot_Easy_Modalities <: EasyModalities.

  definition Modality : Type2@{u a} :=
       Notnot_Modality.

  definition O_reflector : Modality@{u a} → Type@{i} → Type@{i}
    /- We call [not] explicitly with universe annotations so that [O_reflector] has the right number of universe parameters to satisfy the module type. -/ :=
       λO X, not@{i i i} (not@{i i i} X).

  definition to (O : Modality@{u a}) (T : Type@{i})
  : T → O_reflector@{u a i} ∘ T :=
     λx nx, nx x.

  definition O_indO (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} ∘ A → Type@{j})
  : (Πa : A, O_reflector@{u a j} ∘ (B (to ∘ A a))) ->
    Πz : O_reflector@{u a i} ∘ A, O_reflector@{u a j} ∘ (B z).
  /-begin
    intros f z nBz.
    pose (unNotnot O).          /- Access the [funext] hypothesis -/
    /- The goal is [Empty@{j}], whereas [z] has codomain [Empty@{i}].  Thus, simply applying [z] would collapse the universe parameters undesirably, so we first alter the goal to be [Empty@{i}]. -/
    cut (Empty@{i}); [ intros [] | ].
    apply z; intros a.
    /- Now the goal is [Empty@{i}], whereas [f] has codomain [Empty@{j}]. -/
    cut (Empty@{j}); [ intros [] | ].
    exact (f a (transport (λx, not@{j j j} (B x))
                          (path_ishprop _ _)
                          nBz)).
  end-/

  definition O_indO_beta (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} ∘ A → Type@{j})
             (f : Πa, O_reflector@{u a j} ∘ (B (to ∘ A a))) (a:A)
  : O_indO ∘ A B f (to ∘ A a) = f a.
  /-begin
    pose (unNotnot O).
    apply path_ishprop.
  end-/

  definition minO_pathsO (O : Modality@{u a}) (A : Type@{i})
             (z z' : O_reflector@{u a i} ∘ A)
  : is_equiv@{i i} (to@{u a i} ∘ (z = z')).
  /-begin
    pose (unNotnot O).
    refine (isequiv_iff_hprop _ _).
    intros; apply path_ishprop.
  end-/

End Notnot_Easy_Modalities.

Module Notnot_Modalities <: Modalities := EasyModalities_to_Modalities Notnot_Easy_Modalities.

/- After we define any family of modalities or reflective subuniverses, we give a corresponding name to the theory module, generally by postfixing the above-mentioned record constructor with [M] (for "module").  This way, one can either [Import] the theory module (here [NotnotM]) and get access to all the modality functions for the modalities in question, or not import it and access them qualified as [NotnotM.function_name]. -/
Module NotNotM := Modalities_Theory Notnot_Modalities.
Export NotNotM.Coercions.
Export NotNotM.RSU.Coercions.

/- Finally, we declare a coercion allowing us to use elements of the record wrapper as modalities. -/
Coercion Notnot_Modalities_to_Modalities := idmap
  : Notnot_Modality → Notnot_Modalities.Modality.

/- The identity modality -/

/- Of course, there is also the trivial example. -/

Inductive Identity_Modality : Type1 :=
     purely : Identity_Modality.

Module Identity_Modalities <: Modalities.

  definition Modality : Type2@{u a} :=
       Identity_Modality@{a}.

  definition O_reflector : Π(O : Modality@{u a}),
                            Type@{i} → Type@{i} :=
       λO X, X.

  definition inO_internal : Π(O : Modality@{u a}),
                             Type@{i} → Type@{i} :=
       λO X, unit@{i}.

  definition O_inO_internal : Π(O : Modality@{u a}) (T : Type@{i}),
                               inO_internal@{u a i} ∘ (O_reflector@{u a i} ∘ T) :=
       λO X, star.

  definition to : Π(O : Modality@{u a}) (T : Type@{i}),
                   T → O_reflector@{u a i} ∘ T :=
       λO X x, x.

  definition inO_equiv_inO_internal :
      Π(O : Modality@{u a}) (T U : Type@{i})
             (T_inO : inO_internal@{u a i} ∘ T) (f : T → U) (feq : is_equiv f),
        inO_internal@{u a i} ∘ U :=
       λO T U _ _ _, star.

  definition hprop_inO_internal
  : funext → Π(O : Modality@{u a}) (T : Type@{i}),
                is_hprop (inO_internal@{u a i} ∘ T) :=
       λ_ ∘ T, _.

  definition O_ind_internal
  : Π(O : Modality@{u a})
           (A : Type@{i}) (B : O_reflector ∘ A → Type@{j})
           (B_inO : Πoa, inO_internal@{u a j} ∘ (B oa)),
      (Πa, B (to ∘ A a)) → Πa, B a :=
     λO A B _ f a, f a.

  definition O_ind_beta_internal
  : Π(O : Modality@{u a})
           (A : Type@{i}) (B : O_reflector ∘ A → Type@{j})
           (B_inO : Πoa, inO_internal@{u a j} ∘ (B oa))
           (f : Πa : A, B (to ∘ A a)) (a:A),
      O_ind_internal ∘ A B B_inO f (to ∘ A a) = f a :=
       λ_ _ _ _ _ _, 1.

  definition minO_paths
  : Π(O : Modality@{u a})
           (A : Type@{i}) (A_inO : inO_internal@{u a i} ∘ A) (z z' : A),
      inO_internal@{u a i} ∘ (z = z') :=
       λ_ _ _ _ _, star.

End Identity_Modalities.

Module purelyM := Modalities_Theory Identity_Modalities.
Export purelyM.Coercions.
Export purelyM.RSU.Coercions.

Coercion Identity_Modalities_to_Modalities := idmap
  : Identity_Modality → Identity_Modalities.Modality.


Module Accessible_Identity <: Accessible_Modalities Identity_Modalities.

  Import Identity_Modalities.

  definition acc_gen : Modality@{u a} → NullGenerators@{a} :=
       λ_, Build_NullGenerators Empty@{a} (λ_, Empty@{a}).

  definition inO_iff_isnull_internal
  : Π(O : Modality@{u a}) (X : Type@{i}),
      iff@{i i i}
        (inO_internal@{u a i} ∘ X)
        (IsNull@{a i} (acc_gen O) X) :=
       λO X, (λ_, Empty_ind _ , λ_, star).

End Accessible_Identity.

/- For more examples of modalities, see hit/Truncations.v, hit/PropositionalFracture.v, and hit/Localization.v. -/
