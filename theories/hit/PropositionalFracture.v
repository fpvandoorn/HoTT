/- -*- mode: coq; mode: visual-line -*-  -/

Require Import HoTT.Basics HoTT.Types.
Require Import HProp TruncType Extensions ReflectiveSubuniverse Modality.
Require Import hit.Pushout hit.Join hit.Localization hit.Nullification.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

/- Open and closed modalities and the propositional fracture theorem -/

Record Open_Modality :=
  Op { funext_Op : Funext ;
       unOp : hProp
     }.

/- Exercise 7.13(i): Open modalities -/
Module OpenModalities_easy <: EasyModalities.

  definition Modality : Type@{u} := Open_Modality@{a}.

  definition O_reflector : Modality@{u a} → Type@{i} → Type@{i} :=
       λfU X, unOp fU → X.

  definition to (O : Modality@{u a}) (T : Type@{i}) : T → O_reflector@{u a i} ∘ T :=
       λx u, x.

  definition O_indO (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector ∘ A → Type@{j})
             (f : Πa, O_reflector@{u a j} ∘ (B (to@{u a i} ∘ A a)))
    : Πz, O_reflector@{u a j} ∘ (B z).
  /-begin
    intros z u; pose (funext_Op O).
    refine (transport@{i j} B _ (f (z u) u)).
    apply path_arrow; intros u'.
    unfold to; apply ap; apply path_ishprop.
  end-/

  definition O_indO_beta (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} ∘ A → Type@{j})
             (f : Πa, O_reflector@{u a j} ∘ (B (to ∘ A a))) (a : A)
  : O_indO ∘ A B f (to ∘ A a) ≈ f a.
  /-begin
    pose (funext_Op O); apply path_arrow; intros u.
    transitivity (transport B 1 (f a u));
      auto with path_hints.
    apply (ap (λp, transport B p (f a u))).
    transitivity (path_arrow (λ_, a) (λ_, a) (@ap10 (unOp O) _ _ _ 1));
      auto with path_hints.
    × apply ap@{i i}.
      apply path_forall; intros u'.
      apply ap_const.
    × apply eta_path_arrow.
  end-/

  definition minO_pathsO (O : Modality@{u a}) (A : Type@{i})
             (z z' : O_reflector@{u a i} ∘ A)
  : IsEquiv@{i i} (to ∘ (z ≈ z')).
  /-begin
    pose (fs := funext_Op O); refine (isequiv_adjointify _ _ _ _).
    × intros f; apply path_arrow; intros u.
      exact (ap10 (f u) u).
    × intros f; apply path_arrow; intros u.
      transitivity (path_arrow z z' (ap10 (f u))).
      + unfold to; apply ap@{i i}.
        apply path_forall; intros u'.
        apply (ap (λu0, ap10 (f u0) u')).
        apply path_ishprop.
      + apply eta_path_arrow.
    × intros p.
      refine (eta_path_arrow _ _ _).
  end-/

End OpenModalities_easy.

Module OpenModalities <: Modalities :=
     EasyModalities_to_Modalities OpenModalities_easy.

Module OpM := Modalities_Theory OpenModalities.
Export OpM.Coercions.
Export OpM.RSU.Coercions.

Coercion Open_Modality_to_Modality :=
  idmap : Open_Modality → OpenModalities.Modality.

/- The open modality is accessible. -/
Module Accessible_OpenModalities <: Accessible_Modalities OpenModalities.

  definition acc_gen :=
       λ(O : OpenModalities.Modality@{u a}),
         Build_NullGenerators@{a} unit@{a} (λ_, unOp O).

  definition inO_iff_isnull_internal
             (O : OpenModalities.Modality@{u a}) (X : Type@{i})
  : iff@{i i i}
      (OpenModalities.inO_internal@{u a i} ∘ X)
      (IsNull (acc_gen O) X).
  /-begin
    pose (funext_Op O); split.
    - intros X_inO u.
      apply (equiv_inverse (equiv_ooextendable_isequiv _ _)).
      refine (cancelR_isequiv (λx (u:unit), x)).
      apply X_inO.
    - intros ext; specialize (ext star).
      refine (isequiv_compose (f := (λx, unit_name x))
                              (g := (λh, h ∘ (@const (unOp O) unit star)))).
      refine (isequiv_ooextendable (λ_, X) (@const (unOp O) unit star) ext).
  end-/

End Accessible_OpenModalities.

/- Thus, arguably a better definition of [Op] would be as a nullification modality, as it would not require [Funext] and would have a judgmental computation rule.  However, the above definition is also nice to know, as it doesn't use HITs.  We name the other version [Op']. -/
definition Op' (U : hProp) : Nullification_Modality :=
     Nul (Build_NullGenerators unit (λ(_:unit), U)).

/- Exercise 7.13(ii): Closed modalities -/

/- We begin by characterizing the modal types. -/
section ClosedModalTypes
  Context (U : hProp).

  definition equiv_inO_closed (A : Type)
  : (U → is_contr A) <-> IsEquiv (λa:A, push (inr a) : join U A).
  /-begin
    split.
    - intros uac.
      refine (isequiv_adjointify _ _ _ _).
      × refine (pushout_rec A _ _).
        + intros [u | a].
          { pose (uac u). exact (center A). }
          { assumption. }
        + intros [u a]. simpl.
          pose (uac u). apply contr.
      × intros z. pattern z.
        refine (pushout_ind pr1 pr2 _ _ _ z).
        + intros [u | a].
          { pose (contr_inhabited_hprop U u).
            apply path_contr. } 
          { reflexivity. }
        + intros [u a]; pose (contr_inhabited_hprop U u).
          apply path_contr.
      × intros a. reflexivity.
    - intros ? u.
      refine (contr_equiv (join U A) (λa:A, push (inr a))⁻¹).
      pose (contr_inhabited_hprop U u).
      exact _.
  end-/

End ClosedModalTypes.

Record Closed_Modality := Cl { unCl : hProp }.

Module ClosedModalities <: Modalities.

  definition Modality : Type@{u} := Closed_Modality@{a}.

  definition O_reflector : Modality@{u a} → Type@{i} → Type@{i} :=
       λO X, join@{a i i} (unCl O) X.

  definition inO_internal : Modality@{u a} → Type@{i} → Type@{i} :=
       λO X, unCl ∘ → is_contr X.

  definition O_inO_internal (O : Modality@{u a}) (T : Type@{i})
  : inO_internal@{u a i} ∘ (O_reflector@{u a i} ∘ T).
  /-begin
    intros u.
    pose (contr_inhabited_hprop _ u).
    exact _.
  end-/

  definition to (O : Modality@{u a}) (T : Type@{i})
  : T → O_reflector@{u a i} ∘ T :=
       λx, push (inr x).

  definition inO_equiv_inO_internal (O : Modality@{u a}) (T U : Type@{i})
     (T_inO : inO_internal@{u a i} ∘ T) (f : T → U) (feq : IsEquiv@{i i} f)
  : inO_internal@{u a i} ∘ U.
  /-begin
    intros u; pose (T_inO u).
    refine (contr_equiv _ f); exact _.
  end-/

  definition hprop_inO_internal [H : Funext]
             (O : Modality@{u a}) (T : Type@{i})
  : is_hprop (inO_internal@{u a i} ∘ T).
  /-begin
    exact _.
  end-/

  definition O_ind_internal (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} ∘ A → Type@{j})
             (B_inO : Πoa, inO_internal@{u a j} ∘ (B oa))
             (f : Πa : A, B (to ∘ A a))
             (z : O_reflector ∘ A)
  : B z.
  /-begin
    refine (pushout_ind@{i a i j j} _ _ B _ _ z).
    - intros [u | a].
      + apply center, B_inO, u.
      + apply f.
    - intros [u a].
      pose (B_inO (push (inr a)) u).
      apply path_contr.
  end-/

  definition O_ind_beta_internal (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} ∘ A → Type@{j})
             (B_inO : Πoa, inO_internal@{u a j} ∘ (B oa))
             (f : Πa : A, B (to ∘ A a)) (a : A)
  : O_ind_internal ∘ A B B_inO f (to ∘ A a) ≈ f a :=
     1.

  definition minO_paths (O : Modality@{u a}) (A : Type@{i})
             (A_inO : inO_internal@{u a i} ∘ A)
             (z z' : A)
  : inO_internal@{u a i} ∘ (z ≈ z').
  /-begin
    intros u; pose (A_inO u); apply contr_paths_contr.
  end-/

End ClosedModalities.

Module ClM := Modalities_Theory ClosedModalities.
Export ClM.Coercions.
Export ClM.RSU.Coercions.

Coercion Closed_Modality_to_Modality :=
  idmap : Closed_Modality → ClosedModalities.Modality.

/- The closed modality is accessible. -/
Module Accessible_ClosedModalities
  <: Accessible_Modalities ClosedModalities.

  definition acc_gen :=
       λ(O : ClosedModalities.Modality@{u a}),
         Build_NullGenerators@{a} (unCl O) (λ_, Empty@{a}).

  definition inO_iff_isnull_internal
             (O : ClosedModalities.Modality@{u a}) (X : Type@{i})
  : iff@{i i i}
      (ClosedModalities.inO_internal@{u a i} ∘ X)
      (IsNull (acc_gen O) X).
  /-begin
    split.
    - intros X_inO u.
      pose (X_inO u).
      apply ooextendable_contr; exact _.
    - intros ext u.
      exists ((pr1 (ext u 1%nat) Empty_rec).1 star); intros x.
      unfold const in ext.
      exact ((pr1 (pr2 (ext u 2) (pr1 (ext u 1%nat) Empty_rec).1
                       (λ_, x)) (Empty_ind _)).1 star).
  end-/

End Accessible_ClosedModalities.

/- Thus, it also has the following alternative version. -/
definition Cl' (U : hProp) : Nullification_Modality :=
     Nul (Build_NullGenerators U (λ_, Empty)).
