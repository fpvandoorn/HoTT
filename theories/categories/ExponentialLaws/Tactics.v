/- Miscellaneous helper tactics for proving exponential laws -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import HoTT.Tactics Basics.PathGroupoids Types.ΠTypes.Prod.

/- These are probably more general than just exponential laws, but I haven't tried them more widely, yet. -/

/- Miscellaneous tactics to try -/
Ltac exp_laws_misc_t' :=
  idtac;
  match goal with
    | _ => reflexivity
    | _ => progress intros
    | _ => progress simpl in *
    | _ => apply (@path_Π_); intro
    | _ => rewrite !identity_of
    | _ => progress autorewrite with morphism
  end.

/- Safe transformations to simplify complex types in the hypotheses or goal -/
Ltac exp_laws_simplify_types' :=
  idtac;
  match goal with
    | [ H : (_ + _)%type |- _ ] => destruct H
    | [ H : unit |- _ ] => destruct H
    | [ H : Empty |- _ ] => destruct H
    | [ H : (_ × _)%type |- _ ] => destruct H
    | [ |- _ ≈ _ :> Functor _ _ ] => progress path_functor
    | [ |- _ ≈ _ :> NaturalTransformation _ _ ] => progress path_natural_transformation
    | [ |- _ ≈ _ :> prod _ _ ] => apply path_prod
  end.

/- Do some simplifications of contractible types -/
Ltac exp_laws_handle_contr' :=
  idtac;
  match goal with
    | [ H : is_contr ?T, x : ?T |- _ ] => progress destruct (contr x)
    | [ H : Πa, is_contr (?T a), x : ?T _ |- _ ] => progress destruct (contr x)
    | [ H : Πa b, is_contr (?T a b), x : ?T _ _ |- _ ] => progress destruct (contr x)
    | [ |- context[contr (center ?x)] ]
      => progress let H := fresh in
                  assert (H : idpath ≈ contr (center x)) by exact (center _);
                    destruct H
  end.

/- Try to simplify [transport] with some heuristics -/
Ltac exp_laws_handle_transport' :=
  idtac;
  match goal with
    | _ => progress rewrite ?transport_forall_constant, ?path_forall_2_beta, ?transport_const, ?path_functor_uncurried_fst, ?transport_path_prod
    | [ |- context[transport (λy, ?f (@object_of ?C ?D y ?x))] ]
      => rewrite (λa b, @transport_compose _ _ a b (λy', f (y' x)) (@object_of C D))
    | [ |- context[transport (λy, ?f (@object_of ?C ?D y ?x) ?z)] ]
      => rewrite (λa b, @transport_compose _ _ a b (λy', f (y' x) z) (@object_of C D))
    | [ |- context[transport (λy, ?f (@object_of ?C ?D y ?x) ?z)] ]
      => rewrite (λa b, @transport_compose _ _ a b (λy', f (y' x) z) (@object_of C D))
    | [ |- context[transport (λy, ?f (?g (@object_of ?C ?D y ?x)))] ]
      => rewrite (λa b, @transport_compose _ _ a b (λy', f (g (y' x))) (@object_of C D))
    | [ |- context[transport (λy, ?f (?g (@object_of ?C ?D y ?x)) ?z)] ]
      => rewrite (λa b, @transport_compose _ _ a b (λy', f (g (y' x)) z) (@object_of C D))
    | _ => progress transport_path_forall_hammer
    | [ |- context[components_of (transport ?P ?p ?z)] ]
      => simpl rewrite (@ap_transport _ P _ _ _ p (λ_, components_of) z)
    | [ |- context[object_of (transport ?P ?p ?z)] ]
      => simpl rewrite (@ap_transport _ P _ _ _ p (λ_, object_of) z)
    | [ |- context[morphism_of (transport ?P ?p ?z)] ]
      => simpl rewrite (@ap_transport _ P _ _ _ p (λ_, morphism_of) z)
    | [ |- context[pr1 (transport ?P ?p ?z)] ]
      => simpl rewrite (@ap_transport _ P _ _ _ p (λ_, pr1) z)
    | [ |- context[pr2 (transport ?P ?p ?z)] ]
      => simpl rewrite (@ap_transport _ P _ _ _ p (λ_, pr2) z)
    | [ |- context[dpr1 (transport ?P ?p ?z)] ]
      => simpl rewrite (@ap_transport _ P _ _ _ p (λ_, dpr1) z)
  end.

Ltac exp_laws_t' :=
  first [ exp_laws_misc_t'
        | exp_laws_simplify_types'
        | exp_laws_handle_contr'
        | exp_laws_handle_transport' ].

Ltac exp_laws_t := repeat exp_laws_t'.
