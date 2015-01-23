  /- -*- mode: coq; mode: visual-line -*- -/
  /- Theorems about dependent products -/

  Require Import HoTT.Basics.
  Require Import Types.Paths.

  Local Open Scope path_scope.
  Local Open Scope equiv_scope.

  Generalizable Variables A B f g e n.

  section AssumeFunext
  Context [H : Funext].

  /- Paths -/

  /- Paths [p : f = g] in a function type [Πx:X, P x] are equivalent to functions taking values in path types, [H : Πx:X, f x = g x], or concisely, [H : f == g].

  This equivalence, however, is just the combination of [apD10] and function extensionality [funext], and as such, [path_forall], et seq. are given in the [Overture]:  -/

  /- Now we show how these things compute. -/

  definition apD10_path_Π`{P : A → Type}
    (f g : Πx, P x) (h : f == g)
    : apD10 (path_Π_ _ h) == h :=
       apD10 (eisretr apD10 h).

  definition eta_path_Π`{P : A → Type}
    (f g : Πx, P x) (p : f = g)
    : path_Π_ _ (apD10 p) = p :=
       eissect apD10 p.

  definition path_forall_1 {P : A → Type} (f : Πx, P x)
    : (path_Πf f (λx, 1)) = 1 :=
       eta_path_Πf f 1.

  /- The identification of the path space of a dependent function space, up to equivalence, is of course just funext. -/

  definition equiv_apD10 [H : funext] {A : Type} (P : A → Type) f g
  : (f = g) ≃ (f ∼ g) :=
       equiv.mk _ _ (@apD10 A P f g) _.

  definition isequiv_path_pi [instance] {P : A → Type} (f g : Πx, P x)
    : is_equiv (path_pi f g) | 0 :=
       @isequiv_inverse _ _ (@apD10 A P f g) _.

  definition equiv_path_pi `{P : A → Type} (f g : Πx, P x)
    : (f ∼ g)  ≃  (f = g) :=
       equiv.mk _ _ (path_pi f g) _.

  /- Transport -/

  /- The concrete description of transport in sigmas and pis is rather trickier than in the other types. In particular, these cannot be described just in terms of transport in simpler types; they require the full Id-elim rule by way of "dependent transport" [transportD].

    In particular this indicates why "transport" alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory). A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? -/
  definition transport_forall
    {A : Type} {P : A → Type} {C : Πx, P x → Type}
    {x1 x2 : A} (p : x1 = x2) (f : Πy : P x1, C x1 y)
    : (transport (λx, Πy : P x, C x y) p f)
      ∼ (λy,
         transport (C x2) (transport_pV _ _ _) (transportD _ _ p _ (f (p⁻¹ ▹ y)))) :=
       match p with refl => λ_, 1 end.

  /- A special case of [transport_forall] where the type [P] does not depend on [A],
      and so it is just a fixed type [B]. -/
  definition transport_pi_constant
    {A B : Type} {C : A → B → Type}
    {x1 x2 : A} (p : x1 = x2) (f : Πy : B, C x1 y)
    : (transport (λx, Πy : B, C x y) p f)
      ∼ (λy, transport (λx, C x y) p (f y)) :=
       match p with refl => λ_, 1 end.

  /- Maps on paths -/

  /- The action of maps given by lambda. -/
  definition ap_lambdaD {A B : Type} {C : B → Type} {x y : A} (p : x = y) (M : Πa b, C b) :
    ap (λa b, M a b) p =
    path_pi _ _ (λb, ap (λa, M a b) p).
  /-begin
    destruct p;
    apply symmetry.
    simpl; apply path_pi_1.
  end-/

  /- Dependent paths -/

  /- Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 = y2] in [P x2].  However, when [P] is a function space, these dependent paths have a more convenient description: rather than transporting the argument of [y1] forwards and backwards, we transport only forwards but on both sides of the equation, yielding a "naturality square". -/

  definition dpath_pi [H : funext]
    {A:Type} (B:A → Type) (C:Πa, B a → Type) (x1 x2:A) (p:x1=x2)
    (f:Πy1:B x1, C x1 y1) (g:Π(y2:B x2), C x2 y2)
    : (Π(y1:B x1), transportD B C p y1 (f y1) = g (transport B p y1))
    ≃
    (transport (λx, Πy:B x, C x y) p f = g).
  /-begin
    destruct p.
    apply equiv_path_forall.
  end-/

  /- Functorial action -/

  /- The functoriality of [forall] is slightly subtle: it is contravariant in the domain type and covariant in the codomain, but the codomain is dependent on the domain. -/
  definition functor_pi `{P : A → Type} {Q : B → Type}
      (f0 : B → A) (f1 : Πb:B, P (f0 b) → Q b)
    : (Πa:A, P a) → (Πb:B, Q b) :=
       (λg b, f1 _ (g (f0 b))).

  definition ap_functor_pi `{P : A → Type} {Q : B → Type}
      (f0 : B → A) (f1 : Πb:B, P (f0 b) → Q b)
      (g g' : Πa:A, P a) (h : g ∼ g')
    : ap (functor_pi f0 f1) (path_pi _ _ h)
      = path_pi _ _ (λb:B, (ap (f1 b) (h (f0 b)))).
  /-begin
    revert h.  equiv_intro (@apD10 A P g g') h.
    destruct h.  simpl.
    transitivity (refl (functor_pi f0 f1 g)).
    - exact (ap (ap (functor_pi f0 f1)) (path_pi_1 g)).
    - apply symmetry.  apply path_pi_1.
  end-/

  /- Equivalences -/

  definition isequiv_functor_pi [instance] {P : A → Type} {Q : B → Type}
    [H : is_equiv B A f] [H : Πb, @is_equiv (P (f b)) (Q b) (g b)]
    : is_equiv (functor_pi f g) | 1000.
  /-begin
    refine (isequiv_adjointify (functor_pi f g)
      (functor_pi (f⁻¹)
        (λ(x:A) (y:Q (f⁻¹ x)), retr f x ▹ (g (f⁻¹ x))⁻¹ y
        )) _ _);
    intros h.
    - abstract (
          apply path_forall; intros b; unfold functor_forall;
          rewrite adj;
          rewrite <- transport_compose;
          rewrite ap_transport;
          rewrite retr;
          apply apD
        ).
    - abstract (
          apply path_forall; intros a; unfold functor_forall;
          rewrite sect;
          apply apD
        ).
  end-/

  definition equiv_functor_pi `{P : A → Type} {Q : B → Type}
    (f : B → A) [H : is_equiv B A f]
    (g : Πb, P (f b) → Q b)
    [H : Πb, @is_equiv (P (f b)) (Q b) (g b)]
    : (Πa, P a) ≃ (Πb, Q b) :=
       equiv.mk _ _ (functor_pi f g) _.

  definition equiv_functor_forall' {P : A → Type} {Q : B → Type}
    (f : B ≃ A) (g : Πb, P (f b) ≃ Q b)
    : (Πa, P a) ≃ (Πb, Q b) :=
       equiv_functor_pi f g.

  definition equiv_functor_pi_id {P : A → Type} {Q : A → Type}
    (g : Πa, P a ≃ Q a)
    : (Πa, P a) ≃ (Πa, Q a) :=
       equiv_functor_pi (equiv_idmap A) g.

  /- Truncatedness: any dependent product of n-types is an n-type -/

  definition contr_pi [instance] {P : A → Type} [H : Πa, is_contr (P a)]
    : is_contr (Πa, P a) | 100.
  /-begin
    exists (λa, center (P a)).
    intro f.  apply path_forall.  intro a.  apply contr.
  end-/

  definition trunc_pi [instance] {P : A → Type} [H : Πa, is_trunc n (P a)]
    : is_trunc n (Πa, P a) | 100.
  /-begin
    generalize dependent P.
    simple_induction n n IH; simpl; intros P ?.
    /- case [n = -2], i.e. contractibility -/
    - exact _.
    /- case n = n'.+1 -/
    - intros f g; apply (trunc_equiv _ (apD10 ⁻¹)).
  end-/

  /- apply symmetry.of curried arguments -/

  /- Using the standard Haskell name for this, as it’s a handy utility function.

  Note: not sure if [P] will usually be deducible, or whether it would be better explicit. -/
  definition flip {P : A → B → Type}
    : (Πa b, P a b) → (Πb a, P a b) :=
       λf b a, f a b.

  definition isequiv_flip [instance] {P : A → B → Type}
    : is_equiv (@flip _ _ P) | 0.
  /-begin
    set (flip_P := @flip _ _ P).
    set (flip_P_inv := @flip _ _ (flip P)).
    set (flip_P_is_sect := (λf, 1) : Sect flip_P flip_P_inv).
    set (flip_P_is_retr := (λg, 1) : Sect flip_P_inv flip_P).
    exists flip_P_inv flip_P_is_retr flip_P_is_sect.
    intro g.  exact 1.
  end-/

  definition equiv_flip `(P : A → B → Type)
    : (Πa b, P a b) ≃ (Πb a, P a b) :=
       equiv.mk _ _ (@flip _ _ P) _.

  End Assumefunext.