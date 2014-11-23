/- -*- mode: coq; mode: visual-line -*- -/
/- Theorems about Non-dependent function types -/

Require Import HoTT.Basics.
Require Import Types.Paths Types.Forall.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables A B C D f g n.

section AssumeFunext
Context [H : Funext].

/- Paths -/

/- As for dependent functions, paths [p : f ≈ g] in a function type [A → B] are equivalent to functions taking values in path types, [H : Πx:A, f x ≈ g x], or concisely [H : f == g].  These are all given in the [Overture], but we can give them separate names for clarity in the non-dependent case. -/

definition path_arrow {A B : Type} (f g : A → B)
  : (f == g) → (f ≈ g) :=
     path_Πf g.

/- There are a number of combinations of dependent and non-dependent for [apD10_path_forall]; we list all of the combinations as helpful lemmas for rewriting. -/
definition ap10_path_arrow {A B : Type} (f g : A → B) (h : f == g)
  : ap10 (path_arrow f g h) == h :=
     apD10_path_Πf g h.

definition apD10_path_arrow {A B : Type} (f g : A → B) (h : f == g)
  : apD10 (path_arrow f g h) == h :=
     apD10_path_Πf g h.

definition ap10_path_Π{A B : Type} (f g : A → B) (h : f == g)
  : ap10 (path_Πf g h) == h :=
     apD10_path_Πf g h.

definition eta_path_arrow {A B : Type} (f g : A → B) (p : f ≈ g)
  : path_arrow f g (ap10 p) ≈ p :=
     eta_path_Πf g p.

definition path_arrow_1 {A B : Type} (f : A → B)
  : (path_arrow f f (λx, 1)) ≈ 1 :=
     eta_path_arrow f f 1.

definition equiv_ap10 [H : Funext] {A B : Type} f g
: (f ≈ g) ≃ (f == g) :=
     Equiv.mk _ _ (@ap10 A B f g) _.

definition isequiv_path_arrow [instance] {A B : Type} (f g : A → B)
  : IsEquiv (path_arrow f g) | 0 :=
     isequiv_path_Πf g.

definition equiv_path_arrow {A B : Type} (f g : A → B)
  : (f == g) ≃ (f ≈ g) :=
     equiv_path_Πf g.

/- Transport -/

/- Transporting in non-dependent function types is somewhat simpler than in dependent ones. -/

definition transport_arrow {A : Type} {B C : A → Type}
  {x1 x2 : A} (p : x1 ≈ x2) (f : B x1 → C x1) (y : B x2)
  : (transport (λx, B x → C x) p f) y  ≈  p ▹ (f (p⁻¹ ▹ y)).
/-begin
  destruct p; simpl; auto.
end-/

definition transport_arrow_toconst {A : Type} {B : A → Type} {C : Type}
  {x1 x2 : A} (p : x1 ≈ x2) (f : B x1 → C) (y : B x2)
  : (transport (λx, B x → C) p f) y  ≈  f (p⁻¹ ▹ y).
/-begin
  destruct p; simpl; auto.
end-/

definition transport_arrow_fromconst {A B : Type} {C : A → Type}
  {x1 x2 : A} (p : x1 ≈ x2) (f : B → C x1) (y : B)
  : (transport (λx, B → C x) p f) y  ≈  p ▹ (f y).
/-begin
  destruct p; simpl; auto.
end-/

/- And some naturality and coherence for these laws. -/

definition ap_transport_arrow_toconst {A : Type} {B : A → Type} {C : Type}
  {x1 x2 : A} (p : x1 ≈ x2) (f : B x1 → C) {y1 y2 : B x2} (q : y1 ≈ y2)
  : ap (transport (λx, B x → C) p f) q
    ⬝ transport_arrow_toconst p f y2
    ≈ transport_arrow_toconst p f y1
    ⬝ ap (λy, f (p⁻¹ ▹ y)) q.
/-begin
  destruct p, q; reflexivity.
end-/


/- Dependent paths -/

/- Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 ≈ y2] in [P x2].  However, when [P] is a function space, these dependent paths have a more convenient description: rather than transporting the argument of [y1] forwards and backwards, we transport only forwards but on both sides of the equation, yielding a "naturality square". -/

definition dpath_arrow
  {A:Type} (B C : A → Type) {x1 x2:A} (p:x1=x2)
  (f : B x1 → C x1) (g : B x2 → C x2)
  : (Π(y1:B x1), transport C p (f y1) ≈ g (transport B p y1))
  ≃
  (transport (λx, B x → C x) p f ≈ g).
/-begin
  destruct p.
  apply equiv_path_arrow.
end-/

definition ap10_dpath_arrow
  {A:Type} (B C : A → Type) {x1 x2:A} (p:x1=x2)
  (f : B x1 → C x1) (g : B x2 → C x2)
  (h : Π(y1:B x1), transport C p (f y1) ≈ g (transport B p y1))
  (u : B x1)
  : ap10 (dpath_arrow B C p f g h) (p ▹ u)
  ≈ transport_arrow p f (p ▹ u)
  ⬝ ap (λx, p ▹ (f x)) (transport_Vp B p u)
  ⬝ h u.
/-begin
  destruct p; simpl; unfold ap10.
  exact (apD10_path_Πf g h u ⬝ (concat_1p _)⁻¹).
end-/

/- Maps on paths -/

/- The action of maps given by application. -/
definition ap_apply_l {A B : Type} {x y : A → B} (p : x ≈ y) (z : A) :
  ap (λf, f z) p ≈ ap10 p z :=
   1.

definition ap_apply_Fl {A B C : Type} {x y : A} (p : x ≈ y) (M : A → B → C) (z : B) :
  ap (λa, (M a) z) p ≈ ap10 (ap M p) z :=
   match p with 1 => 1 end.

definition ap_apply_Fr {A B C : Type} {x y : A} (p : x ≈ y) (z : B → C) (N : A → B) :
  ap (λa, z (N a)) p ≈ ap01 z (ap N p) :=
   (ap_compose N _ _).

definition ap_apply_FlFr {A B C : Type} {x y : A} (p : x ≈ y) (M : A → B → C) (N : A → B) :
  ap (λa, (M a) (N a)) p ≈ ap11 (ap M p) (ap N p) :=
   match p with 1 => 1 end.

/- The action of maps given by lambda. -/
definition ap_lambda {A B C : Type} {x y : A} (p : x ≈ y) (M : A → B → C) :
  ap (λa b, M a b) p =
  path_arrow _ _ (λb, ap (λa, M a b) p).
/-begin
  destruct p;
  symmetry;
  simpl; apply path_arrow_1.
end-/

/- Functorial action -/

definition functor_arrow `(f : B → A) `(g : C → D)
  : (A → C) → (B → D) :=
     @functor_ΠA (λ_, C) B (λ_, D) f (λ_, g).

definition ap_functor_arrow `(f : B → A) `(g : C → D)
  (h h' : A → C) (p : h == h')
  : ap (functor_arrow f g) (path_arrow _ _ p)
  ≈ path_arrow _ _ (λb, ap g (p (f b))) :=
     @ap_functor_Π_ A (λ_, C) B (λ_, D)
  f (λ_, g) h h' p.

/- Truncatedness: functions into an n-type is an n-type -/

definition contr_arrow [instance] {A B : Type} [H : is_contr B]
  : is_contr (A → B) | 100 :=
   contr_forall.

definition trunc_arrow [instance] {A B : Type} [H : is_trunc n B]
  : is_trunc n (A → B) | 100 :=
   trunc_forall.

/- Equivalences -/

definition isequiv_functor_arrow [instance] [H : IsEquiv B A f] [H : IsEquiv C D g]
  : IsEquiv (functor_arrow f g) | 1000 :=
     @isequiv_functor_Π_ A (λ_, C) B (λ_, D)
     _ _ _ _.

definition equiv_functor_arrow [H : IsEquiv B A f] [H : IsEquiv C D g]
  : (A → C) ≃ (B → D) :=
     @equiv_functor_Π_ A (λ_, C) B (λ_, D)
  f _ (λ_, g) _.

definition equiv_functor_arrow' `(f : B ≃ A) `(g : C ≃ D)
  : (A → C) ≃ (B → D) :=
     @equiv_functor_forall' _ A (λ_, C) B (λ_, D)
  f (λ_, g).

/- What remains is really identical to that in [Forall].  -/

End AssumeFunext.
