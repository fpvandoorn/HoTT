/- -*- mode: coq; mode: visual-line -*- -/
/- Equivalences -/

Require Import Overture PathGroupoids.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

/- We now give many ways to construct equivalences.  In each case, we define an instance of the typeclass [is_equiv] named [isequiv_X], followed by an element of the record type [Equiv] named [equiv_X].

   Whenever we need to assume, as a hypothesis, that a certain function is an equivalence, we do it by assuming separately a function and a proof of [is_equiv].  This is more general than assuming an inhabitant of [Equiv], since the latter has an implicit coercion and an existing instance to give us the former automatically.  Moreover, implicit generalization makes it easy to assume a function and a proof of [is_equiv]. -/

/- A word on naming: some of the lemmas about equivalences are analogues of those for paths in PathGroupoids.  We name them in an analogous way but adding [_equiv] in an appropriate place, e.g. instead of [moveR_M] we have [moveR_equiv_M].  -/

Generalizable Variables A B C f g.

/- The identity map is an equivalence. -/
definition isequiv_idmap [instance] (A : Type) : is_equiv idmap | 0 :=
  is_equiv.mk A A idmap idmap (λ_, 1) (λ_, 1) (λ_, 1).

definition equiv_idmap (A : Type) : A ≃ A := equiv.mk A A idmap _.

definition reflexive_equiv [instance] : Reflexive Equiv | 0 := equiv_idmap.

/- The composition of equivalences is an equivalence. -/
definition isequiv_compose [instance] [H : is_equiv A B f] [H : is_equiv B C g]
  : is_equiv (compose g f) | 1000 :=
     is_equiv.mk A C (compose g f)
    (compose f⁻¹ g⁻¹)
    (λc, ap g (retr f (g⁻¹ c)) ⬝ retr g c)
    (λa, ap (f⁻¹) (sect g (f a)) ⬝ sect f a)
    (λa,
      (whiskerL _ (adj g (f a))) @
      (ap_pp g _ _)⁻¹ @
      ap02 g
      ( (concat_A1p (retr f) (sect g (f a)))⁻¹ @
        (ap_compose f⁻¹ f _ @@ adj f a) @
        (ap_pp f _ _)⁻¹
      ) @
      (ap_compose f g _)⁻¹
    ).

/- An alias of [isequiv_compose], with some arguments explicit; often convenient when type class search fails. -/
definition isequiv_compose'
  {A B : Type} (f : A → B) (_ : is_equiv f)
  {C : Type} (g : B → C) (_ : is_equiv g)
  : is_equiv (g ∘ f) :=
     isequiv_compose.

definition equiv_compose {A B C : Type} (g : B → C) (f : A → B)
  [H : is_equiv B C g] [H : is_equiv A B f]
  : A ≃ C :=
     equiv.mk A C (compose g f) _.

definition equiv_compose' {A B C : Type} (g : B ≃ C) (f : A ≃ B)
  : A ≃ C :=
     equiv_compose g f.

/- The TypeClass [Transitive] has a different order of parameters than [equiv_compose].  Thus in declaring the instance we have to switch the order of arguments. -/
definition transitive_equiv [instance] : Transitive Equiv | 0 :=
  λ_ _ _ f g, equiv_compose g f.


/- Anything homotopic to an equivalence is an equivalence. -/
section is_equivHomotopic

  Context {A B : Type} (f : A → B) {g : A → B}.
  Context [H : is_equiv A B f].
  Hypothesis h : f ∼ g.

  Let sect := (λb:B, (h (f⁻¹ b))⁻¹ ⬝ retr f b).
  Let retr := (λa:A, (ap f⁻¹ (h a))⁻¹ ⬝ sect f a).

  /- We prove the triangle identity with rewrite tactics.  Since we lose control over the proof term that way, we make the result opaque with "Qed". -/
  Let adj (a : A) : sect (g a) = ap g (retr a).
  /-begin
    unfold sect, retr.
    rewrite ap_pp. apply moveR_Vp.
    rewrite concat_p_pp, <- concat_Ap, concat_pp_p, <- concat_Ap.
    rewrite ap_V; apply moveL_Vp.
    rewrite <- ap_compose; unfold compose; rewrite (concat_A1p (retr f) (h a)).
    apply whiskerR, eisadj.
  Qed.

  /- This should not be an instance; it can cause the unifier to spin forever searching for functions to be hoomotpic to. -/
  definition isequiv_homotopic : is_equiv g :=
       is_equiv.mk _ _ g (f ⁻¹) sect retr adj.

  definition equiv_homotopic : A ≃ B :=
       equiv.mk _ _ g isequiv_homotopic.

End is_equivHomotopic.


/- The inverse of an equivalence is an equivalence. -/
section EquivInverse

  Context {A B : Type} (f : A → B) {feq : is_equiv f}.
  Open Scope long_path_scope.

  definition other_adj (b : B) : sect f (f⁻¹ b) = ap f⁻¹ (retr f b).
  Proof.
    /- First we set up the mess. -/
    rewrite <- (concat_1p (sect _ _)).
    rewrite <- (concat_Vp (ap f⁻¹ (retr f (f (f⁻¹ b))))).
    rewrite (whiskerR (inverse2 (ap02 f⁻¹ (adj f (f⁻¹ b)))) _).
    refine (whiskerL _ (concat_1p (sect _ _))⁻¹ ⬝ _).
    rewrite <- (concat_Vp (sect f (f⁻¹ (f (f⁻¹ b))))).
    rewrite <- (whiskerL _ (concat_1p (sect f (f⁻¹ (f (f⁻¹ b)))))).
    rewrite <- (concat_pV (ap f⁻¹ (retr f (f (f⁻¹ b))))).
    apply moveL_M1.
    repeat rewrite concat_p_pp.
    /- Now we apply lots of naturality and cancel things. -/
    rewrite <- (concat_pp_A1 (λa, (sect f a)⁻¹) _ _).
    rewrite (ap_compose' f f⁻¹).
    rewrite <- (ap_p_pp _ _ (ap f (ap f⁻¹ (retr f (f (f⁻¹ b))))) _).
    rewrite <- (ap_compose f⁻¹ f); unfold compose.
    rewrite (concat_A1p (retr f) _).
    rewrite ap_pp, concat_p_pp.
    rewrite (concat_pp_V _ (ap f⁻¹ (retr f (f (f⁻¹ b))))).
    repeat rewrite <- ap_V; rewrite <- ap_pp.
    rewrite <- (concat_pA1 (λy, (sect f y)⁻¹) _).
    rewrite ap_compose', <- (ap_compose f⁻¹ f); unfold compose.
    rewrite <- ap_p_pp.
    rewrite (concat_A1p (retr f) _).
    rewrite concat_p_Vp.
    rewrite <- ap_compose; unfold compose.
    rewrite (concat_pA1_p (sect f) _).
    rewrite concat_pV_p; apply concat_Vp.
  Qed.

  definition isequiv_inverse [instance] : is_equiv f⁻¹ | 10000 :=
       is_equiv.mk B A f⁻¹ f (sect f) (retr f) other_adj.
End EquivInverse.

/- If the goal is [is_equiv _⁻¹], then use [isequiv_inverse]; otherwise, don't pretend worry about if the goal is an evar and we want to add a [⁻¹]. -/
Hint Extern 0 (is_equiv _⁻¹) => apply @isequiv_inverse : typeclass_instances.

/- [Equiv A B] is a symmetric relation. -/
definition equiv_inverse {A B : Type} : (A ≃ B) → (B ≃ A).
Proof.
  intro e.
  exists (e⁻¹).
  apply isequiv_inverse.
end-/

definition symmetric_equiv [instance] : Symmetric Equiv | 0 := @equiv_inverse.

/- If [g \o f] and [f] are equivalences, so is [g].  This is not an Instance because it would require Coq to guess [f]. -/
definition cancelR_isequiv {A B C} (f : A → B) {g : B → C}
  [H : is_equiv A B f] [H : is_equiv A C (g ∘ f)]
  : is_equiv g :=
     isequiv_homotopic (compose (compose g f) f⁻¹)
       (λb, ap g (retr f b)).

definition cancelR_equiv {A B C} (f : A → B) {g : B → C}
  [H : is_equiv A B f] [H : is_equiv A C (g ∘ f)]
  : B ≃ C :=
     equiv.mk B C g (cancelR_isequiv f).

/- If [g \o f] and [g] are equivalences, so is [f]. -/
definition cancelL_isequiv {A B C} (g : B → C) {f : A → B}
  [H : is_equiv B C g] [H : is_equiv A C (g ∘ f)]
  : is_equiv f :=
     isequiv_homotopic (compose g⁻¹ (compose g f))
       (λa, sect g (f a)).

definition cancelL_equiv {A B C} (g : B → C) {f : A → B}
  [H : is_equiv B C g] [H : is_equiv A C (g ∘ f)]
  : A ≃ B :=
     equiv.mk _ _ f (cancelL_isequiv g).

/- Combining these with [isequiv_compose], we see that equivalences can be transported across commutative squares. -/
definition isequiv_commsq {A B C D}
           (f : A → B) (g : C → D) (h : A → C) (k : B → D)
           (p : k ∘ f ∼ g ∘ h)
           [H : is_equiv _ _ f] [H : is_equiv _ _ h] [H : is_equiv _ _ k]
: is_equiv g.
/-begin
  refine (@cancelR_isequiv _ _ _ h g _ _).
  refine (isequiv_homotopic _ p).
end-/

definition isequiv_commsq' {A B C D}
           (f : A → B) (g : C → D) (h : A → C) (k : B → D)
           (p : g ∘ h ∼ k ∘ f)
           [H : is_equiv _ _ g] [H : is_equiv _ _ h] [H : is_equiv _ _ k]
: is_equiv f.
/-begin
  refine (@cancelL_isequiv _ _ _ k f _ _).
  refine (isequiv_homotopic _ p).
end-/

/- Transporting is an equivalence. -/
section EquivTransport

  Context {A : Type} (P : A → Type) (x y : A) (p : x = y).

  definition isequiv_transport [instance] : is_equiv (transport P p) | 0 :=
       is_equiv.mk (P x) (P y) (transport P p) (transport P p⁻¹)
    (transport_pV P p) (transport_Vp P p) (transport_pVp P p).

  definition equiv_transport : P x ≃ P y :=
       equiv.mk _ _ (transport P p) _.

End EquivTransport.

/- In all the above cases, we were able to directly construct all the structure of an equivalence.  However, as is evident, sometimes it is quite difficult to prove the adjoint law.

   The following adjointification theorem allows us to be lazy about this if we wish.  It says that if we have all the data of an (adjoint) equivalence except the triangle identity, then we can always obtain the triangle identity by modifying the datum [equiv_is_section] (or [equiv_is_retraction]).  The proof is the same as the standard categorical argument that any equivalence can be improved to an adjoint equivalence.

   As a stylistic matter, we try to avoid using adjointification in the library whenever possible, to preserve the homotopies specified by the user.  -/

section Adjointify

  Context {A B : Type} (f : A → B) (g : B → A).
  Context (isretr : Sect g f) (issect : Sect f g).

  /- This is the modified [sect]. -/
  Let issect' := λx,
    ap g (ap f (issect x)⁻¹)  ⬝  ap g (isretr (f x))  ⬝  issect x.

  Let is_adjoint' (a : A) : isretr (f a) = ap f (issect' a).
  /-begin
    unfold issect'.
    apply moveR_M1.
    repeat rewrite ap_pp, concat_p_pp; rewrite <- ap_compose; unfold compose.
    rewrite (concat_pA1 (λb, (isretr b)⁻¹) (ap f (issect a)⁻¹)).
    repeat rewrite concat_pp_p; rewrite ap_V; apply moveL_Vp; rewrite concat_p1.
    rewrite concat_p_pp, <- ap_compose; unfold compose.
    rewrite (concat_pA1 (λb, (isretr b)⁻¹) (isretr (f a))).
    rewrite concat_pV, concat_1p; reflexivity.
  Qed.

  /- We don't make this a typeclass instance, because we want to control when we are applying it. -/
  definition isequiv_adjointify : is_equiv f :=
       is_equiv.mk A B f g isretr issect' is_adjoint'.

  definition equiv_adjointify : A ≃ B :=
       equiv.mk A B f isequiv_adjointify.

End Adjointify.

/- Several lemmas useful for rewriting. -/
definition moveR_equiv_M [H : is_equiv A B f] (x : A) (y : B) (p : x = f⁻¹ y)
  : (f x = y) :=
     ap f p ⬝ retr f y.

definition moveL_equiv_M [H : is_equiv A B f] (x : A) (y : B) (p : f⁻¹ y = x)
  : (y = f x) :=
     (retr f y)⁻¹ ⬝ ap f p.

definition moveR_equiv_V [H : is_equiv A B f] (x : B) (y : A) (p : x = f y)
  : (f⁻¹ x = y) :=
     ap (f⁻¹) p ⬝ sect f y.

definition moveL_equiv_V [H : is_equiv A B f] (x : B) (y : A) (p : f y = x)
  : (y = f⁻¹ x) :=
     (sect f y)⁻¹ ⬝ ap (f⁻¹) p.

/- Equivalence preserves contractibility (which of course is trivial under univalence). -/
definition contr_equiv A {B} (f : A → B) [H : is_equiv A B f] [H : is_contr A]
  : is_contr B.
Proof.
  exists (f (center A)).
  intro y.
  apply moveR_equiv_M.
  apply contr.
Qed.

definition contr_equiv' A {B} `(f : A ≃ B) [H : is_contr A]
  : is_contr B :=
     contr_equiv A f.

/- Any two contractible types are equivalent. -/
/- TODO: the name [equiv_contr_contr] is not great in conjunction with the existing, unrelated [contr_equiv_contr].  Consider alternative names? -/
definition equiv_contr_contr {A B : Type} [H : is_contr A] [H : is_contr B]
  : (A ≃ B).
Proof.
  apply equiv_adjointify with (λ_, center B) (λ_, center A);
  intros ?; apply contr.
end-/

/- Assuming function extensionality, composing with an equivalence is itself an equivalence -/

definition isequiv_precompose [instance] [H : funext] {A B C : Type}
  (f : A → B) [H : is_equiv A B f]
  : is_equiv (λg, @compose A B C g f) | 1000 :=
     isequiv_adjointify (λg, @compose A B C g f)
    (λh, @compose B A C h f⁻¹)
    (λh, path_pi _ _ (λx, ap h (sect f x)))
    (λg, path_pi _ _ (λy, ap g (retr f y))).

definition equiv_precompose [H : funext] {A B C : Type}
  (f : A → B) [H : is_equiv A B f]
  : (B → C) ≃ (A → C) :=
     equiv.mk _ _ (λg, @compose A B C g f) _.

definition equiv_precompose' [H : funext] {A B C : Type} (f : A ≃ B)
  : (B → C) ≃ (A → C) :=
     equiv.mk _ _ (λg, @compose A B C g f) _.

definition isequiv_postcompose [instance] [H : funext] {A B C : Type}
  (f : B → C) [H : is_equiv B C f]
  : is_equiv (λg, @compose A B C f g) | 1000 :=
     isequiv_adjointify (λg, @compose A B C f g)
    (λh, @compose A C B f⁻¹ h)
    (λh, path_pi _ _ (λx, retr f (h x)))
    (λg, path_pi _ _ (λy, sect f (g y))).

definition equiv_postcompose [H : funext] {A B C : Type}
  (f : B → C) [H : is_equiv B C f]
  : (A → B) ≃ (A → C) :=
     equiv.mk _ _ (λg, @compose A B C f g) _.

definition equiv_postcompose' [H : funext] {A B C : Type} (f : B ≃ C)
  : (A → B) ≃ (A → C) :=
     equiv.mk _ _ (λg, @compose A B C f g) _.

/- Conversely, if pre- or post-composing with a function is always an equivalence, then that function is also an equivalence.  It's convenient to know that we only need to assume the equivalence when the other type is the domain or the codomain. -/

definition isequiv_isequiv_precompose {A B : Type} (f : A → B)
  (precomp := (λ(C : Type) (h : B → C), h ∘ f))
  (Aeq : is_equiv (precomp A)) (Beq : is_equiv (precomp B))
  : is_equiv f.
/-begin
  assert (H : Π(C D : Type)
                     (Ceq : is_equiv (precomp C)) (Deq : is_equiv (precomp D))
                     (k : C → D) (h : A → C),
                k ∘ (precomp C)⁻¹ h = (precomp D)⁻¹ (k ∘ h)).
  { intros C D ? ? k h.
    transitivity ((precomp D)⁻¹ (k ∘ (precomp C ((precomp C)⁻¹ h)))).
    - transitivity ((precomp D)⁻¹ (precomp D (k ∘ ((precomp C)⁻¹ h)))).
      + rewrite (sect (precomp D) _); reflexivity.
      + reflexivity.
    - rewrite (retr (precomp C) h); reflexivity. }
  refine (isequiv_adjointify f ((precomp A)⁻¹ idmap) _ _).
  - intros x.
    change ((f ∘ (precomp A)⁻¹ idmap) x = idmap x).
    apply ap10.
    rewrite (H A B Aeq Beq).
    change ((precomp B)⁻¹ (precomp B idmap) = idmap).
    apply eissect.
  - intros x.
    change ((precomp A ((precomp A)⁻¹ idmap)) x = idmap x).
    apply ap10, eisretr.
Qed.

(*
definition isequiv_isequiv_postcompose {A B : Type} (f : A → B)
  (postcomp := (λ(C : Type) (h : C → A), f ∘ h))
  (feq : ΠC:Type, is_equiv (postcomp C))
  : is_equiv f.
/- TODO -/
*)

/- If [f] is an equivalence, then so is [ap f].  We are lazy and use [adjointify]. -/
definition isequiv_ap [instance] [H : is_equiv A B f] (x y : A)
  : is_equiv (@ap A B f x y) | 1000 :=
     isequiv_adjointify (ap f)
  (λq, (sect f x)⁻¹  ⬝  ap f⁻¹ q  ⬝  sect f y)
  (λq,
    ap_pp f _ _
    ⬝ whiskerR (ap_pp f _ _) _
    ⬝ ((ap_V f _ ⬝ inverse2 (adj f _)⁻¹)
      @@ (ap_compose f⁻¹ f _)⁻¹
      @@ (adj f _)⁻¹)
    ⬝ concat_pA1_p (retr f) _ _
    ⬝ whiskerR (concat_Vp _) _
    ⬝ concat_1p _)
  (λp,
    whiskerR (whiskerL _ (ap_compose f f⁻¹ _)⁻¹) _
    ⬝ concat_pA1_p (sect f) _ _
    ⬝ whiskerR (concat_Vp _) _
    ⬝ concat_1p _).

/- The function [equiv_ind] says that given an equivalence [f : A ≃ B], and a hypothesis from [B], one may always assume that the hypothesis is in the image of [e].

In fibrational terms, if we have a fibration over [B] which has a section once pulled back along an equivalence [f : A ≃ B], then it has a section over all of [B].  -/

definition equiv_ind [H : is_equiv A B f] (P : B → Type)
  : (Πx:A, P (f x)) → Πy:B, P y :=
     λg y, transport P (retr f y) (g (f⁻¹ y)).

Arguments equiv_ind {A B} f {_} P _ _.

definition equiv_ind_comp [H : is_equiv A B f] (P : B → Type)
  (df : Πx:A, P (f x)) (x : A)
  : equiv_ind f P df (f x) = df x.
Proof.
  unfold equiv_ind.
  rewrite eisadj.
  rewrite <- transport_compose.
  exact (apD df (sect f x)).
end-/

/- Using [equiv_ind], we define a handy little tactic which introduces a variable and simultaneously substitutes it along an equivalence. -/

Ltac equiv_intro E x :=
  match goal with
    | |- Πy, @?Q y =>
      refine (equiv_ind E Q _); intros x
  end.

/- [equiv_composeR'], a flipped version of [equiv_compose'], is (like [concatR]) most often useful partially applied, to give the “first half” of an equivalence one is constructing and leave the rest as a subgoal. One could similarly define [equiv_composeR] as a flip of [equiv_compose], but it doesn’t seem so useful since it doesn’t leave the remaining equivalence as a subgoal. -/
definition equiv_composeR' {A B C} (f : A ≃ B) (g : B ≃ C) :=
     equiv_compose' g f.

/- Shouldn't this become transitivity mid ? -/
Ltac equiv_via mid :=
  apply @equiv_composeR' with (B := mid).

/- It's often convenient when constructing a chain of equivalences to use [equiv_compose'], etc.  But when we treat an [Equiv] object constructed in that way as a function, via the coercion [equiv_fun], Coq sometimes needs a little help to realize that the result is the same as ordinary composition.  This tactic provides that help. -/
Ltac ev_equiv :=
  repeat match goal with
           | [ |- context[equiv_λ(equiv_compose' ?g ?f) ?a] ],
             change ((equiv_compose' g f) a) with (g (f a))
           | [ |- context[equiv_λ(equiv_compose ?g ?f) ?a] ],
             change ((equiv_compose g f) a) with (g (f a))
           | [ |- context[equiv_λ(equiv_inverse ?f) ?a] ],
             change ((equiv_inverse f) a) with (f⁻¹ a)
         end.
