/- -*- mode: coq; mode: visual-line -*- -/
/- Theorems about Sigma-types (dependent sums) -/

Require Import HoTT.Basics.
Require Import Types.Arrow Types.Prod Types.Paths Types.unit.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables X A B C f g n.

Scheme sig_ind := Induction for sig Sort Type.
Scheme sig_rec := Minimality for sig Sort Type.

/- In homotopy type theory, We think of elements of [Type] as spaces, homotopy types, or weak omega-groupoids. A type family [P : A → Type] corresponds to a fibration whose base is [A] and whose fiber over [x] is [P x].

From such a [P] we can build a total space over the base space [A] so that the fiber over [x : A] is [P x]. This is just Coq's dependent sum construction, written as [sigT P] or [Σx : A, P x]. The elements of [Σx : A, P x] are pairs, written [existT P x y] in Coq, where [x : A] and [y : P x].  In [Common.v] we defined the notation [⟨x,y⟩] to mean [existT _ x y].

The base and fiber components of a point in the total space are extracted with the two projections [dpr1] and [dpr2]. -/

/- Unpacking -/

/- Sometimes we would like to prove [Q u] where [u : Σx : A, P x] by writing [u] as a pair [⟨dpr1 u , dpr2 u⟩]. This is accomplished by [sigT_unpack]. We want tight control over the proof, so we just write it down even though is looks a bit scary. -/

definition unpack_sigma {P : A → Type} (Q : sigT P → Type) (u : sigT P)
: Q ⟨u.1, u.2⟩ → Q u :=
     idmap.

Arguments unpack_sigma / .

/- Eta conversion -/

definition eta_sigma {P : A → Type} (u : sigT P)
  : ⟨u.1, u.2⟩ = u :=
     1.

Arguments eta_sigma / .

definition eta2_sigma {P : Π(a : A) (b : B a), Type}
           (u : sigT (λa, sigT (P a)))
  : (u.1; ⟨u.2.1, u.2.2⟩) = u :=
     1.

Arguments eta2_sigma / .

definition eta3_sigma {P : Π(a : A) (b : B a) (c : C a b), Type}
           (u : sigT (λa, sigT (λb, sigT (P a b))))
  : (u.1; (u.2.1; ⟨u.2.2.1, u.2.2.2⟩)) = u :=
     1.

Arguments eta3_sigma / .

/- Paths -/

/- A path in a total space is commonly shown component wise. Because we use this over and over, we write down the proofs by hand to make sure they are what we think they should be. -/

/- With this version of the function, we often have to give [u] and [v] explicitly, so we make them explicit arguments. -/
definition path_sigma_uncurried {A : Type} (P : A → Type) (u v : sigT P)
           (pq : Σp : u.1 = v.1,  p ▹ u.2 = v.2)
: u = v :=
     match pq.2 in (_ = v2) return u = ⟨v.1, v2⟩ with
       | 1 => match pq.1 as p in (_ = v1) return u = ⟨v1, p ▹ u.2⟩ with
                | 1 => 1
              end
     end.

/- This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. -/
definition path_sigma {A : Type} (P : A → Type) (u v : sigT P)
           (p : u.1 = v.1) (q : p ▹ u.2 = v.2)
: u = v :=
     path_sigma_uncurried P u v ⟨p,q⟩.

/- A variant of [Forall.dpath_forall] from which uses dependent sums to package things. It cannot go into [Forall] because [Sigma] depends on [Forall]. -/

definition dpath_forall'
           {A : Type } (P : A → Type) (Q: sigT P → Type) {x y : A} (h : x = y)
           (f : Πp, Q ⟨x , p⟩) (g : Πp, Q ⟨y , p⟩)
:
  (Πp, transport Q (path_sigma P ⟨x , p⟩ ⟨y, _⟩ h 1) (f p) = g (h ▹ p))
    ≃
    (Πp, transportD P (λx, λp, Q ⟨ x , p⟩) h p (f p) = g (transport P h p)).
/-begin
  destruct h.
  apply equiv_idmap.
end-/


/- This version produces only paths between pairs, as opposed to paths between arbitrary inhabitants of dependent sum types.  But it has the advantage that the components of those pairs can more often be inferred, so we make them implicit arguments. -/
definition path_sigma' {A : Type} (P : A → Type) {x x' : A} {y : P x} {y' : P x'}
           (p : x = x') (q : p ▹ y = y')
: ⟨x,y⟩ = ⟨x',y'⟩ :=
     path_sigma P ⟨x,y⟩ ⟨x',y'⟩ p q.


/- Projections of paths from a total space. -/

definition pr1_path {P : A → Type} {u v : sigT P} (p : u = v)
: u.1 = v.1 :=
    
    ap dpr1 p.
/- match p with refl => 1 end. -/

Notation "p ..1" := (pr1_path p) (at level 3) : fibration_scope.

definition pr2_path {P : A → Type} {u v : sigT P} (p : u = v)
: p..1 ▹ u.2 = v.2 :=
     (transport_compose P dpr1 p u.2)⁻¹
     ⬝ (@apD Σx:A, P x _ dpr2 _ _ p).

Notation "p ..2" := (pr2_path p) (at level 3) : fibration_scope.

/- Now we show how these things compute. -/

definition pr1_path_sigma_uncurried {P : A → Type} {u v : sigT P}
           (pq : Σp : u.1 = v.1, p ▹ u.2 = v.2 )
: (path_sigma_uncurried _ _ _ pq)..1 = pq.1.
/-begin
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
end-/

definition pr2_path_sigma_uncurried {P : A → Type} {u v : sigT P}
           (pq : Σp : u.1 = v.1, p ▹ u.2 = v.2 )
: (path_sigma_uncurried _ _ _ pq)..2
  = ap (λs, transport P s u.2) (pr1_path_sigma_uncurried pq) ⬝ pq.2.
/-begin
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
end-/

definition eta_path_sigma_uncurried {P : A → Type} {u v : sigT P}
           (p : u = v)
: path_sigma_uncurried _ _ _ ⟨p..1, p..2⟩ = p.
/-begin
  destruct p. reflexivity.
end-/

definition transport_pr1_path_sigma_uncurried
      {P : A → Type} {u v : sigT P}
      (pq : Σp : u.1 = v.1, transport P p u.2 = v.2 )
      Q
: transport (λx, Q x.1) (@path_sigma_uncurried A P u v pq)
  = transport _ pq.1.
/-begin
  destruct pq as [p q], u, v; simpl in *.
  destruct p, q; simpl in *.
  reflexivity.
end-/

definition pr1_path_sigma {P : A → Type} {u v : sigT P}
           (p : u.1 = v.1) (q : p ▹ u.2 = v.2)
: (path_sigma _ _ _ p q)..1 = p :=
     pr1_path_sigma_uncurried ⟨p, q⟩.

definition pr2_path_sigma {P : A → Type} {u v : sigT P}
           (p : u.1 = v.1) (q : p ▹ u.2 = v.2)
: (path_sigma _ _ _ p q)..2
  = ap (λs, transport P s u.2) (pr1_path_sigma p q) ⬝ q :=
     pr2_path_sigma_uncurried ⟨p, q⟩.

definition eta_path_sigma {P : A → Type} {u v : sigT P} (p : u = v)
: path_sigma _ _ _ (p..1) (p..2) = p :=
     eta_path_sigma_uncurried p.

definition transport_pr1_path_sigma
           {P : A → Type} {u v : sigT P}
           (p : u.1 = v.1) (q : p ▹ u.2 = v.2)
           Q
: transport (λx, Q x.1) (@path_sigma A P u v p q)
  = transport _ p :=
     transport_pr1_path_sigma_uncurried ⟨p, q⟩ Q.

/- This lets us identify the path space of a sigma-type, up to equivalence. -/

definition isequiv_path_sigma [instance] {P : A → Type} {u v : sigT P}
: is_equiv (path_sigma_uncurried P u v) | 0 :=
     is_equiv.mk
       _ _
       _ (λr, ⟨r..1, r..2⟩)
       eta_path_sigma
       _ _.
/-begin
  all: destruct u, v; intros [p q].
  all: simpl in *.
  all: destruct q, p; simpl in *.
  all: reflexivity.
end-/

definition equiv_path_sigma `(P : A → Type) (u v : sigT P)
: Σp : u.1 = v.1,  p ▹ u.2 = v.2 ≃ (u = v) :=
     equiv.mk _ _ (path_sigma_uncurried P u v) _.

/- This identification respects path concatenation. -/

definition path_sigma_pp_pp {A : Type} (P : A → Type) {u v w : sigT P}
           (p1 : u.1 = v.1) (q1 : p1 ▹ u.2 = v.2)
           (p2 : v.1 = w.1) (q2 : p2 ▹ v.2 = w.2)
: path_sigma P u w (p1 ⬝ p2)
             (transport_pp P p1 p2 u.2 ⬝ ap (transport P p2) q1 ⬝ q2)
  = path_sigma P u v p1 q1 ⬝ path_sigma P v w p2 q2.
/-begin
  destruct u, v, w. simpl in *.
  destruct p1, p2, q1, q2.
  reflexivity.
end-/

definition path_sigma_pp_pp' {A : Type} (P : A → Type)
           {u1 v1 w1 : A} {u2 : P u1} {v2 : P v1} {w2 : P w1}
           (p1 : u1 = v1) (q1 : p1 ▹ u2 = v2)
           (p2 : v1 = w1) (q2 : p2 ▹ v2 = w2)
: path_sigma' P (p1 ⬝ p2)
              (transport_pp P p1 p2 u2 ⬝ ap (transport P p2) q1 ⬝ q2)
  = path_sigma' P p1 q1 ⬝ path_sigma' P p2 q2 :=
     @path_sigma_pp_pp A P ⟨u1,u2⟩ ⟨v1,v2⟩ ⟨w1,w2⟩ p1 q1 p2 q2.

definition path_sigma_p1_1p' {A : Type} (P : A → Type)
           {u1 v1 : A} {u2 : P u1} {v2 : P v1}
           (p : u1 = v1) (q : p ▹ u2 = v2)
: path_sigma' P p q
  = path_sigma' P p 1 ⬝ path_sigma' P 1 q.
/-begin
  destruct p, q.
  reflexivity.
end-/

/- [pr1_path] also commutes with the groupoid structure. -/

definition pr1_path_1 {A : Type} {P : A → Type} (u : sigT P)
: (refl u) ..1 = refl (u .1) :=
     1.

definition pr1_path_pp {A : Type} {P : A → Type} {u v w : sigT P}
           (p : u = v) (q : v = w)
: (p ⬝ q) ..1 = (p ..1) ⬝ (q ..1) :=
     ap_pp _ _ _.

definition pr1_path_V {A : Type} {P : A → Type} {u v : sigT P} (p : u = v)
: p⁻¹ ..1 = (p ..1)⁻¹ :=
     ap_V _ _.

/- Applying [existT] to one argument is the same as [path_sigma] with reflexivity in the first place. -/

definition ap_existT {A : Type} (P : A → Type) (x : A) (y1 y2 : P x)
           (q : y1 = y2)
: ap (existT P x) q = path_sigma' P 1 q.
/-begin
  destruct q; reflexivity.
end-/

/- Dependent transport is the same as transport along a [path_sigma]. -/

definition transportD_is_transport
           {A:Type} (B:A->Type) (C:sigT B → Type)
           (x1 x2:A) (p:x1=x2) (y:B x1) (z:C ⟨x1,y⟩)
: transportD B (λa b, C ⟨a,b⟩) p y z
  = transport C (path_sigma' B p 1) z.
/-begin
  destruct p. reflexivity.
end-/

/- Applying a function constructed with [sigT_ind] to a [path_sigma] can be computed.  Technically this computation should probably go by way of a 2-variable [ap], and should be done in the dependently typed case. -/

definition ap_sigT_rec_path_sigma {A : Type} (P : A → Type) {Q : Type}
           (x1 x2:A) (p:x1=x2) (y1:P x1) (y2:P x2) (q:p ▹ y1 = y2)
           (d : Πa, P a → Q)
: ap (sigT_ind (λ_, Q) d) (path_sigma' P p q)
  = (transport_const p _)⁻¹
    ⬝ (ap ((transport (λ_, Q) p) ∘ (d x1)) (transport_Vp _ p y1))⁻¹

    ⬝ (transport_arrow p _ _)⁻¹
    ⬝ ap10 (apD d p) (p ▹ y1)
      ⬝ ap (d x2) q.
/-begin
  destruct p. destruct q. reflexivity.
end-/


/- A path between paths in a total space is commonly shown component wise. -/

/- With this version of the function, we often have to give [u] and [v] explicitly, so we make them explicit arguments. -/
definition path_path_sigma_uncurried {A : Type} (P : A → Type) (u v : sigT P)
           (p q : u = v)
           (rs : Σr : p..1 = q..1, transport (λx, transport P x u.2 = v.2) r p..2 = q..2)
: p = q.
/-begin
  destruct rs, p, u.
  etransitivity; [ | apply eta_path_sigma ].
  path_induction.
  reflexivity.
end-/

/- This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. -/
definition path_path_sigma {A : Type} (P : A → Type) (u v : sigT P)
           (p q : u = v)
           (r : p..1 = q..1)
           (s : transport (λx, transport P x u.2 = v.2) r p..2 = q..2)
: p = q :=
     path_path_sigma_uncurried P u v p q ⟨r, s⟩.

/- Transport -/

/- The concrete description of transport in sigmas (and also pis) is rather trickier than in the other types.  In particular, these cannot be described just in terms of transport in simpler types; they require also the dependent transport [transportD].

  In particular, this indicates why "transport" alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory).  A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? -/

definition transport_sigma {A : Type} {B : A → Type} {C : Πa:A, B a → Type}
           {x1 x2 : A} (p : x1 = x2) (yz : Σy : B x1, C x1 y )
: transport (λx, Σy : B x, C x y ) p yz
  = (p ▹ yz.1 ; transportD _ _ p yz.1 yz.2).
/-begin
  destruct p.  destruct yz as [y z]. reflexivity.
end-/

/- The special case when the second variable doesn't depend on the first is simpler. -/
definition transport_sigma' {A B : Type} {C : A → B → Type}
           {x1 x2 : A} (p : x1 = x2) (yz : Σy : B, C x1 y )
: transport (λx, Σy : B, C x y ) p yz =
  (yz.1 ; transport (λx, C x yz.1) p yz.2).
/-begin
  destruct p. destruct yz. reflexivity.
end-/

/- Or if the second variable contains a first component that doesn't depend on the first.  Need to think about the naming of these. -/

definition transport_sigma_' {A : Type} {B C : A → Type}
           {D : Πa:A, B a → C a → Type}
           {x1 x2 : A} (p : x1 = x2)
           (yzw : Σy : B x1, Σz : C x1, D x1 y z  )
: transport (λx, Σy : B x, Σz : C x, D x y z  ) p yzw
  = (p ▹ yzw.1 ; (p ▹ yzw.2.1 ; transportD2 _ _ _ p yzw.1 yzw.2.1 yzw.2.2)).
/-begin
  destruct p. reflexivity.
end-/

/- Functorial action -/

definition functor_sigma {P : A → Type} {Q : B → Type}
           (f : A → B) (g : Πa, P a → Q (f a))
: sigT P → sigT Q :=
     λu, ⟨f u.1 , g u.1 u.2⟩.

definition ap_functor_sigma {P : A → Type} {Q : B → Type}
           (f : A → B) (g : Πa, P a → Q (f a))
           (u v : sigT P) (p : u.1 = v.1) (q : p ▹ u.2 = v.2)
: ap (functor_sigma f g) (path_sigma P u v p q)
  = path_sigma Q (functor_sigma f g u) (functor_sigma f g v)
               (ap f p)
               ((transport_compose Q f p (g u.1 u.2))⁻¹
                ⬝ (@ap_transport _ P (λx, Q (f x)) _ _ p g u.2)⁻¹
                ⬝ ap (g v.1) q).
/-begin
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in p, q.
  destruct p; simpl in q.
  destruct q.
  reflexivity.
end-/

/- Equivalences -/

definition isequiv_functor_sigma [instance] {P : A → Type} {Q : B → Type}
         [H : is_equiv A B f] [H : Πa, @is_equiv (P a) (Q (f a)) (g a)]
: is_equiv (functor_sigma f g) | 1000.
/-begin
  refine (isequiv_adjointify (functor_sigma f g)
                             (functor_sigma (f⁻¹)
                                            (λx y, ((g (f⁻¹ x))⁻¹ ((retr f x)⁻¹ ▹ y)))) _ _);
  intros [x y].
  - refine (path_sigma' _ (retr f x) _); simpl.
    rewrite (retr (g (f⁻¹ x))).
    apply transport_pV.
  - refine (path_sigma' _ (sect f x) _); simpl.
    refine ((ap_transport (sect f x) (λx', (g x') ⁻¹)
                          (transport Q (retr f (f x)) ⁻¹ (g x y)))⁻¹ ⬝ _).
    rewrite transport_compose, adj, transport_pV.
    apply eissect.
Qed.

definition equiv_functor_sigma {P : A → Type} {Q : B → Type}
           (f : A → B) [H : is_equiv A B f]
           (g : Πa, P a → Q (f a))
           [H : Πa, @is_equiv (P a) (Q (f a)) (g a)]
: sigT P ≃ sigT Q :=
     equiv.mk _ _ (functor_sigma f g) _.

definition equiv_functor_sigma' {P : A → Type} {Q : B → Type}
           (f : A ≃ B)
           (g : Πa, P a ≃ Q (f a))
: sigT P ≃ sigT Q :=
     equiv_functor_sigma f g.

definition equiv_functor_sigma_id {P : A → Type} {Q : A → Type}
           (g : Πa, P a ≃ Q a)
: sigT P ≃ sigT Q :=
     equiv_functor_sigma (equiv_idmap A) g.

/- definition 3.11.9(i): Summing up a contractible family of types does nothing. -/

definition isequiv_pr1_contr [instance] {A} {P : A → Type}
         [H : Πa, is_contr (P a)]
: is_equiv (@dpr1 A P) | 100.
Proof.
  refine (isequiv_adjointify (@dpr1 A P)
                             (λa, (a ; center (P a))) _ _).
  - intros a; reflexivity.
  - intros [a p].
    refine (path_sigma' P 1 (contr _)).
end-/

definition equiv_sigma_contr {A : Type} (P : A → Type)
           [H : Πa, is_contr (P a)]
: sigT P ≃ A :=
     equiv.mk _ _ dpr1 _.

/- definition 3.11.9(ii): Dually, summing up over a contractible type does nothing. -/

definition equiv_contr_sigma {A : Type} (P : A → Type) [H : is_contr A]
: Σx : A, P x  ≃ P (center A).
/-begin
  refine (equiv_adjointify (λxp, (contr xp.1)⁻¹ ▹ xp.2)
                           (λp, ⟨center A , p⟩) _ _).
  - intros p; simpl.
    exact (ap (λq, q ▹ p) (path_contr _ 1)).
  - intros [a p].
    refine (path_sigma' _ (contr a) _).
    apply transport_pV.
end-/

/- Associativity -/

definition equiv_sigma_assoc `(P : A → Type) (Q : Σa : A, P a → Type)
: Σa : A, Σp : P a, Q ⟨a,p⟩ ≃ sigT Q :=
     @equiv.mk
       _ _ _
       (@is_equiv.mk
          Σa : A, Σp : P a, Q ⟨a,p⟩ (sigT Q)
          (λapq, (⟨apq.1, apq.2.1⟩; apq.2.2))
          (λapq, (apq.1.1; ⟨apq.1.2, apq.2⟩))
          (λ_, 1)
          (λ_, 1)
          (λ_, 1)).

definition equiv_sigma_prod `(Q : (A × B) → Type)
: Σa : A, Σb : B, Q (a,b) ≃ sigT Q :=
     @equiv.mk
       _ _ _
       (@is_equiv.mk
          Σa : A, Σb : B, Q (a,b) (sigT Q)
          (λapq, ((apq.1, apq.2.1); apq.2.2))
          (λapq, (pr1 apq.1; ⟨pr2 apq.1, apq.2⟩))
          (λ_, 1)
          (λ_, 1)
          (λ_, 1)).

/- apply symmetry.-/

definition equiv_sigma_symm `(P : A → B → Type)
: Σa : A, Σb : B, P a b ≃ Σb : B, Σa : A, P a b :=
   equiv_compose'
     (equiv_inverse (equiv_sigma_prod (λx, P (pr2 x) (pr1 x))))
   (equiv_compose'
      (equiv_functor_sigma' (equiv_prod_symm A B)
                            (λx, equiv_idmap (P (pr1 x) (pr2 x))))
      (equiv_sigma_prod (λx, P (pr1 x) (pr2 x)))).

definition equiv_sigma_symm0 (A B : Type)
: Σa : A, B ≃ Σb : B, A.
/-begin
  refine (equiv.mk _ _ (λ(w:Σa:A, B), ⟨w.2 , w.1⟩) _).
  refine (is_equiv.mk _ _ _ (λ(z:Σb:B, A), ⟨z.2 , z.1⟩)
                       _ _ _); intros [x y]; reflexivity.
end-/

/- Universal mapping properties -/

/- The positive universal property. -/
definition isequiv_sigT_ind [instance] {P : A → Type}
         (Q : sigT P → Type)
: is_equiv (sigT_ind Q) | 0 :=
     is_equiv.mk
       _ _
       (sigT_ind Q)
       (λf x y, f ⟨x,y⟩)
       (λ_, 1)
       (λ_, 1)
       (λ_, 1).

definition equiv_sigT_ind {P : A → Type}
           (Q : sigT P → Type)
: (Π(x:A) (y:P x), Q ⟨x,y⟩) ≃ (Πxy, Q xy) :=
     equiv.mk _ _ (sigT_ind Q) _.

/- The negative universal property. -/

definition sigT_coind_uncurried
           {A : X → Type} (P : Πx, A x → Type)
: Σf : Πx, A x, Πx, P x (f x) 
  → (Πx, sigT (P x)) :=
     λfg, λx, ⟨fg.1 x , fg.2 x⟩.

definition sigT_coind
           {A : X → Type} (P : Πx, A x → Type)
           (f : Πx, A x) (g : Πx, P x (f x))
: (Πx, sigT (P x)) :=
     sigT_coind_uncurried P ⟨f,g⟩.

Global Instance isequiv_sigT_coind
         {A : X → Type} {P : Πx, A x → Type}
: is_equiv (sigT_coind_uncurried P) | 0 :=
     is_equiv.mk
       _ _
       (sigT_coind_uncurried P)
       (λh, existT (λf, Πx, P x (f x))
                        (λx, (h x).1)
                        (λx, (h x).2))
       (λ_, 1)
       (λ_, 1)
       (λ_, 1).

definition equiv_sigT_coind
           `(A : X → Type) (P : Πx, A x → Type)
: Σf : Πx, A x, Πx, P x (f x) 
    ≃ (Πx, sigT (P x)) :=
     equiv.mk _ _ (sigT_coind_uncurried P) _.

/- Sigmas preserve truncation -/

definition trunc_sigma [instance] {P : A → Type}
         [H : is_trunc n A] [H : Πa, is_trunc n (P a)]
: is_trunc n (sigT P) | 100.
/-begin
  generalize dependent A.
  induction n; simpl; intros A P ac Pc.
  { exists (center A; center (P (center A))).
    intros [a ?].
    refine (path_sigma' P (contr a) (path_contr _ _)). }
  { intros u v.
    refine (trunc_equiv _ (path_sigma_uncurried P u v)). }
end-/

/- Subtypes (sigma types whose second components are hprops) -/

/- To prove equality in a subtype, we only need equality of the first component. -/
definition path_sigma_hprop {A : Type} {P : A → Type}
           [H : Πx, is_hprop (P x)]
           (u v : sigT P)
: u.1 = v.1 → u = v :=
     path_sigma_uncurried P u v ∘ dpr1⁻¹.

definition isequiv_path_sigma_hprop [instance] {A P} {Πx : A, is_hprop (P x)} {u v : sigT P}
: is_equiv (@path_sigma_hprop A P _ u v) | 100 :=
     isequiv_compose.

Hint Immediate isequiv_path_sigma_hprop : typeclass_instances.

definition equiv_path_sigma_hprop {A : Type} {P : A → Type}
           {HP : Πa, is_hprop (P a)} (u v : sigT P)
: (u.1 = v.1) ≃ (u = v) :=
     equiv.mk _ _ (path_sigma_hprop _ _) _.
