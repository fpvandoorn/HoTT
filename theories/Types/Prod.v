/- -*- mode: coq; mode: visual-line -*- -/
/- Theorems about cartesian products -/

Require Import HoTT.Basics.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

Scheme prod_ind := Induction for prod Sort Type.
Arguments prod_ind {A B} P f p.

/- Unpacking -/

/- Sometimes we would like to prove [Q u] where [u : A × B] by writing [u] as a pair [⟨pr1 u , pr2 u⟩]. This is accomplished by [unpack_prod]. We want tight control over the proof, so we just write it down even though is looks a bit scary. -/

definition unpack_prod {P : A × B → Type} (u : A × B) :
  P (pr1 u, pr2 u) → P u :=
     idmap.

Arguments unpack_prod / .

/- Now we write down the reverse. -/
definition pack_prod {P : A × B → Type} (u : A × B) :
  P u → P (pr1 u, pr2 u) :=
     idmap.

Arguments pack_prod / .

/- Eta conversion -/

definition eta_prod `(z : A × B) : (pr1 z, pr2 z) ≈ z :=
     1.

Arguments eta_prod / .

/- Paths -/

/- With this version of the function, we often have to give [z] and [z'] explicitly, so we make them explicit arguments. -/
definition path_prod_uncurried {A B : Type} (z z' : A × B)
  (pq : (pr1 z ≈ pr1 z') × (pr2 z ≈ pr2 z'))
  : (z ≈ z').
/-begin
  change ((pr1 z, pr2 z) ≈ (pr1 z', pr2 z')).
  case (pr1 pq). case (pr2 pq).
  reflexivity.
end-/

/- This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. -/
definition path_prod {A B : Type} (z z' : A × B) :
  (pr1 z ≈ pr1 z') → (pr2 z ≈ pr2 z') → (z ≈ z') :=
     λp q, path_prod_uncurried z z' (p,q).

/- This version produces only paths between pairs, as opposed to paths between arbitrary inhabitants of product types.  But it has the advantage that the components of those pairs can more often be inferred. -/
definition path_prod' {A B : Type} {x x' : A} {y y' : B}
  : (x ≈ x') → (y ≈ y') → ((x,y) ≈ (x',y')) :=
     λp q, path_prod (x,y) (x',y') p q.

/- Now we show how these things compute. -/

definition ap_fst_path_prod {A B : Type} {z z' : A × B}
  (p : pr1 z ≈ pr1 z') (q : pr2 z ≈ pr2 z') :
  ap pr1 (path_prod _ _ p q) ≈ p.
/-begin
  change z with (pr1 z, pr2 z).
  change z' with (pr1 z', pr2 z').
  destruct p, q.
  reflexivity.
end-/

definition ap_snd_path_prod {A B : Type} {z z' : A × B}
  (p : pr1 z ≈ pr1 z') (q : pr2 z ≈ pr2 z') :
  ap pr2 (path_prod _ _ p q) ≈ q.
/-begin
  change z with (pr1 z, pr2 z).
  change z' with (pr1 z', pr2 z').
  destruct p, q.
  reflexivity.
end-/

definition eta_path_prod {A B : Type} {z z' : A × B} (p : z ≈ z') :
  path_prod _ _(ap pr1 p) (ap pr2 p) ≈ p.
/-begin
  destruct p. reflexivity.
end-/

/- Now we show how these compute with transport. -/

definition transport_path_prod_uncurried {A B} (P : A × B → Type) {x y : A × B}
      (H : (pr1 x ≈ pr1 y) × (pr2 x ≈ pr2 y))
      (Px : P x)
: transport P (path_prod_uncurried _ _ H) Px
  ≈ transport (λx, P (x, pr2 y))
              (pr1 H)
              (transport (λy, P (pr1 x, y))
                         (pr2 H)
                         Px).
/-begin
  destruct x, y, H; simpl in *.
  path_induction.
  reflexivity.
end-/

definition transport_path_prod {A B} (P : A × B → Type) {x y : A × B}
           (HA : pr1 x ≈ pr1 y)
           (HB : pr2 x ≈ pr2 y)
           (Px : P x)
: transport P (path_prod _ _ HA HB) Px
  ≈ transport (λx, P (x, pr2 y))
              HA
              (transport (λy, P (pr1 x, y))
                         HB
                         Px) :=
     transport_path_prod_uncurried P (HA, HB) Px.

definition transport_path_prod'
           {A B} (P : A × B → Type)
           {x y : A}
           {x' y' : B}
           (HA : x ≈ y)
           (HB : x' ≈ y')
           (Px : P (x,x'))
: transport P (path_prod' HA HB) Px
  ≈ transport (λx, P (x, y'))
              HA
              (transport (λy, P (x, y))
                         HB
                         Px) :=
     @transport_path_prod _ _ P (x, x') (y, y') HA HB Px.

/- This lets us identify the path space of a product type, up to equivalence. -/

definition isequiv_path_prod [instance] {A B : Type} {z z' : A × B}
: IsEquiv (path_prod_uncurried z z') | 0 :=
     IsEquiv.mk
       _ _ _
       (λr, (ap pr1 r, ap pr2 r))
       eta_path_prod
       (λpq, path_prod'
                    (ap_fst_path_prod (pr1 pq) (pr2 pq))
                    (ap_snd_path_prod (pr1 pq) (pr2 pq)))
       _.
/-begin
  destruct z as [x y], z' as [x' y'].
  intros [p q]; simpl in p, q.
  destruct p, q; reflexivity.
end-/

definition equiv_path_prod {A B : Type} (z z' : A × B)
  : (pr1 z ≈ pr1 z') × (pr2 z ≈ pr2 z')  ≃  (z ≈ z') :=
     Equiv.mk _ _ (path_prod_uncurried z z') _.

/- Transport -/

definition transport_prod {A : Type} {P Q : A → Type} {a a' : A} (p : a ≈ a')
  (z : P a × Q a)
  : transport (λa, P a × Q a) p z  ≈  (p ▹ (pr1 z), p ▹ (pr2 z)) :=
     match p with idpath => 1 end.

/- Functorial action -/

definition functor_prod {A A' B B' : Type} (f:A->A') (g:B->B')
  : A × B → A' × B' :=
     λz, (f (pr1 z), g (pr2 z)).

definition ap_functor_prod {A A' B B' : Type} (f:A->A') (g:B->B')
  (z z' : A × B) (p : pr1 z ≈ pr1 z') (q : pr2 z ≈ pr2 z')
  : ap (functor_prod f g) (path_prod _ _ p q)
  ≈ path_prod (functor_prod f g z) (functor_prod f g z') (ap f p) (ap g q).
/-begin
  destruct z as [a b]; destruct z' as [a' b'].
  simpl in p, q. destruct p, q. reflexivity.
end-/

/- Equivalences -/

definition isequiv_functor_prod [instance] [H : IsEquiv A A' f] [H : IsEquiv B B' g]
: IsEquiv (functor_prod f g) | 1000 :=
     IsEquiv.mk
       _ _ (functor_prod f g) (functor_prod f⁻¹ g⁻¹)
       (λz, path_prod' (eisretr f (pr1 z)) (eisretr g (pr2 z)) ⬝ eta_prod z)
       (λw, path_prod' (eissect f (pr1 w)) (eissect g (pr2 w)) ⬝ eta_prod w)
       _.
/-begin
  intros [a b]; simpl.
  unfold path_prod'.
  rewrite !concat_p1.
  rewrite ap_functor_prod.
  rewrite !eisadj.
  reflexivity.
end-/

definition equiv_functor_prod [H : IsEquiv A A' f] [H : IsEquiv B B' g]
  : A × B ≃ A' × B'.
/-begin
  exists (functor_prod f g).
  exact _. /- i.e., search the context for instances -/
end-/

definition equiv_functor_prod' {A A' B B' : Type} (f : A ≃ A') (g : B ≃ B')
  : A × B ≃ A' × B'.
/-begin
  exists (functor_prod f g).
  exact _.
end-/

definition equiv_functor_prod_l {A B B' : Type} (g : B ≃ B')
  : A × B ≃ A × B'.
/-begin
  exists (functor_prod idmap g).
  exact _.
end-/

definition equiv_functor_prod_r {A A' B : Type} (f : A ≃ A')
  : A × B ≃ A' × B.
/-begin
  exists (functor_prod f idmap).
  exact _.
end-/

/- Symmetry -/

/- This is a special property of [prod], of course, not an instance of a general family of facts about types. -/

definition equiv_prod_symm (A B : Type) : A × B ≃ B × A :=
     Equiv.mk
       _ _ _
       (IsEquiv.mk
          (A*B) (B*A)
          (λab, (pr2 ab, pr1 ab))
          (λba, (pr2 ba, pr1 ba))
          (λ_, 1)
          (λ_, 1)
          (λ_, 1)).

/- Associativity -/

/- This, too, is a special property of [prod], of course, not an instance of a general family of facts about types. -/
definition equiv_prod_assoc (A B C : Type) : A × (B × C) ≃ (A × B) × C :=
     Equiv.mk
       _ _ _
       (IsEquiv.mk
          (A × (B × C)) ((A × B) × C)
          (λabc, ((pr1 abc, pr1 (pr2 abc)), pr2 (pr2 abc)))
          (λabc, (pr1 (pr1 abc), (pr2 (pr1 abc), pr2 abc)))
          (λ_, 1)
          (λ_, 1)
          (λ_, 1)).

/- Universal mapping properties -/

/- Ordinary universal mapping properties are expressed as equivalences of sets or spaces of functions.  In type theory, we can go beyond this and express an equivalence of types of *dependent* functions.  Moreover, because the product type can expressed both positively and negatively, it has both a left universal property and a right one. -/

/- First the positive universal property. -/
definition isequiv_prod_ind [instance] `(P : A × B → Type)
: IsEquiv (prod_ind P) | 0 :=
     IsEquiv.mk
       _ _
       (prod_ind P)
       (λf x y, f (x, y))
       (λ_, 1)
       (λ_, 1)
       (λ_, 1).

definition equiv_prod_ind `(P : A × B → Type)
  : (Π(a : A) (b : B), P (a, b)) ≃ (Πp : A × B, P p) :=
     Equiv.mk _ _ (prod_ind P) _.

/- The non-dependent version, which is a special case, is the currying equivalence. -/
definition equiv_uncurry (A B C : Type)
  : (A → B → C) ≃ (A × B → C) :=
     equiv_prod_ind (λ_, C).

/- Now the negative universal property. -/
definition prod_coind_uncurried {A : X → Type} {B : X → Type}
  : (Πx, A x) × (Πx, B x) → (Πx, A x × B x) :=
     λfg x, (pr1 fg x, pr2 fg x).

definition prod_coind `(f : Πx:X, A x) `(g : Πx:X, B x)
  : Πx, A x × B x :=
     prod_coind_uncurried (f, g).

definition isequiv_prod_coind [instance] `(A : X → Type) (B : X → Type)
: IsEquiv (@prod_coind_uncurried X A B) | 0 :=
     IsEquiv.mk
       _ _
       (@prod_coind_uncurried X A B)
       (λh, (λx, pr1 (h x), λx, pr2 (h x)))
       (λ_, 1)
       (λ_, 1)
       (λ_, 1).

definition equiv_prod_coind `(A : X → Type) (B : X → Type)
  : ((Πx, A x) × (Πx, B x)) ≃ (Πx, A x × B x) :=
     Equiv.mk _ _ (@prod_coind_uncurried X A B) _.

/- Products preserve truncation -/

definition trunc_prod [instance] [H : is_trunc n A] [H : is_trunc n B] : is_trunc n (A × B) | 100.
/-begin
  generalize dependent B; generalize dependent A.
  simple_induction n n IH; simpl; (intros A ? B ?).
  { exists (center A, center B).
    intros z; apply path_prod; apply contr. }
  { intros x y.
    exact (trunc_equiv _ (equiv_path_prod x y)). }
end-/

definition contr_prod [instance] {CA : is_contr A} {CB : is_contr B} : is_contr (A × B) | 100 :=
     @trunc_prod -2 A CA B CB.
