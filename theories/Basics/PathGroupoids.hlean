/- -*- mode: coq; mode: visual-line -*-  -/

/- The groupid structure of paths -/

Require Import Overture.

Local Open Scope path_scope.

/- Naming conventions

   We need good naming conventions that allow us to name theorems without looking them up. The names should indicate the structure of the theorem, but they may sometimes be ambiguous, in which case you just have to know what is going on.    We shall adopt the following principles:

   - we are not afraid of long names
   - we are not afraid of short names when they are used frequently
   - we use underscores
   - name of theorems and lemmas are lower-case
   - records and other types may be upper or lower case

   Theorems about concatenation of paths are called [concat_XXX] where [XXX] tells us what is on the left-hand side of the equation. You have to guess the right-hand side. We use the following symbols in [XXX]:

   - [1] means the identity path
   - [p] means 'the path'
   - [V] means 'the inverse path'
   - [A] means '[ap]'
   - [M] means the thing we are moving across equality
   - [x] means 'the point' which is not a path, e.g. in [transport p x]
   - [2] means relating to 2-dimensional paths
   - [3] means relating to 3-dimensional paths, and so on

   Associativity is indicated with an underscore. Here are some examples of how the name gives hints about the left-hand side of the equation.

   - [concat_1p] means [1 × p]
   - [concat_Vp] means [p⁻¹ × p]
   - [concat_p_con] means [p × (q × r)]
   - [concat_con_p] means [(p × q) × r]
   - [concat_V_con] means [p⁻¹ × (p × q)]
   - [concat_pV_p] means [(q × p⁻¹) × p] or [(p × p⁻¹) × q], but probably the former because for the latter you could just use [concat_pV].

   Laws about inverse of something are of the form [inv_XXX], and those about [ap] are of the form [ap_XXX], and so on. For example:

   - [inv_con] is about [(p ⬝ q)⁻¹]
   - [inv_V] is about [(p⁻¹)⁻¹]
   - [inv_A] is about [(ap f p)⁻¹]
   - [ap_V] is about [ap f (p⁻¹)]
   - [ap_con] is about [ap f (p ⬝ q)]
   - [ap_idmap] is about [ap idmap p]
   - [ap_1] is about [ap f 1]
   - [ap02_p2p] is about [ap02 f (p @@ q)]

   Then we have laws which move things around in an equation. The naming scheme here is [moveD_XXX]. The direction [D] indicates where to move to: [L] means that we move something to the left-hand side, whereas [R] means we are moving something to the right-hand side. The part [XXX] describes the shape of the side _from_ which we are moving where the thing that is getting moves is called [M].  The presence of 1 next to an [M] generally indicates an *implied* identity path which is inserted automatically after the movement.  Examples:

   - [moveL_pM] means that we transform [p = q ⬝ r] to [p ⬝ r⁻¹ = q]
     because we are moving something to the left-hand side, and we are
     moving the right argument of concat.

   - [moveR_Mp] means that we transform [p ⬝ q = r] to [q = p⁻¹ ⬝ r]
     because we move to the right-hand side, and we are moving the left
     argument of concat.

   - [moveR_1M] means that we transform [p = q] (rather than [p = 1 ⬝ q]) to [p × q⁻¹ = 1].

   There are also cancellation laws called [cancelR] and [cancelL], which are inverse to the 2-dimensional 'whiskering' operations [whiskerR] and [whiskerL].

   We may now proceed with the groupoid structure proper.
-/

/- The 1-dimensional groupoid structure. -/

/- The identity path is a right unit. -/
definition concat_p1 {A : Type} {x y : A} (p : x = y) :
  p ⬝ 1 = p :=
     
  match p with refl => 1 end.

/- The identity is a left unit. -/
definition concat_1p {A : Type} {x y : A} (p : x = y) :
  1 ⬝ p = p :=
    
  match p with refl => 1 end.

/- Concatenation is associative. -/
definition concat_p_con {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p ⬝ (q ⬝ r) = (p ⬝ q) ⬝ r :=
  match r with refl =>
    match q with refl =>
      match p with refl => 1
      end end end.

definition concat_con_p {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  (p ⬝ q) ⬝ r = p ⬝ (q ⬝ r) :=
  match r with refl =>
    match q with refl =>
      match p with refl => 1
      end end end.

/- The left inverse law. -/
definition concat_pV {A : Type} {x y : A} (p : x = y) :
  p ⬝ p⁻¹ = 1 :=
    
  match p with refl => 1 end.

/- The right inverse law. -/
definition concat_Vp {A : Type} {x y : A} (p : x = y) :
  p⁻¹ ⬝ p = 1 :=
    
  match p with refl => 1 end.

/- Several auxiliary theorems about canceling inverses across associativity.  These are somewhat redundant, following from earlier theorems.  -/

definition concat_V_con {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  p⁻¹ ⬝ (p ⬝ q) = q :=
    
  match q with refl =>
    match p with refl => 1 end
  end.

definition concat_p_Vp {A : Type} {x y z : A} (p : x = y) (q : x = z) :
  p ⬝ (p⁻¹ ⬝ q) = q :=
    
  match q with refl =>
    match p with refl => 1 end
  end.

definition concat_con_V {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p ⬝ q) ⬝ q⁻¹ = p :=
    
  match q with refl =>
    match p with refl => 1 end
  end.

definition concat_pV_p {A : Type} {x y z : A} (p : x = z) (q : y = z) :
  (p ⬝ q⁻¹) ⬝ q = p :=
    
  (match q as i return Πp, (p ⬝ i⁻¹) ⬝ i = p with
    refl =>
    λp,
      match p with refl => 1 end
  end) p.

/- Inverse distributes over concatenation -/
definition inv_con {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p ⬝ q)⁻¹ = q⁻¹ ⬝ p⁻¹ :=
    
  match q with refl =>
    match p with refl => 1 end
  end.

definition inv_Vp {A : Type} {x y z : A} (p : y = x) (q : y = z) :
  (p⁻¹ ⬝ q)⁻¹ = q⁻¹ ⬝ p :=
    
  match q with refl =>
    match p with refl => 1 end
  end.

definition inv_pV {A : Type} {x y z : A} (p : x = y) (q : z = y) :
  (p ⬝ q⁻¹)⁻¹ = q ⬝ p⁻¹.
/-begin
  destruct p. destruct q. reflexivity.
end-/

definition inv_VV {A : Type} {x y z : A} (p : y = x) (q : z = y) :
  (p⁻¹ ⬝ q⁻¹)⁻¹ = q ⬝ p.
/-begin
  destruct p. destruct q. reflexivity.
end-/

/- Inverse is an involution. -/
definition inv_V {A : Type} {x y : A} (p : x = y) :
  p⁻¹⁻¹ = p :=
    
  match p with refl => 1 end.


/- Theorems for moving things around in equations. -/

definition moveR_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  p = r⁻¹ ⬝ q → r ⬝ p = q.
/-begin
  destruct r.
  intro h. exact (concat_1p _ ⬝ h ⬝ concat_1p _).
end-/

definition moveR_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r = q ⬝ p⁻¹ → r ⬝ p = q.
/-begin
  destruct p.
  intro h. exact (concat_p1 _ ⬝ h ⬝ concat_p1 _).
end-/

definition moveR_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  p = r ⬝ q → r⁻¹ ⬝ p = q.
/-begin
  destruct r.
  intro h. exact (concat_1p _ ⬝ h ⬝ concat_1p _).
end-/

definition moveR_pV {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x) :
  r = q ⬝ p → r ⬝ p⁻¹ = q.
/-begin
  destruct p.
  intro h. exact (concat_p1 _ ⬝ h ⬝ concat_p1 _).
end-/

definition moveL_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r⁻¹ ⬝ q = p → q = r ⬝ p.
/-begin
  destruct r.
  intro h. exact ((concat_1p _)⁻¹ ⬝ h ⬝ (concat_1p _)⁻¹).
end-/

definition moveL_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  q ⬝ p⁻¹ = r → q = r ⬝ p.
/-begin
  destruct p.
  intro h. exact ((concat_p1 _)⁻¹ ⬝ h ⬝ (concat_p1 _)⁻¹).
end-/

definition moveL_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r ⬝ q = p → q = r⁻¹ ⬝ p.
/-begin
  destruct r.
  intro h. exact ((concat_1p _)⁻¹ ⬝ h ⬝ (concat_1p _)⁻¹).
end-/

definition moveL_pV {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x) :
  q ⬝ p = r → q = r ⬝ p⁻¹.
/-begin
  destruct p.
  intro h. exact ((concat_p1 _)⁻¹ ⬝ h ⬝ (concat_p1 _)⁻¹).
end-/

definition moveL_1M {A : Type} {x y : A} (p q : x = y) :
  p ⬝ q⁻¹ = 1 → p = q.
/-begin
  destruct q.
  intro h. exact ((concat_p1 _)⁻¹ ⬝ h).
end-/

definition moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  q⁻¹ ⬝ p = 1 → p = q.
/-begin
  destruct q.
  intro h. exact ((concat_1p _)⁻¹ ⬝ h).
end-/

definition moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  p ⬝ q = 1 → p = q⁻¹.
/-begin
  destruct q.
  intro h. exact ((concat_p1 _)⁻¹ ⬝ h).
end-/

definition moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  q ⬝ p = 1 → p = q⁻¹.
/-begin
  destruct q.
  intro h. exact ((concat_1p _)⁻¹ ⬝ h).
end-/

definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  1 = p⁻¹ ⬝ q → p = q.
/-begin
  destruct p.
  intro h. exact (h ⬝ (concat_1p _)).
end-/

definition moveR_1M {A : Type} {x y : A} (p q : x = y) :
  1 = q ⬝ p⁻¹ → p = q.
/-begin
  destruct p.
  intro h. exact (h ⬝ (concat_p1 _)).
end-/

definition moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = q ⬝ p → p⁻¹ = q.
/-begin
  destruct p.
  intro h. exact (h ⬝ (concat_p1 _)).
end-/

definition moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = p ⬝ q → p⁻¹ = q.
/-begin
  destruct p.
  intro h. exact (h ⬝ (concat_1p _)).
end-/

/- In general, the path we want to move might be arbitrarily deeply nested at the beginning of a long concatenation.  Thus, instead of defining functions such as [moveL_Mp_p], we define a tactical that can repeatedly rewrite with associativity to expose it. -/
Ltac with_rassoc tac :=
  repeat rewrite concat_con_p;
  tac;
  /- After moving, we reassociate to the left (the canonical direction for paths). -/
  repeat rewrite concat_p_con.

Ltac rewrite_moveL_Mp_p := with_rassoc ltac:(apply moveL_Mp).
Ltac rewrite_moveL_Vp_p := with_rassoc ltac:(apply moveL_Vp).
Ltac rewrite_moveR_Mp_p := with_rassoc ltac:(apply moveR_Mp).
Ltac rewrite_moveR_Vp_p := with_rassoc ltac:(apply moveR_Vp).

definition moveR_transport_p {A : Type} (P : A → Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : u = p⁻¹ ▹ v → p ▹ u = v.
/-begin
  destruct p.
  exact idmap.
end-/

definition moveR_transport_V {A : Type} (P : A → Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : u = p ▹ v → p⁻¹ ▹ u = v.
/-begin
  destruct p.
  exact idmap.
end-/

definition moveL_transport_V {A : Type} (P : A → Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : p ▹ u = v → u = p⁻¹ ▹ v.
/-begin
  destruct p.
  exact idmap.
end-/

definition moveL_transport_p {A : Type} (P : A → Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : p⁻¹ ▹ u = v → u = p ▹ v.
/-begin
  destruct p.
  exact idmap.
end-/

/- Functoriality of functions -/

/- Here we prove that functions behave like functors between groupoids, and that [ap] itself is functorial. -/

/- Functions take identity paths to identity paths. -/
definition ap_1 {A B : Type} (x : A) (f : A → B) :
  ap f 1 = 1 :> (f x = f x) :=
    
  1.

definition apD_1 {A B} (x : A) (f : Πx : A, B x) :
  apD f 1 = 1 :> (f x = f x) :=
    
  1.

/- Functions commute with concatenation. -/
definition ap_con {A B : Type} (f : A → B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p ⬝ q) = (ap f p) ⬝ (ap f q) :=
    
  match q with
    refl =>
    match p with refl => 1 end
  end.

definition ap_p_con {A B : Type} (f : A → B) {w : B} {x y z : A}
  (r : w = f x) (p : x = y) (q : y = z) :
  r ⬝ (ap f (p ⬝ q)) = (r ⬝ ap f p) ⬝ (ap f q).
/-begin
  destruct p, q. simpl. exact (concat_p_con r 1 1).
end-/

definition ap_con_p {A B : Type} (f : A → B) {x y z : A} {w : B}
  (p : x = y) (q : y = z) (r : f z = w) :
  (ap f (p ⬝ q)) ⬝ r = (ap f p) ⬝ (ap f q ⬝ r).
/-begin
  destruct p, q. simpl. exact (concat_con_p 1 1 r).
end-/

/- Functions commute with path inverses. -/
definition inverse_ap {A B : Type} (f : A → B) {x y : A} (p : x = y) :
  (ap f p)⁻¹ = ap f (p⁻¹) :=
    
  match p with refl => 1 end.

definition ap_V {A B : Type} (f : A → B) {x y : A} (p : x = y) :
  ap f (p⁻¹) = (ap f p)⁻¹ :=
    
  match p with refl => 1 end.

/- [ap] itself is functorial in the first argument. -/

definition ap_idmap {A : Type} {x y : A} (p : x = y) :
  ap idmap p = p :=
    
  match p with refl => 1 end.

definition ap_compose {A B C : Type} (f : A → B) (g : B → C) {x y : A} (p : x = y) :
  ap (g ∘ f) p = ap g (ap f p) :=
    
  match p with refl => 1 end.

/- Sometimes we don't have the actual function [compose]. -/
definition ap_compose' {A B C : Type} (f : A → B) (g : B → C) {x y : A} (p : x = y) :
  ap (λa, g (f a)) p = ap g (ap f p) :=
    
  match p with refl => 1 end.

/- The action of constant maps. -/
definition ap_const {A B : Type} {x y : A} (p : x = y) (z : B) :
  ap (λ_, z) p = 1 :=
    
  match p with refl => refl end.

/- Naturality of [ap]. -/
definition concat_Ap {A B : Type} {f g : A → B} (p : Πx, f x = g x) {x y : A} (q : x = y) :
  (ap f q) ⬝ (p y) = (p x) ⬝ (ap g q) :=
    
  match q with
    | refl => concat_1p _ ⬝ ((concat_p1 _) ⁻¹)
  end.

/- Naturality of [ap] at identity. -/
definition concat_A1p {A : Type} {f : A → A} (p : Πx, f x = x) {x y : A} (q : x = y) :
  (ap f q) ⬝ (p y) = (p x) ⬝ q :=
    
  match q with
    | refl => concat_1p _ ⬝ ((concat_p1 _) ⁻¹)
  end.

definition concat_pA1 {A : Type} {f : A → A} (p : Πx, x = f x) {x y : A} (q : x = y) :
  (p x) ⬝ (ap f q) =  q ⬝ (p y) :=
    
  match q as i in (_ = y) return (p x ⬝ ap f i = i ⬝ p y) with
    | refl => concat_p1 _ ⬝ (concat_1p _)⁻¹
  end.

/- Naturality with other paths hanging around. -/
definition concat_pA_con {A B : Type} {f g : A → B} (p : Πx, f x = g x)
  {x y : A} (q : x = y)
  {w z : B} (r : w = f x) (s : g y = z)
  :
  (r ⬝ ap f q) ⬝ (p y ⬝ s) = (r ⬝ p x) ⬝ (ap g q ⬝ s).
/-begin
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
end-/

definition concat_pA_p {A B : Type} {f g : A → B} (p : Πx, f x = g x)
  {x y : A} (q : x = y)
  {w : B} (r : w = f x)
  :
  (r ⬝ ap f q) ⬝ p y = (r ⬝ p x) ⬝ ap g q.
/-begin
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
end-/

definition concat_A_con {A B : Type} {f g : A → B} (p : Πx, f x = g x)
  {x y : A} (q : x = y)
  {z : B} (s : g y = z)
  :
  (ap f q) ⬝ (p y ⬝ s) = (p x) ⬝ (ap g q ⬝ s).
/-begin
  destruct q, s; cbn.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
end-/

definition concat_pA1_con {A : Type} {f : A → A} (p : Πx, f x = x)
  {x y : A} (q : x = y)
  {w z : A} (r : w = f x) (s : y = z)
  :
  (r ⬝ ap f q) ⬝ (p y ⬝ s) = (r ⬝ p x) ⬝ (q ⬝ s).
/-begin
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
end-/

definition concat_con_A1p {A : Type} {g : A → A} (p : Πx, x = g x)
  {x y : A} (q : x = y)
  {w z : A} (r : w = x) (s : g y = z)
  :
  (r ⬝ p x) ⬝ (ap g q ⬝ s) = (r ⬝ q) ⬝ (p y ⬝ s).
/-begin
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
end-/

definition concat_pA1_p {A : Type} {f : A → A} (p : Πx, f x = x)
  {x y : A} (q : x = y)
  {w : A} (r : w = f x)
  :
  (r ⬝ ap f q) ⬝ p y = (r ⬝ p x) ⬝ q.
/-begin
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
end-/

definition concat_A1_con {A : Type} {f : A → A} (p : Πx, f x = x)
  {x y : A} (q : x = y)
  {z : A} (s : y = z)
  :
  (ap f q) ⬝ (p y ⬝ s) = (p x) ⬝ (q ⬝ s).
/-begin
  destruct q, s; cbn.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
end-/

definition concat_con_A1 {A : Type} {g : A → A} (p : Πx, x = g x)
  {x y : A} (q : x = y)
  {w : A} (r : w = x)
  :
  (r ⬝ p x) ⬝ ap g q = (r ⬝ q) ⬝ p y.
/-begin
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
end-/

definition concat_p_A1p {A : Type} {g : A → A} (p : Πx, x = g x)
  {x y : A} (q : x = y)
  {z : A} (s : g y = z)
  :
  p x ⬝ (ap g q ⬝ s) = q ⬝ (p y ⬝ s).
/-begin
  destruct q, s; simpl.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
end-/

/- Action of [apD10] and [ap10] on paths. -/

/- Application of paths between functions preserves the groupoid structure -/

definition apD10_1 {A} {B:A->Type} (f : Πx, B x) (x:A)
  : apD10 (refl f) x = 1 :=
   1.

definition apD10_con {A} {B:A->Type} {f f' f'' : Πx, B x}
  (h:f=f') (h':f'=f'') (x:A)
: apD10 (h ⬝ h') x = apD10 h x ⬝ apD10 h' x.
/-begin
  case h, h'; reflexivity.
end-/

definition apD10_V {A} {B:A->Type} {f g : Πx, B x} (h:f=g) (x:A)
  : apD10 (h⁻¹) x = (apD10 h x)⁻¹ :=
   match h with refl => 1 end.

definition ap10_1 {A B} {f:A->B} (x:A) : ap10 (refl f) x = 1 :=
     1.

definition ap10_con {A B} {f f' f'':A->B} (h:f=f') (h':f'=f'') (x:A)
  : ap10 (h ⬝ h') x = ap10 h x ⬝ ap10 h' x :=
   apD10_con h h' x.

definition ap10_V {A B} {f g : A->B} (h : f = g) (x:A)
  : ap10 (h⁻¹) x = (ap10 h x)⁻¹ :=
   apD10_V h x.

/- [apD10] and [ap10] also behave nicely on paths produced by [ap] -/
definition apD10_ap_precompose {A B C} (f : A → B) {g g' : Πx:B, C x} (p : g = g') a
: apD10 (ap (λh : Πx:B, C x, h oD f) p) a = apD10 p (f a).
/-begin
  destruct p; reflexivity.
end-/

definition ap10_ap_precompose {A B C} (f : A → B) {g g' : B → C} (p : g = g') a
: ap10 (ap (λh : B → C, h ∘ f) p) a = ap10 p (f a) :=
   apD10_ap_precompose f p a.

definition apD10_ap_postcompose {A B C} (f : Πx, B x → C) {g g' : Πx:A, B x} (p : g = g') a
: apD10 (ap (λh : Πx:A, B x, λx, f x (h x)) p) a = ap (f a) (apD10 p a).
/-begin
  destruct p; reflexivity.
end-/

definition ap10_ap_postcompose {A B C} (f : B → C) {g g' : A → B} (p : g = g') a
: ap10 (ap (λh : A → B, f ∘ h) p) a = ap f (ap10 p a) :=
   apD10_ap_postcompose (λa, f) p a.

/- Transport and the groupoid structure of paths -/

definition transport_1 {A : Type} (P : A → Type) {x : A} (u : P x)
  : 1 ▹ u = u :=
   1.

definition transport_con {A : Type} (P : A → Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p ⬝ q ▹ u = q ▹ p ▹ u :=
  match q with refl =>
    match p with refl => 1 end
  end.

definition transport_pV {A : Type} (P : A → Type) {x y : A} (p : x = y) (z : P y)
  : p ▹ p⁻¹ ▹ z = z :=
     (transport_con P p⁻¹ p z)⁻¹
  ⬝ ap (λr, transport P r z) (concat_Vp p).

definition transport_Vp {A : Type} (P : A → Type) {x y : A} (p : x = y) (z : P x)
  : p⁻¹ ▹ p ▹ z = z :=
     (transport_con P p p⁻¹ z)⁻¹
  ⬝ ap (λr, transport P r z) (concat_pV p).

/- In the future, we may expect to need some higher coherence for transport:
  for instance, that transport acting on the associator is trivial. -/
definition transport_p_con {A : Type} (P : A → Type)
  {x y z w : A} (p : x = y) (q : y = z) (r : z = w)
  (u : P x)
  : ap (λe, e ▹ u) (concat_p_con p q r)
    ⬝ (transport_con P (p@q) r u) ⬝ ap (transport P r) (transport_con P p q u)
  = (transport_con P p (q@r) u) ⬝ (transport_con P q r (p#u))
  :> ((p ⬝ (q ⬝ r)) ▹ u = r ▹ q ▹ p ▹ u) .
/-begin
  destruct p, q, r.  simpl.  exact 1.
end-/

/- Here is another coherence lemma for transport. -/
definition transport_pVp {A} (P : A → Type) {x y:A} (p:x=y) (z:P x)
  : transport_pV P p (transport P p z)
  = ap (transport P p) (transport_Vp P p z).
/-begin
  destruct p; reflexivity.
end-/

/- Dependent transport in doubly dependent types and more. -/

definition transportD {A : Type} (B : A → Type) (C : Πa:A, B a → Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y)
  : C x2 (p ▹ y) :=
    
  match p with refl => z end.

definition transportD2 {A : Type} (B C : A → Type) (D : Πa:A, B a → C a → Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1) (w : D x1 y z)
  : D x2 (p ▹ y) (p ▹ z) :=
    
  match p with refl => w end.

/- [ap] for multivariable functions -/

definition ap011 {A B C} (f : A → B → C) {x x' y y'} (p : x = x') (q : y = y')
: f x y = f x' y' :=
   ap11 (ap f p) q.

/- It would be nice to have a consistent way to name the different ways in which this can be dependent.  The following are a sort of half-hearted attempt. -/

definition ap011D {A B C} (f : Π(a:A), B a → C)
           {x x'} (p : x = x') {y y'} (q : p ▹ y = y')
: f x y = f x' y'.
/-begin
  destruct p, q; reflexivity.
end-/

definition ap01D1 {A B C} (f : Π(a:A), B a → C a)
           {x x'} (p : x = x') {y y'} (q : p ▹ y = y')
: transport C p (f x y) = f x' y'.
/-begin
  destruct p, q; reflexivity.
end-/

definition apD011 {A B C} (f : Π(a:A) (b:B a), C a b)
           {x x'} (p : x = x') {y y'} (q : p ▹ y = y')
: transport (C x') q (transportD B C p y (f x y)) = f x' y'.
/-begin
  destruct p, q; reflexivity.
end-/

/- Transporting along higher-dimensional paths -/

definition transport2 {A : Type} (P : A → Type) {x y : A} {p q : x = y}
  (r : p = q) (z : P x)
  : p ▹ z = q ▹ z :=
     ap (λp', p' ▹ z) r.

/- An alternative definition. -/
definition transport2_is_ap10 {A : Type} (Q : A → Type) {x y : A} {p q : x = y}
  (r : p = q) (z : Q x)
  : transport2 Q r z = ap10 (ap (transport Q) r) z :=
     match r with refl => 1 end.

definition transport2_p2p {A : Type} (P : A → Type) {x y : A} {p1 p2 p3 : x = y}
  (r1 : p1 = p2) (r2 : p2 = p3) (z : P x)
  : transport2 P (r1 ⬝ r2) z = transport2 P r1 z ⬝ transport2 P r2 z.
/-begin
  destruct r1, r2; reflexivity.
end-/

definition transport2_V {A : Type} (Q : A → Type) {x y : A} {p q : x = y}
  (r : p = q) (z : Q x)
  : transport2 Q (r⁻¹) z = (transport2 Q r z)⁻¹ :=
     match r with refl => 1 end.

definition concat_AT {A : Type} (P : A → Type) {x y : A} {p q : x = y}
  {z w : P x} (r : p = q) (s : z = w)
  : ap (transport P p) s  ⬝  transport2 P r w
    = transport2 P r z  ⬝  ap (transport P q) s :=
     match r with refl => (concat_p1 _ ⬝ (concat_1p _)⁻¹) end.

/- TODO: What should this be called? -/
definition ap_transport {A} {P Q : A → Type} {x y : A} (p : x = y) (f : Πx, P x → Q x) (z : P x) :
  f y (p ▹ z) = (p ▹ (f x z)).
/-begin
  by induction p.
end-/

definition ap_transportD {A : Type}
      (B : A → Type) (C1 C2 : Πa : A, B a → Type)
      (f : Πa b, C1 a b → C2 a b)
      {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C1 x1 y)
: f x2 (p ▹ y) (transportD B C1 p y z)
  = transportD B C2 p y (f x1 y z).
/-begin
  by induction p.
end-/

definition ap_transportD2 {A : Type}
      (B C : A → Type) (D1 D2 : Πa, B a → C a → Type)
      (f : Πa b c, D1 a b c → D2 a b c)
      {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1) (w : D1 x1 y z)
: f x2 (p ▹ y) (p ▹ z) (transportD2 B C D1 p y z w)
  = transportD2 B C D2 p y z (f x1 y z w).
/-begin
  by induction p.
end-/

/- TODO: What should this be called? -/
definition ap_transport_pV {X} (Y : X → Type) {x1 x2 : X} (p : x1 = x2)
      {y1 y2 : Y x2} (q : y1 = y2)
: ap (transport Y p) (ap (transport Y p⁻¹) q) =
  transport_pV Y p y1 ⬝ q ⬝ (transport_pV Y p y2)⁻¹.
/-begin
  destruct p, q; reflexivity.
end-/

/- TODO: And this? -/
definition transport_pV_ap {X} (P : X → Type) (f : Πx, P x)
      {x1 x2 : X} (p : x1 = x2)
: ap (transport P p) (apD f p⁻¹) ⬝ apD f p = transport_pV P p (f x2).
/-begin
  destruct p; reflexivity.
end-/


/- Transporting in particular fibrations. -/

/- One frequently needs lemmas showing that transport in a certain dependent type is equal to some more explicitly defined operation, defined according to the structure of that dependent type.  For most dependent types, we prove these lemmas in the appropriate file in the types/ subdirectory.  Here we consider only the most basic cases. -/

/- Transporting in a constant fibration. -/
definition transport_const {A B : Type} {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport (λx, B) p y = y.
/-begin
  destruct p.  exact 1.
end-/

definition transport2_const {A B : Type} {x1 x2 : A} {p q : x1 = x2}
  (r : p = q) (y : B)
  : transport_const p y = transport2 (λ_, B) r y ⬝ transport_const q y :=
     match r with refl => (concat_1p _)⁻¹ end.

/- Transporting in a pulled back fibration. -/
definition transport_compose {A B} {x y : A} (P : B → Type) (f : A → B)
  (p : x = y) (z : P (f x))
  : transport (λx, P (f x)) p z  =  transport P (ap f p) z.
/-begin
  destruct p; reflexivity.
end-/

definition transport_precompose {A B C} (f : A → B) (g g' : B → C) (p : g = g')
: transport (λh : B → C, g ∘ f = h ∘ f) p 1 =
  ap (λh, h ∘ f) p.
/-begin
  destruct p; reflexivity.
end-/

/- A special case of [transport_compose] which seems to come up a lot. -/
definition transport_idmap_ap A (P : A → Type) x y (p : x = y) (u : P x)
: transport P p u = transport idmap (ap P p) u :=
     match p with refl => refl end.

/- Sometimes, it's useful to have the goal be in terms of [ap], so we can use lemmas about [ap].  However, we can't just [rewrite !transport_idmap_ap], as that's likely to loop.  So, instead, we provide a tactic [transport_to_ap], that replaces all [transport P p u] with [transport idmap (ap P p) u] for non-[idmap] [P]. -/
Ltac transport_to_ap :=
  repeat match goal with
           | [ |- context[transport ?P ?p ?u] ]
             => match P with
                  | idmap => fail 1 /- we don't want to turn [transport idmap (ap _ _)] into [transport idmap (ap idmap (ap _ _))] -/
                  | _ => idtac
                end;
               progress rewrite (transport_idmap_ap _ P _ _ p u)
         end.

/- The behavior of [ap] and [apD]. -/

/- In a constant fibration, [apD] reduces to [ap], modulo [transport_const]. -/
definition apD_const {A B} {x y : A} (f : A → B) (p: x = y) :
  apD f p = transport_const p (f x) ⬝ ap f p.
/-begin
  destruct p; reflexivity.
end-/

/- The 2-dimensional groupoid structure -/

/- Horizontal composition of 2-dimensional paths. -/
definition concat2 {A} {x y z : A} {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q')
  : p ⬝ q = p' ⬝ q' :=
   match h, h' with refl, refl => 1 end.

Notation "p @@ q" := (concat2 p q)%path (at level 20) : path_scope.

/- 2-dimensional path inversion -/
definition inverse2 {A : Type} {x y : A} {p q : x = y} (h : p = q)
  : p⁻¹ = q⁻¹ :=
   match h with refl => 1 end.

/- Whiskering -/

definition whiskerL {A : Type} {x y z : A} (p : x = y)
  {q r : y = z} (h : q = r) : p ⬝ q = p ⬝ r :=
   1 @@ h.

definition whiskerR {A : Type} {x y z : A} {p q : x = y}
  (h : p = q) (r : y = z) : p ⬝ r = q ⬝ r :=
   h @@ 1.

/- Unwhiskering, a.k.a. cancelling. -/

definition cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
: (p ⬝ q = p ⬝ r) → (q = r) :=
   λh, (concat_V_con p q)⁻¹ ⬝ whiskerL p⁻¹ h ⬝ (concat_V_con p r).

definition cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p ⬝ r = q ⬝ r) → (p = q) :=
   λh, (concat_con_V p r)⁻¹ ⬝ whiskerR h r⁻¹ ⬝ (concat_con_V q r).

/- Whiskering and identity paths. -/

definition whisker_right_p1 {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  (concat_p1 p) ⁻¹ ⬝ whiskerR h 1 ⬝ concat_p1 q = h :=
    
  match h with refl =>
    match p with refl =>
      1
    end end.

definition whisker_right_1p {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  whiskerR 1 q = 1 :> (p ⬝ q = p ⬝ q) :=
    
  match q with refl => 1 end.

definition whisker_left_p1 {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  whiskerL p 1 = 1 :> (p ⬝ q = p ⬝ q) :=
    
  match q with refl => 1 end.

definition whisker_left_1p {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  (concat_1p p) ⁻¹ ⬝ whiskerL 1 h ⬝ concat_1p q = h :=
    
  match h with refl =>
    match p with refl =>
      1
    end end.

definition concat2_p1 {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  h @@ 1 = whiskerR h 1 :> (p ⬝ 1 = q ⬝ 1) :=
    
  match h with refl => 1 end.

definition concat2_1p {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  1 @@ h = whiskerL 1 h :> (1 ⬝ p = 1 ⬝ q) :=
    
  match h with refl => 1 end.

/- Whiskering and composition -/

/- The naming scheme for these is a little unclear; should [pp] refer to concatenation of the 2-paths being whiskered or of the paths we are whiskering by? -/
definition whisker_left_con {A} {x y z : A} (p : x = y) {q q' q'' : y = z}
           (r : q = q') (s : q' = q'')
: whiskerL p (r ⬝ s) = whiskerL p r ⬝ whiskerL p s.
/-begin
  destruct p, r, s; reflexivity.
end-/

definition whisker_right_con {A} {x y z : A} {p p' p'' : x = y} (q : y = z)
           (r : p = p') (s : p' = p'')
: whiskerR (r ⬝ s) q = whiskerR r q ⬝ whiskerR s q.
/-begin
  destruct q, r, s; reflexivity.
end-/

/- For now, I've put an [L] or [R] to mark when we're referring to the whiskering paths. -/
definition whisker_left_VpL {A} {x y z : A} (p : x = y)
           {q q' : y = z} (r : q = q')
: (concat_V_con p q)⁻¹ ⬝ whiskerL p⁻¹ (whiskerL p r) ⬝ concat_V_con p q'
  = r.
/-begin
  destruct p, r, q. reflexivity.
end-/

definition whisker_left_pVL {A} {x y z : A} (p : y = x)
           {q q' : y = z} (r : q = q')
: (concat_p_Vp p q)⁻¹ ⬝ whiskerL p (whiskerL p⁻¹ r) ⬝ concat_p_Vp p q'
  = r.
/-begin
  destruct p, r, q. reflexivity.
end-/

definition whisker_right_pVR {A} {x y z : A} {p p' : x = y}
           (r : p = p') (q : y = z)
: (concat_con_V p q)⁻¹ ⬝ whiskerR (whiskerR r q) q⁻¹ ⬝ concat_con_V p' q
  = r.
/-begin
  destruct p, r, q. reflexivity.
end-/

definition whisker_right_VpR {A} {x y z : A} {p p' : x = y}
           (r : p = p') (q : z = y)
: (concat_pV_p p q)⁻¹ ⬝ whiskerR (whiskerR r q⁻¹) q ⬝ concat_pV_p p' q
  = r.
/-begin
  destruct p, r, q. reflexivity.
end-/

/- The interchange law for concatenation. -/
definition concat_concat2 {A : Type} {x y z : A} {p p' p'' : x = y} {q q' q'' : y = z}
  (a : p = p') (b : p' = p'') (c : q = q') (d : q' = q'') :
  (a @@ c) ⬝ (b @@ d) = (a ⬝ b) @@ (c ⬝ d).
/-begin
  case d.
  case c.
  case b.
  case a.
  reflexivity.
end-/

/- The interchange law for whiskering.  Special case of [concat_concat2]. -/
definition concat_whisker {A} {x y z : A} (p p' : x = y) (q q' : y = z) (a : p = p') (b : q = q') :
  (whiskerR a q) ⬝ (whiskerL p' b) = (whiskerL p b) ⬝ (whiskerR a q') :=
    
  match b with
    refl =>
    match a with refl =>
      (concat_1p _)⁻¹
    end
  end.

/- Structure corresponding to the coherence equations of a bicategory. -/

/- The "pentagonator": the 3-cell witnessing the associativity pentagon. -/
definition pentagon {A : Type} {v w x y z : A} (p : v = w) (q : w = x) (r : x = y) (s : y = z)
  : whiskerL p (concat_p_con q r s)
      ⬝ concat_p_con p (q@r) s
      ⬝ whiskerR (concat_p_con p q r) s
  = concat_p_con p q (r@s) ⬝ concat_p_con (p@q) r s.
/-begin
  case p, q, r, s.  reflexivity.
end-/

/- The 3-cell witnessing the left unit triangle. -/
definition triangulator {A : Type} {x y z : A} (p : x = y) (q : y = z)
  : concat_p_con p 1 q ⬝ whiskerR (concat_p1 p) q
  = whiskerL p (concat_1p q).
/-begin
  case p, q.  reflexivity.
end-/

/- The Eckmann-Hilton argument -/
definition eckmann_hilton {A : Type} {x:A} (p q : 1 = 1 :> (x = x)) : p ⬝ q = q ⬝ p :=
  (whisker_right_p1 p @@ whisker_left_1p q)⁻¹
  ⬝ (concat_p1 _ @@ concat_p1 _)
  ⬝ (concat_1p _ @@ concat_1p _)
  ⬝ (concat_whisker _ _ _ _ p q)
  ⬝ (concat_1p _ @@ concat_1p _)⁻¹
  ⬝ (concat_p1 _ @@ concat_p1 _)⁻¹
  ⬝ (whisker_left_1p q @@ whisker_right_p1 p).

/- The action of functions on 2-dimensional paths -/

definition ap02 {A B : Type} (f:A->B) {x y:A} {p q:x=y} (r:p=q) : ap f p = ap f q :=
     match r with refl => 1 end.

definition ap02_con {A B} (f:A->B) {x y:A} {p p' p'':x=y} (r:p=p') (r':p'=p'')
  : ap02 f (r ⬝ r') = ap02 f r ⬝ ap02 f r'.
/-begin
  case r, r'; reflexivity.
end-/

definition ap02_p2p {A B} (f:A->B) {x y z:A} {p p':x=y} {q q':y=z} (r:p=p') (s:q=q')
  : ap02 f (r @@ s) =   ap_con f p q
                      ⬝ (ap02 f r  @@  ap02 f s)
                      ⬝ (ap_con f p' q')⁻¹.
/-begin
  case r, s, p, q. reflexivity.
end-/

definition apD02 {A : Type} {B : A → Type} {x y : A} {p q : x = y}
  (f : Πx, B x) (r : p = q)
  : apD f p = transport2 B r (f x) ⬝ apD f q :=
     match r with refl => (concat_1p _)⁻¹ end.

/- And now for a lemma whose statement is much longer than its proof. -/
definition apD02_con {A} (B : A → Type) (f : Πx:A, B x) {x y : A}
  {p1 p2 p3 : x = y} (r1 : p1 = p2) (r2 : p2 = p3)
  : apD02 f (r1 ⬝ r2)
  = apD02 f r1
  ⬝ whiskerL (transport2 B r1 (f x)) (apD02 f r2)
  ⬝ concat_p_con _ _ _
  ⬝ (whiskerR (transport2_p2p B r1 r2 (f x))⁻¹ (apD f p3)).
/-begin
  destruct r1, r2. destruct p1. reflexivity.
end-/

/- This lemma needs a better name. -/
definition ap_transport_Vp {A B} (p q : A = B) (r : q = p) (z : A)
: ap (transport idmap q⁻¹) (ap (λs, transport idmap s z) r)
  ⬝ ap (λs, transport idmap s (p ▹ z)) (inverse2 r)
  ⬝ transport_Vp idmap p z
  = transport_Vp idmap q z.
/-begin
  by path_induction.
end-/

/- Tactics, hints, and aliases -/

/- [concat], with arguments flipped. Useful mainly in the idiom [apply (concatR (expression))]. Given as a notation not a definition so that the resultant terms are literally instances of [concat], with no unfolding required. -/
Notation concatR := (λp q, concat q p).

Hint Resolve
  concat_1p concat_p1 concat_p_con
  inv_con inv_V
 : path_hints.

/- First try at a paths db
We want the RHS of the equation to become strictly simpler -/
Hint Rewrite
@concat_p1
@concat_1p
@concat_p_con /- there is a choice here !-/
@concat_pV
@concat_Vp
@concat_V_con
@concat_p_Vp
@concat_con_V
@concat_pV_p
(*@inv_con*) /- I am not sure about this one -/
@inv_V
@moveR_Mp
@moveR_pM
@moveL_Mp
@moveL_pM
@moveL_1M
@moveL_M1
@moveR_M1
@moveR_1M
@ap_1
/- @ap_con
@ap_p_con ?-/
@inverse_ap
@ap_idmap
/- @ap_compose
@ap_compose'-/
@ap_const
/- Unsure about naturality of [ap], was absent in the old implementation-/
@apD10_1
:paths.

Ltac hott_simpl :=
  autorewrite with paths in × |- × ; auto with path_hints.
