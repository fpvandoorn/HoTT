/- -*- mode: coq; mode: visual-line -*- -/
/- Theorems about path spaces -/

Require Import HoTT.Basics.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables A B f x y z.

/- Path spaces -/

/- The path spaces of a path space are not, of course, determined; they are just the
    higher-dimensional structure of the original space. -/

/- Transporting in path spaces.

   There are potentially a lot of these lemmas, so we adopt a uniform naming scheme:

   - `l` means the left endpoint varies
   - `r` means the right endpoint varies
   - `F` means application of a function to that (varying) endpoint.
-/

definition transport_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y)
  : transport (λx, x = y) p q = p⁻¹ ⬝ q.
/-begin
  destruct p, q; reflexivity.
end-/

definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  : transport (λy, x = y) p q = q ⬝ p.
/-begin
  destruct p, q; reflexivity.
end-/

definition transport_paths_lr {A : Type} {x1 x2 : A} (p : x1 = x2) (q : x1 = x1)
  : transport (λx, x = x) p q = p⁻¹ ⬝ q ⬝ p.
/-begin
  destruct p; simpl.
  exact ((concat_1p q)⁻¹ ⬝ (concat_p1 (1 ⬝ q))⁻¹).
end-/

definition transport_paths_Fl {A B : Type} {f : A → B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y)
  : transport (λx, f x = y) p q = (ap f p)⁻¹ ⬝ q.
/-begin
  destruct p, q; reflexivity.
end-/

definition transport_paths_Fr {A B : Type} {g : A → B} {y1 y2 : A} {x : B}
  (p : y1 = y2) (q : x = g y1)
  : transport (λy, x = g y) p q = q ⬝ (ap g p).
/-begin
  destruct p. apply symmetry. apply concat_p1.
end-/

definition transport_paths_FlFr {A B : Type} {f g : A → B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1)
  : transport (λx, f x = g x) p q = (ap f p)⁻¹ ⬝ q ⬝ (ap g p).
/-begin
  destruct p; simpl.
  exact ((concat_1p q)⁻¹ ⬝ (concat_p1 (1 ⬝ q))⁻¹).
end-/

definition transport_paths_FlFr_D {A : Type} {B : A → Type}
  {f g : Πa, B a} {x1 x2 : A} (p : x1 = x2) (q : f x1 = g x1)
: transport (λx, f x = g x) p q
  = (apD f p)⁻¹ ⬝ ap (transport B p) q ⬝ (apD g p).
/-begin
  destruct p; simpl.
  exact ((ap_idmap _)⁻¹ ⬝ (concat_1p _)⁻¹ ⬝ (concat_p1 _)⁻¹).
end-/

definition transport_paths_FFlr {A B : Type} {f : A → B} {g : B → A} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = x1)
  : transport (λx, g (f x) = x) p q = (ap g (ap f p))⁻¹ ⬝ q ⬝ p.
/-begin
  destruct p; simpl.
  exact ((concat_1p q)⁻¹ ⬝ (concat_p1 (1 ⬝ q))⁻¹).
end-/

definition transport_paths_lFFr {A B : Type} {f : A → B} {g : B → A} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = g (f x1))
  : transport (λx, x = g (f x)) p q = p⁻¹ ⬝ q ⬝ (ap g (ap f p)).
/-begin
  destruct p; simpl.
  exact ((concat_1p q)⁻¹ ⬝ (concat_p1 (1 ⬝ q))⁻¹).
end-/


/- Functorial action -/

/- 'functor_path' is called [ap]. -/

/- Equivalences between path spaces -/

/- [isequiv_ap] is in Equivalences.v  -/

definition equiv_ap `(f : A → B) [H : is_equiv A B f] (x y : A)
  : (x = y) ≃ (f x = f y) :=
     equiv.mk _ _ (ap f) _.

/- TODO: Is this really necessary? -/
definition equiv_inj `(f : A → B) [H : is_equiv A B f] {x y : A}
  : (f x = f y) → (x = y) :=
     (ap f)⁻¹.

/- Path operations are equivalences -/

definition isequiv_path_inverse [instance] {A : Type} (x y : A)
  : is_equiv (@inverse A x y) | 0 :=
     is_equiv.mk _ _ _ (@inverse A y x) (@inv_V A y x) (@inv_V A x y) _.
/-begin
  intros p; destruct p; reflexivity.
end-/

definition equiv_path_inverse {A : Type} (x y : A)
  : (x = y) ≃ (y = x) :=
     equiv.mk _ _ (@inverse A x y) _.

definition isequiv_concat_l [instance] {A : Type} `(p : x = y:>A) (z : A)
  : is_equiv (@transitivity A _ _ x y z p) | 0 :=
     is_equiv.mk _ _ _ (concat p⁻¹)
     (concat_p_Vp p) (concat_V_pp p) _.
/-begin
  intros q; destruct p; destruct q; reflexivity.
end-/

definition equiv_concat_l {A : Type} `(p : x = y) (z : A)
  : (y = z) ≃ (x = z) :=
     equiv.mk _ _ (concat p) _.

definition isequiv_concat_r [instance] {A : Type} `(p : y = z) (x : A)
  : is_equiv (λq:x=y, q ⬝ p) | 0 :=
     is_equiv.mk _ _ (λq, q ⬝ p) (λq, q ⬝ p⁻¹)
     (λq, concat_pV_p q p) (λq, concat_pp_V q p) _.
/-begin
  intros q; destruct p; destruct q; reflexivity.
end-/

definition equiv_concat_r {A : Type} `(p : y = z) (x : A)
  : (x = y) ≃ (x = z) :=
     equiv.mk _ _ (λq, q ⬝ p) _.

definition isequiv_concat_lr [instance] {A : Type} {x x' y y' : A} (p : x' = x) (q : y = y')
  : is_equiv (λr:x=y, p ⬝ r ⬝ q) | 0 :=
     @isequiv_compose _ _ (λr, p ⬝ r) _ _ (λr, r ⬝ q) _.

definition equiv_concat_lr {A : Type} {x x' y y' : A} (p : x' = x) (q : y = y')
  : (x = y) ≃ (x' = y') :=
     equiv.mk _ _ (λr:x=y, p ⬝ r ⬝ q) _.

definition isequiv_whiskerL [instance] {A} {x y z : A} (p : x = y) {q r : y = z}
: is_equiv (@whiskerL A x y z p q r).
/-begin
  refine (isequiv_adjointify _ _ _ _).
  - apply cancelL.
  - intros k. unfold cancelL.
    rewrite !whiskerL_pp.
    refine ((_ @@ 1 @@ _) ⬝ whiskerL_pVL p k).
    + destruct p, q; reflexivity.
    + destruct p, r; reflexivity.
  - intros k. unfold cancelL.
    refine ((_ @@ 1 @@ _) ⬝ whiskerL_VpL p k).
    + destruct p, q; reflexivity.
    + destruct p, r; reflexivity.
end-/

definition equiv_whiskerL {A} {x y z : A} (p : x = y) (q r : y = z)
: (q = r) ≃ (p ⬝ q = p ⬝ r) :=
     equiv.mk _ _ (whiskerL p) _.

definition equiv_cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
: (p ⬝ q = p ⬝ r) ≃ (q = r) :=
     equiv_inverse (equiv_whiskerL p q r).

definition isequiv_cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
  : is_equiv (cancelL p q r).
/-begin
  change (is_equiv (equiv_cancelL p q r)); exact _.
end-/

definition isequiv_whiskerR [instance] {A} {x y z : A} {p q : x = y} (r : y = z)
: is_equiv (λh, @whiskerR A x y z p q h r).
/-begin
  refine (isequiv_adjointify _ _ _ _).
  - apply cancelR.
  - intros k. unfold cancelR.
    rewrite !whiskerR_pp.
    refine ((_ @@ 1 @@ _) ⬝ whiskerR_VpR k r).
    + destruct p, r; reflexivity.
    + destruct q, r; reflexivity.
  - intros k. unfold cancelR.
    refine ((_ @@ 1 @@ _) ⬝ whiskerR_pVR k r).
    + destruct p, r; reflexivity.
    + destruct q, r; reflexivity.
end-/

definition equiv_whiskerR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p = q) ≃ (p ⬝ r = q ⬝ r) :=
     equiv.mk _ _ (λh, whiskerR h r) _.

definition equiv_cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p ⬝ r = q ⬝ r) ≃ (p = q) :=
     equiv_inverse (equiv_whiskerR p q r).

definition isequiv_cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
  : is_equiv (cancelR p q r).
/-begin
  change (is_equiv (equiv_cancelR p q r)); exact _.
end-/

/- We can use these to build up more complicated equivalences.

In particular, all of the [move] family are equivalences.

(Note: currently, some but not all of these [isequiv_] lemmas have corresponding [equiv_] lemmas.  Also, they do *not* currently contain the computational content that e.g. the inverse of [moveR_Mp] is [moveL_Vp]; perhaps it would be useful if they did? -/

Global Instance isequiv_moveR_Mp
 {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: is_equiv (moveR_Mp p q r).
/-begin
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
end-/

definition equiv_moveR_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (p = r⁻¹ ⬝ q) ≃ (r ⬝ p = q) :=
   equiv.mk _ _ (moveR_Mp p q r) _.

Global Instance isequiv_moveR_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: is_equiv (moveR_pM p q r).
/-begin
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
end-/

definition equiv_moveR_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (r = q ⬝ p⁻¹) ≃ (r ⬝ p = q) :=
   equiv.mk _ _ (moveR_pM p q r) _.

Global Instance isequiv_moveR_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: is_equiv (moveR_Vp p q r).
/-begin
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
end-/

definition equiv_moveR_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: (p = r ⬝ q) ≃ (r⁻¹ ⬝ p = q) :=
   equiv.mk _ _ (moveR_Vp p q r) _.

Global Instance isequiv_moveR_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: is_equiv (moveR_pV p q r).
/-begin
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
end-/

definition equiv_moveR_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: (r = q ⬝ p) ≃ (r ⬝ p⁻¹ = q) :=
   equiv.mk _ _ (moveR_pV p q r) _.

Global Instance isequiv_moveL_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: is_equiv (moveL_Mp p q r).
/-begin
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
end-/

definition equiv_moveL_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (r⁻¹ ⬝ q = p) ≃ (q = r ⬝ p) :=
   equiv.mk _ _ (moveL_Mp p q r) _.

definition isequiv_moveL_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: is_equiv (moveL_pM p q r).
/-begin
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
end-/

definition equiv_moveL_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  q ⬝ p⁻¹ = r ≃ q = r ⬝ p :=
     equiv.mk _ _ _ (isequiv_moveL_pM p q r).

Global Instance isequiv_moveL_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: is_equiv (moveL_Vp p q r).
/-begin
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
end-/

definition equiv_moveL_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: r ⬝ q = p ≃ q = r⁻¹ ⬝ p :=
   equiv.mk _ _ (moveL_Vp p q r) _.

Global Instance isequiv_moveL_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: is_equiv (moveL_pV p q r).
/-begin
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
end-/

definition equiv_moveL_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: q ⬝ p = r ≃ q = r ⬝ p⁻¹ :=
   equiv.mk _ _ (moveL_pV p q r) _.

definition isequiv_moveL_1M {A : Type} {x y : A} (p q : x = y)
: is_equiv (moveL_1M p q).
/-begin
  destruct q. apply isequiv_concat_l.
end-/

definition isequiv_moveL_M1 {A : Type} {x y : A} (p q : x = y)
: is_equiv (moveL_M1 p q).
/-begin
  destruct q. apply isequiv_concat_l.
end-/

definition isequiv_moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
: is_equiv (moveL_1V p q).
/-begin
  destruct q. apply isequiv_concat_l.
end-/

definition isequiv_moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
: is_equiv (moveL_V1 p q).
/-begin
  destruct q. apply isequiv_concat_l.
end-/

definition isequiv_moveR_M1 {A : Type} {x y : A} (p q : x = y)
: is_equiv (moveR_M1 p q).
/-begin
  destruct p. apply isequiv_concat_r.
end-/

definition isequiv_moveR_1M {A : Type} {x y : A} (p q : x = y)
: is_equiv (moveR_1M p q).
/-begin
  destruct p. apply isequiv_concat_r.
end-/

definition isequiv_moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
: is_equiv (moveR_1V p q).
/-begin
  destruct p. apply isequiv_concat_r.
end-/

definition isequiv_moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
: is_equiv (moveR_V1 p q).
/-begin
  destruct p. apply isequiv_concat_r.
end-/

definition isequiv_moveR_transport_p [instance] {A : Type} (P : A → Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: is_equiv (moveR_transport_p P p u v).
/-begin
  destruct p. apply isequiv_idmap.
end-/

definition equiv_moveR_transport_p {A : Type} (P : A → Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: u = transport P p⁻¹ v ≃ transport P p u = v :=
   equiv.mk _ _ (moveR_transport_p P p u v) _.

definition isequiv_moveR_transport_V [instance] {A : Type} (P : A → Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: is_equiv (moveR_transport_V P p u v).
/-begin
  destruct p. apply isequiv_idmap.
end-/

definition equiv_moveR_transport_V {A : Type} (P : A → Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: u = transport P p v ≃ transport P p⁻¹ u = v :=
   equiv.mk _ _ (moveR_transport_V P p u v) _.

definition isequiv_moveL_transport_V [instance] {A : Type} (P : A → Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: is_equiv (moveL_transport_V P p u v).
/-begin
  destruct p. apply isequiv_idmap.
end-/

definition equiv_moveL_transport_V {A : Type} (P : A → Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: transport P p u = v ≃ u = transport P p⁻¹ v :=
   equiv.mk _ _ (moveL_transport_V P p u v) _.

definition isequiv_moveL_transport_p [instance] {A : Type} (P : A → Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: is_equiv (moveL_transport_p P p u v).
/-begin
  destruct p. apply isequiv_idmap.
end-/

definition equiv_moveL_transport_p {A : Type} (P : A → Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: transport P p⁻¹ u = v ≃ u = transport P p v :=
   equiv.mk _ _ (moveL_transport_p P p u v) _.

definition isequiv_moveR_equiv_M [instance] [H : is_equiv A B f] (x : A) (y : B)
: is_equiv (@moveR_equiv_M A B f _ x y).
/-begin
  unfold moveR_equiv_M.
  refine (@isequiv_compose _ _ (ap f) _ _ (λq, q ⬝ retr f y) _).
end-/

definition equiv_moveR_equiv_M [H : is_equiv A B f] (x : A) (y : B)
  : (x = f⁻¹ y) ≃ (f x = y) :=
     equiv.mk _ _ (@moveR_equiv_M A B f _ x y) _.

definition isequiv_moveR_equiv_V [instance] [H : is_equiv A B f] (x : B) (y : A)
: is_equiv (@moveR_equiv_V A B f _ x y).
/-begin
  unfold moveR_equiv_V.
  refine (@isequiv_compose _ _ (ap f⁻¹) _ _ (λq, q ⬝ sect f y) _).
end-/

definition equiv_moveR_equiv_V [H : is_equiv A B f] (x : B) (y : A)
  : (x = f y) ≃ (f⁻¹ x = y) :=
     equiv.mk _ _ (@moveR_equiv_V A B f _ x y) _.

definition isequiv_moveL_equiv_M [instance] [H : is_equiv A B f] (x : A) (y : B)
: is_equiv (@moveL_equiv_M A B f _ x y).
/-begin
  unfold moveL_equiv_M.
  refine (@isequiv_compose _ _ (ap f) _ _ (λq, (retr f y)⁻¹ ⬝ q) _).
end-/

definition equiv_moveL_equiv_M [H : is_equiv A B f] (x : A) (y : B)
  : (f⁻¹ y = x) ≃ (y = f x) :=
     equiv.mk _ _ (@moveL_equiv_M A B f _ x y) _.

definition isequiv_moveL_equiv_V [instance] [H : is_equiv A B f] (x : B) (y : A)
: is_equiv (@moveL_equiv_V A B f _ x y).
/-begin
  unfold moveL_equiv_V.
  refine (@isequiv_compose _ _ (ap f⁻¹) _ _ (λq, (sect f y)⁻¹ ⬝ q) _).
end-/

definition equiv_moveL_equiv_V [H : is_equiv A B f] (x : B) (y : A)
  : (f y = x) ≃ (y = f⁻¹ x) :=
     equiv.mk _ _ (@moveL_equiv_V A B f _ x y) _.

/- Dependent paths -/

/- Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 = y2] in [P x2].  However, when [P] is a path space, these dependent paths have a more convenient description: rather than transporting the left side both forwards and backwards, we transport both sides of the equation forwards, forming a sort of "naturality square".

   We use the same naming scheme as for the transport lemmas. -/

definition dpath_path_l {A : Type} {x1 x2 y : A}
  (p : x1 = x2) (q : x1 = y) (r : x2 = y)
  : q = p ⬝ r
  ≃
  transport (λx, x = y) p q = r.
/-begin
  destruct p; simpl.
  exact (equiv_concat_r (concat_1p r) q).
end-/

definition dpath_path_r {A : Type} {x y1 y2 : A}
  (p : y1 = y2) (q : x = y1) (r : x = y2)
  : q ⬝ p = r
  ≃
  transport (λy, x = y) p q = r.
/-begin
  destruct p; simpl.
  exact (equiv_concat_l (concat_p1 q)⁻¹ r).
end-/

definition dpath_path_lr {A : Type} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = x1) (r : x2 = x2)
  : q ⬝ p = p ⬝ r
  ≃
  transport (λx, x = x) p q = r.
/-begin
  destruct p; simpl.
  refine (equiv_compose' (B := (q ⬝ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)⁻¹ r).
  exact (equiv_concat_r (concat_1p r) (q ⬝ 1)).
end-/

definition dpath_path_Fl {A B : Type} {f : A → B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y) (r : f x2 = y)
  : q = ap f p ⬝ r
  ≃
  transport (λx, f x = y) p q = r.
/-begin
  destruct p; simpl.
  exact (equiv_concat_r (concat_1p r) q).
end-/

definition dpath_path_Fr {A B : Type} {g : A → B} {x : B} {y1 y2 : A}
  (p : y1 = y2) (q : x = g y1) (r : x = g y2)
  : q ⬝ ap g p = r
  ≃
  transport (λy, x = g y) p q = r.
/-begin
  destruct p; simpl.
  exact (equiv_concat_l (concat_p1 q)⁻¹ r).
end-/

definition dpath_path_FlFr {A B : Type} {f g : A → B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1) (r : f x2 = g x2)
  : q ⬝ ap g p = ap f p ⬝ r
  ≃
  transport (λx, f x = g x) p q = r.
/-begin
  destruct p; simpl.
  refine (equiv_compose' (B := (q ⬝ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)⁻¹ r).
  exact (equiv_concat_r (concat_1p r) (q ⬝ 1)).
end-/

definition dpath_path_FFlr {A B : Type} {f : A → B} {g : B → A}
  {x1 x2 : A} (p : x1 = x2) (q : g (f x1) = x1) (r : g (f x2) = x2)
  : q ⬝ p = ap g (ap f p) ⬝ r
  ≃
  transport (λx, g (f x) = x) p q = r.
/-begin
  destruct p; simpl.
  refine (equiv_compose' (B := (q ⬝ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)⁻¹ r).
  exact (equiv_concat_r (concat_1p r) (q ⬝ 1)).
end-/

definition dpath_path_lFFr {A B : Type} {f : A → B} {g : B → A}
  {x1 x2 : A} (p : x1 = x2) (q : x1 = g (f x1)) (r : x2 = g (f x2))
  : q ⬝ ap g (ap f p) = p ⬝ r
  ≃
  transport (λx, x = g (f x)) p q = r.
/-begin
  destruct p; simpl.
  refine (equiv_compose' (B := (q ⬝ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)⁻¹ r).
  exact (equiv_concat_r (concat_1p r) (q ⬝ 1)).
end-/


/- Universal mapping property -/

definition isequiv_paths_ind [instance] [H : funext] {A : Type} (a : A)
  (P : Πx, (a = x) → Type)
  : is_equiv (paths_ind a P) | 0 :=
     isequiv_adjointify (paths_ind a P) (λf, f a 1) _ _.
/-begin
  - intros f.
    apply path_forall; intros x.
    apply path_forall; intros p.
    destruct p; reflexivity.
  - intros u. reflexivity.
end-/

definition equiv_paths_ind [H : funext] {A : Type} (a : A)
  (P : Πx, (a = x) → Type)
  : P a 1 ≃ Πx p, P x p :=
     equiv.mk _ _ (paths_ind a P) _.

/- Truncation -/

/- Paths reduce truncation level by one.  This is essentially the definition of [IsTrunc_internal]. -/
