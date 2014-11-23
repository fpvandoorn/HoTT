/- -*- mode: coq; mode: visual-line -*-  -/
/- Truncatedness -/

Require Import Overture PathGroupoids Contractible Equivalences.
Local Open Scope equiv_scope.
Local Open Scope trunc_scope.
Local Open Scope path_scope.
Generalizable Variables A B m n f.

/- Arithmetic on truncation-levels. -/

Fixpoint trunc_index_add (m n : trunc_index) : trunc_index :=
     match m with
       | -2 => n
       | m'.+1 => (trunc_index_add m' n).+1
     end.

Notation "m -2+ n" := (trunc_index_add m n) (at level 50, left associativity) : trunc_scope.

Fixpoint trunc_index_leq (m n : trunc_index) : Type :=
     match m, n with
       | -2, _ => unit
       | m'.+1, -2 => Empty
       | m'.+1, n'.+1 => trunc_index_leq m' n'
     end.

Notation "m <= n" := (trunc_index_leq m n) (at level 70, no associativity) : trunc_scope.

/- Truncatedness proper. -/

/- A contractible space is (-2)-truncated, by definition. -/
definition contr_trunc_minus_two {H : is_trunc -2 A} : is_contr A :=
     H.

/- Truncation levels are cumulative. -/
definition trunc_succ [instance] [H : is_trunc n A] : is_trunc n.+1 A | 1000.
/-begin
  generalize dependent A.
  simple_induction n n IH; simpl; intros A H x y.
  - apply contr_paths_contr.
  - apply IH, H.
Qed.

definition trunc_leq [instance] {m n} (Hmn : m <= n) [H : is_trunc m A] : is_trunc n A | 1000.
Proof.
  generalize dependent A; generalize dependent m.
  simple_induction n n' IH;
    intros [ | m'] Hmn A ? .
  - /- -2, -2 -/ assumption.
  - /- S m', -2 -/ destruct Hmn.
  - /- -2, S n' -/ apply @trunc_succ, (IH -2); auto.
  - /- S m', S n' -/ intros x y; apply (IH m');
                     auto with typeclass_instances.
Qed.

/- In particular, a contractible type, hprop, or hset is truncated at all higher levels. -/

definition trunc_contr {n} {A} [H : is_contr A] : is_trunc n A :=
     (@trunc_leq -2 n star _ _).

definition trunc_hprop {n} {A} [H : is_hprop A] : is_trunc n.+1 A :=
     (@trunc_leq -1 n.+1 star _ _).

definition trunc_hset {n} {A} [H : IsHSet A] : is_trunc n.+1.+1 A :=
     (@trunc_leq 0 n.+1.+1 star _ _).

/- Consider the preceding definitions as instances for typeclass search, but only if the requisite hypothesis is already a known assumption; otherwise they result in long or interminable searches. -/
Hint Immediate trunc_contr : typeclass_instances.
Hint Immediate trunc_hprop : typeclass_instances.
Hint Immediate trunc_hset : typeclass_instances.

/- Equivalence preserves truncation (this is, of course, trivial with univalence).
   This is not an [Instance] because it causes infinite loops.
   -/
definition trunc_equiv A {B} (f : A → B)
  [H : is_trunc n A] [H : IsEquiv A B f]
  : is_trunc n B.
Proof.
  generalize dependent B; generalize dependent A.
  simple_induction n n IH; simpl; intros A ? B f ?.
  - exact (contr_equiv _ f).
  - intros x y.
    exact (IH (f⁻¹ x ≈ f⁻¹ y) (H (f⁻¹ x) (f⁻¹ y)) (x ≈ y) ((ap (f⁻¹))⁻¹) _).
Qed.

definition trunc_equiv' A {B} (f : A ≃ B) [H : is_trunc n A]
  : is_trunc n B :=
     trunc_equiv A f.

/- Truncated morphisms -/

Class IsTruncMap (n : trunc_index) {X Y : Type} (f : X → Y) :=
  istruncmap_fiber : Πy:Y, is_trunc n (hfiber f y).

Global Existing Instance istruncmap_fiber.

Notation IsEmbedding := (IsTruncMap -1).

/- Universes of truncated types -/

/- It is convenient for some purposes to consider the universe of all n-truncated types (within a given universe of types).  In particular, this allows us to state the important fact that each such universe is itself (n+1)-truncated. -/

Record TruncType (n : trunc_index) := BuildTruncType {
  trunctype_type : Type ;
  istrunc_trunctype_type : is_trunc n trunctype_type
}.
/- Note: the naming of the second constructor is more than a little clunky.  However, the more obvious [istrunc_trunctype] is taken by the theorem below, that [IsTrunc n.+1 (TruncType n)], which seems to have an even better claim to it. -/

Arguments BuildTruncType _ _ {_}.
Arguments trunctype_type {_} _.
Arguments istrunc_trunctype_type [_] _.

Coercion trunctype_type : TruncType >-> Sortclass.
Global Existing Instance istrunc_trunctype_type.

Notation "n -Type" := (TruncType n) (at level 1) : type_scope.
Notation hProp := (-1)-Type.
Notation hSet := 0-Type.

Notation BuildhProp := (BuildTruncType -1).
Notation BuildhSet := (BuildTruncType 0).

/- This is (as of October 2014) the only [Canonical Structure] in the library.  It would be nice to do without it, in the interests of minimizing the number of fancy Coq features that the reader needs to know about. -/
Canonical Structure default_TruncType := λn T P, (@BuildTruncType n T P).

/- Facts about hprops -/

/- An inhabited proposition is contractible.
   This is not an [Instance] because it causes infinite loops.
   -/
definition contr_inhabited_hprop (A : Type) {H : is_hprop A} (x : A)
  : is_contr A.
Proof.
  exists x.
  intro y.
  apply center, H.
end-/

/- If inhabitation implies contractibility, then we have an h-proposition.  We probably won't often have a hypothesis of the form [A → is_contr A], so we make sure we give priority to other instances. -/
definition hprop_inhabited_contr [instance] (A : Type) : (A → is_contr A) → is_hprop A | 10000.
/-begin
  intros H x y.
  pose (C := H x).
  apply contr_paths_contr.
end-/

/- Any two points in an hprop are connected by a path. -/
definition path_ishprop {H : is_hprop A} : Πx y : A, x ≈ y.
/-begin
  apply H.
end-/

/- Conversely, this property characterizes hprops. -/
definition hprop_allpath (A : Type) : (Π(x y : A), x ≈ y) → is_hprop A.
  intros H x y.
  pose (C := BuildContr A x (H x)).
  apply contr_paths_contr.
Defined.

/- Two propositions are equivalent as soon as there are maps in both directions. -/
definition isequiv_iff_hprop [H : is_hprop A] [H : is_hprop B]
  (f : A → B) (g : B → A)
: IsEquiv f.
/-begin
  apply (isequiv_adjointify f g);
    intros ?; apply path_ishprop.
end-/

definition equiv_iff_hprop_uncurried [H : is_hprop A] [H : is_hprop B]
  : (A <-> B) → (A ≃ B).
/-begin
  intros [f g].
  apply (equiv_adjointify f g);
    intros ?; apply path_ishprop.
end-/

definition equiv_iff_hprop [H : is_hprop A] [H : is_hprop B]
  : (A → B) → (B → A) → (A ≃ B) :=
     λf g, equiv_iff_hprop_uncurried (f, g).

/- Hedberg's theorem: any type with decidable equality is a set. -/

Class WeaklyConstant {A B} (f : A → B) :=
  wconst : Πx y, f x ≈ f y.

Class Collapsible (A : Type) :=
  { collapse : A → A ;
    wconst_collapse : WeaklyConstant collapse
  }.
Global Existing Instance wconst_collapse.

Class PathCollapsible (A : Type) :=
  path_coll : Π(x y : A), Collapsible (x ≈ y).
Global Existing Instance path_coll.

definition collapsible_decidable [instance] (A : Type) [H : Decidable A]
: Collapsible A.
/-begin
  destruct (dec A) as [a | na].
  - exists (const a).
    intros x y; reflexivity.
  - exists idmap.
    intros x y; destruct (na x).
end-/

definition pathcoll_decpaths [instance] (A : Type) [H : DecidablePaths A]
: PathCollapsible A.
/-begin
  intros x y; exact _.
end-/

definition hset_pathcoll [instance] (A : Type) [H : PathCollapsible A]
: IsHSet A.
/-begin
  intros x y.
  assert (h : Πp:x=y, p ≈ (collapse (idpath x))⁻¹ ⬝ collapse p).
  { intros []; symmetry; by apply concat_Vp. }
  apply hprop_allpath; intros p q.
  refine (h p ⬝ _ ⬝ (h q)⁻¹).
  apply whiskerL.
  apply wconst.
end-/

definition collapsible_hprop (A : Type) [H : is_hprop A]
: Collapsible A.
/-begin
  exists idmap.
  intros x y; apply path_ishprop.
end-/

definition pathcoll_hset (A : Type) [H : IsHSet A]
: PathCollapsible A.
/-begin
  intros x y; apply collapsible_hprop; exact _.
end-/

Corollary hset_decpaths (A : Type) [H : DecidablePaths A]
: IsHSet A.
/-begin
  exact _.
end-/
