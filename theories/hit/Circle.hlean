/- -*- mode: coq; mode: visual-line -*- -/

/- Theorems about the circle [S¹]. -/

Require Import HoTT.Basics.
Require Import Types.Paths Types.ΠTypes.Arrow Types.Universe Types.Empty Types.unit.
Require Import HSet UnivalenceImpliesfunext.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

/- definition of the circle. -/

Module Export Circle.

Private Inductive S1 : Type1 :=
| base : S1.

Axiom loop : base = base.

definition S1_ind (P : S1 → Type) (b : P base) (l : loop ▹ b = b)
  : Π(x:S1), P x :=
     λx, match x with base => λ_, b end l.

Axiom S1_ind_beta_loop
  : Π(P : S1 → Type) (b : P base) (l : loop ▹ b = b),
  apD (S1_ind P b l) loop = l.

End Circle.

/- The non-dependent eliminator -/

definition S1_rec (P : Type) (b : P) (l : b = b)
  : S1 → P :=
     S1_ind (λ_, P) b (transport_const _ _ ⬝ l).

definition S1_rec_beta_loop (P : Type) (b : P) (l : b = b)
  : ap (S1_rec P b l) loop = l.
/-begin
  unfold S1_rec.
  refine (cancelL (transport_const loop b) _ _ _).
  refine ((apD_const (S1_ind (λ_, P) b _) loop)⁻¹ ⬝ _).
  refine (S1_ind_beta_loop (λ_, P) _ _).
end-/

/- The loop space of the circle is the Integers. -/

/- First we define the appropriate integers. -/

Inductive Pos : Type1 :=
| one : Pos
| succ_pos : Pos → Pos.

definition one_neq_succ_pos (z : Pos) : ~ (one = succ_pos z) :=
     λp, transport (λs, match s with one => unit | succ_pos t => Empty end) p star.

definition succ_pos_injective {z w : Pos} (p : succ_pos z = succ_pos w) : z = w :=
     transport (λs, z = (match s with one => w | succ_pos a => a end)) p (refl z).

Inductive Int : Type1 :=
| neg : Pos → Int
| zero : Int
| pos : Pos → Int.

definition neg_injective {z w : Pos} (p : neg z = neg w) : z = w :=
     transport (λs, z = (match s with neg a => a | zero => w | pos a => w end)) p (refl z).

definition pos_injective {z w : Pos} (p : pos z = pos w) : z = w :=
     transport (λs, z = (match s with neg a => w | zero => w | pos a => a end)) p (refl z).

definition neg_neq_zero {z : Pos} : ~ (neg z = zero) :=
     λp, transport (λs, match s with neg a => z = a | zero => Empty | pos _ => Empty end) p (refl z).

definition pos_neq_zero {z : Pos} : ~ (pos z = zero) :=
     λp, transport (λs, match s with pos a => z = a | zero => Empty | neg _ => Empty end) p (refl z).

definition neg_neq_pos {z w : Pos} : ~ (neg z = pos w) :=
     λp, transport (λs, match s with neg a => z = a | zero => Empty | pos _ => Empty end) p (refl z).

/- And prove that they are a set. -/

definition decpaths_int [instance] : DecidablePaths Int.
/-begin
  intros [n | | n] [m | | m].
  revert m; induction n as [|n IHn]; intros m; induction m as [|m IHm].
  exact (inl 1).
  exact (inr (λp, one_neq_succ_pos _ (neg_injective p))).
  exact (inr (λp, one_neq_succ_pos _ (symmetry _ _ (neg_injective p)))).
  destruct (IHn m) as [p | np].
  exact (inl (ap neg (ap succ_pos (neg_injective p)))).
  exact (inr (λp, np (ap neg (succ_pos_injective (neg_injective p))))).
  exact (inr neg_neq_zero).
  exact (inr neg_neq_pos).
  exact (inr (neg_neq_zero ∘ apply symmetry._ _)).
  exact (inl 1).
  exact (inr (pos_neq_zero ∘ apply symmetry._ _)).
  exact (inr (neg_neq_pos ∘ apply symmetry._ _)).
  exact (inr pos_neq_zero).
  revert m; induction n as [|n IHn]; intros m; induction m as [|m IHm].
  exact (inl 1).
  exact (inr (λp, one_neq_succ_pos _ (pos_injective p))).
  exact (inr (λp, one_neq_succ_pos _ (symmetry _ _ (pos_injective p)))).
  destruct (IHn m) as [p | np].
  exact (inl (ap pos (ap succ_pos (pos_injective p)))).
  exact (inr (λp, np (ap pos (succ_pos_injective (pos_injective p))))).
end-/

definition hset_int [instance] : IsHSet Int | 0.
/-begin
  exact _.
end-/

/- Successor is an autoequivalence of [Int]. -/

definition succ_int (z : Int) : Int :=
     match z with
       | neg (succ_pos n) => neg n
       | neg one => zero
       | zero => pos one
       | pos n => pos (succ_pos n)
     end.

definition pred_int (z : Int) : Int :=
     match z with
       | neg n => neg (succ_pos n)
       | zero => neg one
       | pos one => zero
       | pos (succ_pos n) => pos n
     end.

definition isequiv_succ_int [instance] : is_equiv succ_int | 0 :=
     isequiv_adjointify succ_int pred_int _ _.
/-begin
  intros [[|n] | | [|n]]; reflexivity.
  intros [[|n] | | [|n]]; reflexivity.
end-/

/- Now we do the encode/decode. -/

section AssumeUnivalence
Context [H : Univalence].

definition S1_code : S1 → Type :=
     S1_rec Type Int (path_universe succ_int).

/- Transporting in the codes fibration is the successor autoequivalence. -/

definition transport_S1_code_loop (z : Int)
  : transport S1_code loop z = succ_int z.
/-begin
  refine (transport_compose idmap S1_code loop z ⬝ _).
  unfold S1_code; rewrite S1_rec_beta_loop.
  apply transport_path_universe.
end-/

definition transport_S1_code_loopV (z : Int)
  : transport S1_code loop⁻¹ z = pred_int z.
/-begin
  refine (transport_compose idmap S1_code loop⁻¹ z ⬝ _).
  rewrite ap_V.
  unfold S1_code; rewrite S1_rec_beta_loop.
  rewrite <- (path_universe_V succ_int).
  apply transport_path_universe.
end-/

/- Encode by transporting -/

definition S1_encode (x:S1) : (base = x) → S1_code x :=
     λp, p ▹ zero.

/- Decode by iterating loop. -/

Fixpoint loopexp {A : Type} {x : A} (p : x = x) (n : Pos) : (x = x) :=
     match n with
       | one => p
       | succ_pos n => loopexp p n ⬝ p
     end.

definition looptothe (z : Int) : (base = base) :=
     match z with
       | neg n => loopexp (loop⁻¹) n
       | zero => 1
       | pos n => loopexp (loop) n
     end.

definition S1_decode (x:S1) : S1_code x → (base = x).
/-begin
  revert x; refine (S1_ind (λx, S1_code x → base = x) looptothe _).
  apply path_forall; intros z; simpl in z.
  refine (transport_arrow _ _ _ ⬝ _).
  refine (transport_paths_r loop _ ⬝ _).
  rewrite transport_S1_code_loopV.
  destruct z as [[|n] | | [|n]]; simpl.
  by apply concat_pV_p.
  by apply concat_pV_p.
  by apply concat_Vp.
  by apply concat_1p.
  reflexivity.
end-/

/- The nontrivial part of the proof that decode and encode are equivalences is showing that decoding followed by encoding is the identity on the fibers over [base]. -/

definition S1_encode_looptothe (z:Int)
  : S1_encode base (looptothe z) = z.
/-begin
  destruct z as [n | | n]; unfold S1_encode.
  induction n; simpl in *.
  refine (moveR_transport_V _ loop _ _ _).
  by apply symmetry. apply transport_S1_code_loop.
  rewrite transport_pp.
  refine (moveR_transport_V _ loop _ _ _).
  refine (_ ⬝ (transport_S1_code_loop _)⁻¹).
  assumption.
  reflexivity.
  induction n; simpl in *.
  by apply transport_S1_code_loop.
  rewrite transport_pp.
  refine (moveR_transport_p _ loop _ _ _).
  refine (_ ⬝ (transport_S1_code_loopV _)⁻¹).
  assumption.
end-/

/- Now we put it together. -/

definition S1_encode_isequiv (x:S1) : is_equiv (S1_encode x).
/-begin
  refine (isequiv_adjointify (S1_encode x) (S1_decode x) _ _).
  /- Here we induct on [x:S1].  We just did the case when [x] is [base]. -/
  refine (S1_ind (λx, Sect (S1_decode x) (S1_encode x))
    S1_encode_looptothe _ _).
  /- What remains is easy since [Int] is known to be a set. -/
  by apply path_forall; intros z; apply set_path2.
  /- The other side is trivial by path induction. -/
  intros []; reflexivity.
end-/

definition equiv_loopS1_int : (base = base) ≃ Int :=
     equiv.mk _ _ (S1_encode base) (S1_encode_isequiv base).

End AssumeUnivalence.
