/- -*- mode: coq; mode: visual-line -*- -/
/- Theorems about disjoint unions -/

Require Import HoTT.Basics.
Require Import Types.Empty.
/- The following are only required for the equivalence between [sum] and a sigma type -/
Require Import Types.bool Types.ΠTypes.Sigma.
Local Open Scope trunc_scope.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

Scheme sum_ind := Induction for sum Sort Type.
Arguments sum_ind {A B} P f g s : rename.

/- CoUnpacking -/

/- Sums are coproducts, so there should be a dual to [unpack_prod].  I'm not sure what it is, though. -/

/- Eta conversion -/

definition eta_sum `(z : A + B) : match z with
                                    | inl z' => inl z'
                                    | inr z' => inr z'
                                  end ≈ z :=
     match z with inl _ => 1 | inr _ => 1 end.

/- Paths -/

definition path_sum {A B : Type} (z z' : A + B)
           (pq : match z, z' with
                   | inl z0, inl z'0 => z0 ≈ z'0
                   | inr z0, inr z'0 => z0 ≈ z'0
                   | _, _ => Empty
                 end)
: z ≈ z'.
  destruct z, z', pq; exact idpath.
Defined.

definition path_sum_inv {A B : Type} {z z' : A + B}
           (pq : z ≈ z')
: match z, z' with
    | inl z0, inl z'0 => z0 ≈ z'0
    | inr z0, inr z'0 => z0 ≈ z'0
    | _, _ => Empty
  end :=
     match pq with
       | 1 => match z with
                | inl _ => 1
                | inr _ => 1
              end
     end.

/- This version produces only paths between closed terms, as opposed to paths between arbitrary inhabitants of sum types. -/
definition path_sum_inl {A B : Type} {x x' : A}
: inl x ≈ inl x' → x ≈ x' :=
     λp, @path_sum_inv A B _ _ p.

definition path_sum_inr {A B : Type} {x x' : B}
: inr x ≈ inr x' → x ≈ x' :=
     λp, @path_sum_inv A B _ _ p.

/- This lets us identify the path space of a sum type, up to equivalence. -/

definition eisretr_path_sum {A B} {z z' : A + B}
: Sect (@path_sum_inv _ _ z z') (path_sum z z') :=
     λp, match p as p in (_ ≈ z') return
                    path_sum z z' (path_sum_inv p) ≈ p
              with
                | 1 => match z as z return
                             path_sum z z (path_sum_inv 1) ≈ 1
                       with
                         | inl _ => 1
                         | inr _ => 1
                       end
              end.

definition eissect_path_sum {A B} {z z' : A + B}
: Sect (path_sum z z') (@path_sum_inv _ _ z z').
/-begin
  intro p.
  destruct z, z', p; exact idpath.
end-/

definition isequiv_path_sum [instance] {A B : Type} {z z' : A + B}
: IsEquiv (path_sum z z') | 0.
/-begin
  refine (IsEquiv.mk _ _
                       (path_sum z z')
                       (@path_sum_inv _ _ z z')
                       (@eisretr_path_sum A B z z')
                       (@eissect_path_sum A B z z')
                       _).
  destruct z, z';
    intros [];
    exact idpath.
end-/

definition equiv_path_sum {A B : Type} (z z' : A + B) :=
     Equiv.mk _ _ _ (@isequiv_path_sum A B z z').

/- Transport -/

definition transport_sum {A : Type} {P Q : A → Type} {a a' : A} (p : a ≈ a')
           (z : P a + Q a)
: transport (λa, P a + Q a) p z ≈ match z with
                                         | inl z' => inl (p ▹ z')
                                         | inr z' => inr (p ▹ z')
                                       end :=
     match p with idpath => match z with inl _ => 1 | inr _ => 1 end end.

/- Functorial action -/

definition functor_sum {A A' B B' : Type} (f : A → A') (g : B → B')
: A + B → A' + B' :=
     λz, match z with inl z' => inl (f z') | inr z' => inr (g z') end.

/- Equivalences -/

definition isequiv_functor_sum [instance] [H : IsEquiv A A' f] [H : IsEquiv B B' g]
: IsEquiv (functor_sum f g) | 1000.
/-begin
  apply (isequiv_adjointify
           (functor_sum f g)
           (functor_sum f⁻¹ g⁻¹));
  [ intros [?|?]; simpl; apply ap; apply eisretr
  | intros [?|?]; simpl; apply ap; apply eissect ].
end-/

definition equiv_functor_sum [H : IsEquiv A A' f] [H : IsEquiv B B' g]
: A + B ≃ A' + B' :=
     Equiv.mk _ _ (functor_sum f g) _.

definition equiv_functor_sum' {A A' B B' : Type} (f : A ≃ A') (g : B ≃ B')
: A + B ≃ A' + B' :=
     equiv_functor_sum (f := f) (g := g).

definition equiv_functor_sum_l {A B B' : Type} (g : B ≃ B')
: A + B ≃ A + B' :=
     equiv_functor_sum (f := idmap) (g := g).

definition equiv_functor_sum_r {A A' B : Type} (f : A ≃ A')
: A + B ≃ A' + B :=
     equiv_functor_sum (f := f) (g := idmap).

/- Symmetry -/

/- This is a special property of [sum], of course, not an instance of a general family of facts about types. -/

definition equiv_sum_symm (A B : Type) : A + B ≃ B + A.
/-begin
  apply (equiv_adjointify
           (λab, match ab with inl a => inr a | inr b => inl b end)
           (λab, match ab with inl a => inr a | inr b => inl b end));
  intros [?|?]; exact idpath.
end-/

/- Universal mapping properties -/

/- Ordinary universal mapping properties are expressed as equivalences of sets or spaces of functions.  In type theory, we can go beyond this and express an equivalence of types of *dependent* functions. -/

definition sum_ind_uncurried {A B} (P : A + B → Type)
           (fg : (Πa, P (inl a)) × (Πb, P (inr b)))
: Πs, P s :=
     @sum_ind A B P (pr1 fg) (pr2 fg).

/- First the positive universal property.
   Doing this sort of thing without adjointifying will require very careful use of funext. -/
definition isequiv_sum_ind [instance] [H : Funext] `(P : A + B → Type)
: IsEquiv (sum_ind_uncurried P) | 0.
/-begin
  apply (isequiv_adjointify
           (sum_ind_uncurried P)
           (λf, (λa, f (inl a), λb, f (inr b))));
  repeat ((exact idpath)
            || intros []
            || intro
            || apply path_forall).
end-/

definition equiv_sum_ind [H : Funext] `(P : A + B → Type) :=
     Equiv.mk _ _ _ (isequiv_sum_ind P).

/- The non-dependent version, which is a special case, is the sum-distributive equivalence. -/
definition equiv_sum_distributive [H : Funext] (A B C : Type)
: (A → C) × (B → C) ≃ (A + B → C) :=
     equiv_sum_ind (λ_, C).

/- Sums preserve most truncation -/

definition trunc_sum [instance] n' (n := n'.+2)
         [H : is_trunc n A, is_trunc n B]
: is_trunc n (A + B) | 100.
/-begin
  intros a b.
  eapply trunc_equiv';
    [ exact (equiv_path_sum _ _) | ].
  destruct a, b; simpl in *;
  try typeclasses eauto;
  intros [].
end-/

definition hset_sum [instance] {HA : IsHSet A, HB : IsHSet B} : IsHSet (A + B) | 100 :=
     @trunc_sum -2 A HA B HB.

/- Binary coproducts are equivalent to dependent sigmas where the first component is a bool. -/

definition sigT_of_sum A B (x : A + B)
: Σb : bool, if b then A else B  :=
     (_;
      match
        x as s
        return
        (if match s with
              | inl _ => tt
              | inr _ => ff
            end then A else B)
      with
        | inl a => a
        | inr b => b
      end).

definition sum_of_sigT A B (x : Σb : bool, if b then A else B )
: A + B :=
     match x with
       | ⟨tt, a⟩ => inl a
       | ⟨ff, b⟩ => inr b
     end.

definition isequiv_sigT_of_sum [instance] A B : IsEquiv (@sigT_of_sum A B) | 0.
/-begin
  apply (isequiv_adjointify (@sigT_of_sum A B)
                            (@sum_of_sigT A B));
  repeat (intros [] || intro); exact idpath.
end-/

definition isequiv_sum_of_sigT [instance] A B : IsEquiv (sum_of_sigT A B) :=
     isequiv_inverse (@sigT_of_sum A B).

/- An alternative way of proving the truncation property of [sum]. -/
definition trunc_sum' n A B [H : is_trunc n bool, is_trunc n A, is_trunc n B]
: (IsTrunc n (A + B)).
/-begin
  eapply trunc_equiv'; [ esplit;
                         exact (@isequiv_sum_of_sigT _ _)
                       | ].
  typeclasses eauto.
end-/
