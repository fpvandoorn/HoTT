(* -*- mode: coq; mode: visual-line -*-  *)

(** * Basic definitions of homotopy type theory, particularly the groupoid structure of identity types. *)

(** ** Type classes *)

(** This command prevents Coq from trying to guess the values of existential variables while doing typeclass resolution.  If you don't know what that means, ignore it. *)
Local Set Typeclasses Strict Resolution.

(** This command prevents Coq from automatically defining the eliminator functions for inductive types.  We will define them ourselves to match the naming scheme of the HoTT Book.  In principle we ought to make this [Global], but unfortunately the tactics [induction] and [elim] assume that the eliminators are named in Coq's way, e.g. [thing_rect], so making it global could cause unpleasant surprises for people defining new inductive types.  However, when you do define your own inductive types you are encouraged to also do [Local Unset Elimination Schemes] and then use [Scheme] to define [thing_ind], [thing_rec], and (for compatibility with [induction] and [elim]) [thing_rect], as we have done below for [paths], [Empty], [Unit], etc.  We are hoping that this will be fixed eventually; see https://coq.inria.fr/bugs/show_bug.cgi?id=3745.  *)
Local Unset Elimination Schemes.

Definition relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : relation A) :=
  reflexivity : forall x : A, R x x.

Class Symmetric {A} (R : relation A) :=
  symmetry : forall x y, R x y -> R y x.

Class Transitive {A} (R : relation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.

(** A [PreOrder] is both Reflexive and Transitive. *)
Class PreOrder {A} (R : relation A) :=
  { PreOrder_Reflexive : Reflexive R | 2 ;
    PreOrder_Transitive : Transitive R | 2 }.

Global Existing Instance PreOrder_Reflexive.
Global Existing Instance PreOrder_Transitive.

Arguments reflexivity {A R _} / _.
Arguments symmetry {A R _} / _ _ _.
Arguments transitivity {A R _} / {_ _ _} _ _.

(** Above, we have made [reflexivity], [symmetry], and [transitivity] reduce under [cbn]/[simpl] to their underlying instances.  This allows the tactics to build proof terms referencing, e.g., [concat].  We use [change] after the fact to make sure that we didn't [cbn] away the original form of the relation.

    If we want to remove the use of [cbn], we can play tricks with [Module Type]s and [Module]s to declare [inverse] directly as an instance of [Symmetric] without changing its type.  Then we can simply [unfold symmetry].  See the comments around the definition of [inverse]. *)

(** Even if we weren't using [cbn], we would have to redefine symmetry, since the built-in Coq version is sometimes too smart for its own good, and will occasionally fail when it should not. *)
Ltac symmetry :=
  let R := match goal with |- ?R ?x ?y => constr:(R) end in
  let x := match goal with |- ?R ?x ?y => constr:(x) end in
  let y := match goal with |- ?R ?x ?y => constr:(y) end in
  let pre_proof_term_head := constr:(@symmetry _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head y x _); change (R y x).

Tactic Notation "etransitivity" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  let pre_proof_term_head := constr:(@transitivity _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head x y z _ _); [ change (R x y) | change (R y z) ].

Tactic Notation "etransitivity" := etransitivity _.

(** We redefine [transitivity] to work without needing to include [Setoid] or be using Leibniz equality, and to give proofs that unfold to [concat]. *)
Ltac transitivity x := etransitivity x.


(** ** Basic definitions *)

(** Define an alias for [Set], which is really [Type₀]. *)
Notation Type0 := Set.

(** Define [Type₁] (really, [Type_i] for any [i > 0]) so that we can enforce having universes that are not [Set].  In trunk, universes will not be unified with [Set] in most places, so we want to never use [Set] at all. *)
Definition Type1 := Eval hnf in let gt := (Set : Type@{i}) in Type@{i}.
Arguments Type1 / .
Identity Coercion unfold_Type1 : Type1 >-> Sortclass.

(** We also define "the next couple of universes", which are actually an arbitrary universe with another one or two strictly below it.  Note when giving universe annotations to these that their universe parameters appear in order of *decreasing* size. *)
Definition Type2 := Eval hnf in let gt := (Type1 : Type@{i}) in Type@{i}.
Arguments Type2 / .
Identity Coercion unfold_Type2 : Type2 >-> Sortclass.

Definition Type3 := Eval hnf in let gt := (Type2 : Type@{i}) in Type@{i}.
Arguments Type3 / .
Identity Coercion unfold_Type3 : Type3 >-> Sortclass.

(** Along the same lines, here is a universe with an extra universe parameter that's less than or equal to it in size.  The [gt] isn't necessary to force the larger universe to be bigger than [Set] (since we refer to the smaller universe by [Type1] which is already bigger than [Set]), but we include it anyway to make the universe parameters occur again in (now non-strictly) decreasing order. *)
Definition Type2le := Eval hnf in let gt := (Set : Type@{i}) in
                                  let ge := ((fun x => x) : Type1 -> Type@{i}) in Type@{i}.
Arguments Type2le / .
Identity Coercion unfold_Type2le : Type2le >-> Sortclass.

Definition Type3le := Eval hnf in let gt := (Set : Type@{i}) in
                                  let ge := ((fun x => x) : Type2le@{j k} -> Type@{i}) in Type@{i}.
Arguments Type3le / .
Identity Coercion unfold_Type3le : Type3le >-> Sortclass.


(** We make the identity map a notation so we do not have to unfold it,
    or complicate matters with its type. *)
Notation idmap := (fun x => x).

(** *** Constant functions *)
Definition const {A B} (b : B) := fun x : A => b.

(** We define notation for dependent pairs because it is too annoying to write and see [existT P x y] all the time.  However, we put it in its own scope, because sometimes it is necessary to give the particular dependent type, so we'd like to be able to turn off this notation selectively. *)
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.
(** We bind [fibration_scope] with [sigT] so that we are automatically in [fibration_scope] when we are passing an argument of type [sigT]. *)
Bind Scope fibration_scope with sigT.

(** We have unified [sig] and [sigT] of the standard Coq, and so we introduce a new notation to not annoy newcomers with the [T] in [projT1] and [projT2] nor the [_sig] in [proj1_sig] and [proj2_sig], and to not confuse Coq veterans by stealing [proj1] and [proj2], which Coq uses for [and]. *)
Notation pr1 := projT1.
Notation pr2 := projT2.

(** The following notation is very convenient, although it unfortunately clashes with Proof General's "electric period".  We add [format] specifiers so that it will display without an extra space, as [x.1] rather than as [x .1]. *)
Notation "x .1" := (pr1 x) (at level 3, format "x '.1'") : fibration_scope.
Notation "x .2" := (pr2 x) (at level 3, format "x '.2'") : fibration_scope.

(** Composition of functions. *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) :=
  fun x => g (f x).

Hint Unfold compose.

(** We put the following notation in a scope because leaving it unscoped causes it to override identical notations in other scopes.  It's convenient to use the same notation for, e.g., function composition, morphism composition in a category, and functor composition, and let Coq automatically infer which one we mean by scopes.  We can't do this if this notation isn't scoped.  Unfortunately, Coq doesn't have a built-in [function_scope] like [type_scope]; [type_scope] is automatically opened wherever Coq is expecting a [Sort], and it would be nice if [function_scope] were automatically opened whenever Coq expects a thing of type [forall _, _] or [_ -> _].  To work around this, we open [function_scope] globally. *)
Notation "g 'o' f" := (compose g f) (at level 40, left associativity) : function_scope.
Open Scope function_scope.

(** Dependent composition of functions. *)
Definition composeD {A B C} (g : forall b, C b) (f : A -> B) := fun x : A => g (f x).

Hint Unfold composeD.

Notation "g 'oD' f" := (composeD g f) (at level 40, left associativity) : function_scope.

(** ** The groupoid structure of identity types. *)

(** The results in this file are used everywhere else, so we need to be extra careful about how we define and prove things.  We prefer hand-written terms, or at least tactics that allow us to retain clear control over the proof-term produced. *)

(** We define our own identity type, rather than using the one in the Coq standard library, so as to have more control over transitivity, symmetry and inverse.  It seems impossible to change these for the standard eq/identity type (or its Type-valued version) because it breaks various other standard things.  Merely changing notations also doesn't seem to quite work. *)
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Scheme paths_ind := Induction for paths Sort Type.
Arguments paths_ind [A] a P f y p.
Scheme paths_rec := Minimality for paths Sort Type.
Arguments paths_rec [A] a P f y p.

(* See comment above about the tactic [induction]. *)
Definition paths_rect := paths_ind.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

(** Ensure [internal_paths_rew] and [internal_paths_rew_r] are defined outside sections, so they are not unnecessarily polymorphic. *)
Lemma paths_rew A a y P (X : P a) (H : a = y :> A) : P y.
Proof. rewrite <- H. exact X. Defined.

Lemma paths_rew_r A a y P (X : P y) (H : a = y :> A) : P a.
Proof. rewrite -> H. exact X. Defined.

Global Instance reflexive_paths {A} : Reflexive (@paths A) | 0 := @idpath A.
Arguments reflexive_paths / .

(** Our identity type is the Paulin-Mohring style.  We derive the Martin-Lof eliminator. *)

Definition paths_ind' {A : Type} (P : forall (a b : A), (a = b) -> Type)
  : (forall (a : A), P a a idpath) -> forall (a b : A) (p : a = b), P a b p.
Proof.
  intros H ? ? [].
  apply H.
Defined.

(** We declare a scope in which we shall place path notations. This way they can be turned on and off by the user. *)

Delimit Scope path_scope with path.
Local Open Scope path_scope.

(** We bind [path_scope] to [paths] so that when we are constructing arguments to things like [concat], we automatically are in [path_scope]. *)
Bind Scope path_scope with paths.


(** The inverse of a path. *)
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

(** Declaring this as [simpl nomatch] prevents the tactic [simpl] from expanding it out into [match] statements.  We only want [inverse] to simplify when applied to an identity path. *)
Arguments inverse {A x y} p : simpl nomatch.

Global Instance symmetric_paths {A} : Symmetric (@paths A) | 0 := @inverse A.
Arguments symmetric_paths / .

(** If we wanted to not have the constant [symmetric_paths] floating around, and wanted to resolve [inverse] directly, instead, we could play this trick, discovered by Georges Gonthier to fool Coq's restriction on [Identity Coercion]s:

<<
Module Export inverse.
  Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
    := match p with idpath => idpath end.
End inverse.

Module Type inverseT.
  Parameter inverse : forall {A}, Symmetric (@paths A).
End inverseT.

Module inverseSymmetric (inverse : inverseT).
  Global Existing Instance inverse.inverse.
End inverseSymmetric.

Module Export symmetric_paths := inverseSymmetric inverse.
>> *)


(** We define equality concatenation by destructing on both its arguments, so that it only computes when both arguments are [idpath].  This makes proofs more robust and symmetrical.  Compare with the definition of [identity_trans].  *)

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments concat {A x y z} p q : simpl nomatch.

Global Instance transitive_paths {A} : Transitive (@paths A) | 0 := @concat A.
Arguments transitive_paths / .


(** Note that you can use the Coq tactics [reflexivity], [transitivity], [etransitivity], and [symmetry] when working with paths; we've redefined them above to use typeclasses and to unfold the instances so you get proof terms with [concat] and [inverse]. *)

(** The identity path. *)
Notation "1" := idpath : path_scope.

(** The composition of two paths. *)
Notation "p @ q" := (concat p q) (at level 20) : path_scope.

(** The inverse of a path. *)
Notation "p ^" := (inverse p) (at level 3, format "p '^'") : path_scope.

(** An alternative notation which puts each path on its own line.  Useful as a temporary device during proofs of equalities between very long composites; to turn it on inside a section, say [Open Scope long_path_scope]. *)
Notation "p @' q" := (concat p q) (at level 21, left associativity,
  format "'[v' p '/' '@''  q ']'") : long_path_scope.


(** An important instance of [paths_ind] is that given any dependent type, one can _transport_ elements of instances of the type along equalities in the base.

   [transport P p u] transports [u : P x] to [P y] along [p : x = y]. *)
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments transport {A} P {x y} p%path_scope u : simpl nomatch.

(** Transport is very common so it is worth introducing a parsing notation for it.  However, we do not use the notation for output because it hides the fibration, and so makes it very hard to read involved transport expression.*)
Delimit Scope fib_scope with fib.
Local Open Scope fib_scope.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.

(** Having defined transport, we can use it to talk about what a homotopy theorist might see as "paths in a fibration over paths in the base"; and what a type theorist might see as "heterogeneous eqality in a dependent type".

We will first see this appearing in the type of [apD]. *)

(** Functions act on paths: if [f : A -> B] and [p : x = y] is a path in [A], then [ap f p : f x = f y].

   We typically pronounce [ap] as a single syllable, short for "application"; but it may also be considered as an acronym, "action on paths". *)

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

(** We introduce the convention that [apKN] denotes the application of a K-path between
   functions to an N-path between elements, where a 0-path is simply a function or an
   element. Thus, [ap] is a shorthand for [ap01]. *)

Notation ap01 := ap (only parsing).

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

Hint Unfold pointwise_paths : typeclass_instances.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with idpath => 1 end.

Definition ap10 {A B} {f g:A->B} (h:f=g) : f == g
  := apD10 h.

(** For the benefit of readers of the HoTT Book: *)
Notation happly := ap10 (only parsing).

Definition ap11 {A B} {f g:A->B} (h:f=g) {x y:A} (p:x=y) : f x = g y.
Proof.
  case h, p; reflexivity.
Defined.

(** See above for the meaning of [simpl nomatch]. *)
Arguments ap {A B} f {x y} p : simpl nomatch.

(** Similarly, dependent functions act on paths; but the type is a bit more subtle. If [f : forall a:A, B a] and [p : x = y] is a path in [A], then [apD f p] should somehow be a path between [f x : B x] and [f y : B y]. Since these live in different types, we use transport along [p] to make them comparable: [apD f p : p # f x = f y].

  The type [p # f x = f y] can profitably be considered as a heterogeneous or dependent equality type, of "paths from [f x] to [f y] over [p]". *)

Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  :=
  match p with idpath => idpath end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments apD {A B} f {x y} p : simpl nomatch.

(** ** Equivalences *)

(** Homotopy equivalences are a central concept in homotopy type theory. Before we define equivalences, let us consider when two types [A] and [B] should be considered "the same".

   The first option is to require existence of [f : A -> B] and [g : B -> A] which are inverses of each other, up to homotopy.  Homotopically speaking, we should also require a certain condition on these homotopies, which is one of the triangle identities for adjunctions in category theory.  Thus, we call this notion an *adjoint equivalence*.

  The other triangle identity is provable from the first one, along with all the higher coherences, so it is reasonable to only assume one of them.  Moreover, as we will see, if we have maps which are inverses up to homotopy, it is always possible to make the triangle identity hold by modifying one of the homotopies.

   The second option is to use Vladimir Voevodsky's definition of an equivalence as a map whose homotopy fibers are contractible.  We call this notion a *homotopy bijection*.

   An interesting third option was suggested by André Joyal: a map [f] which has separate left and right homotopy inverses.  We call this notion a *homotopy isomorphism*.

   While the second option was the one used originally, and it is the most concise one, it makes more sense to use the first one in a formalized development, since it exposes most directly equivalence as a structure.  In particular, it is easier to extract directly from it the data of a homotopy inverse to [f], which is what we care about having most in practice.  Thus, adjoint equivalences are what we will refer to merely as *equivalences*. *)

(** Naming convention: we use [equiv] and [Equiv] systematically to denote types of equivalences, and [isequiv] and [IsEquiv] systematically to denote the assertion that a given map is an equivalence. *)

(** The fact that [r] is a left inverse of [s]. As a mnemonic, note that the partially applied type [Sect s] is the type of proofs that [s] is a section. *)
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

(** A typeclass that includes the data making [f] into an adjoint equivalence. *)
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.

(** A record that includes all the data of an adjoint equivalence. *)
Record Equiv A B := BuildEquiv {
  equiv_fun : A -> B ;
  equiv_isequiv : IsEquiv equiv_fun
}.

Coercion equiv_fun : Equiv >-> Funclass.

Global Existing Instance equiv_isequiv.

Arguments equiv_fun {A B} _ _.
Arguments equiv_isequiv {A B} _.

Delimit Scope equiv_scope with equiv.
Local Open Scope equiv_scope.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.

(** A notation for the inverse of an equivalence.  We can apply this to a function as long as there is a typeclass instance asserting it to be an equivalence.  We can also apply it to an element of [A <~> B], since there is an implicit coercion to [A -> B] and also an existing instance of [IsEquiv]. *)

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'") : equiv_scope.

(** ** Contractibility and truncation levels *)

(** Truncation measures how complicated a type is.  In this library, a witness that a type is n-truncated is formalized by the [IsTrunc n] typeclass.  In many cases, the typeclass machinery of Coq can automatically infer a witness for a type being n-truncated.  Because [IsTrunc n A] itself has no computational content (that is, all witnesses of n-truncation of a type are provably equal), it does not matter much which witness Coq infers.  Therefore, the primary concerns in making use of the typeclass machinery are coverage (how many goals can be automatically solved) and speed (how long does it take to solve a goal, and how long does it take to error on a goal we cannot automatically solve).  Careful use of typeclass instances and priorities, which determine the order of typeclass resolution, can be used to effectively increase both the coverage and the speed in cases where the goal is solvable.  Unfortunately, typeclass resolution tends to spin for a while before failing unless you're very, very, very careful.  We currently aim to achieve moderate coverage and fast speed in solvable cases.  How long it takes to fail typeclass resolution is not currently considered, though it would be nice someday to be even more careful about things.

In order to achieve moderate coverage and speedy resolution, we currently follow the following principles.  They set up a kind of directed flow of information, intended to prevent cycles and potentially infinite chains, which are often the ways that typeclass resolution gets stuck.

- We prefer to reason about [IsTrunc (S n) A] rather than [IsTrunc n (@paths A a b)].  Whenever we see a statement (or goal) about truncation of paths, we try to turn it into a statement (or goal) about truncation of a (non-[paths]) type.  We do not allow typeclass resolution to go in the reverse direction from [IsTrunc (S n) A] to [forall a b : A, IsTrunc n (a = b)].

- We prefer to reason about syntactically smaller types.  That is, typeclass instances should turn goals of type [IsTrunc n (forall a : A, P a)] into goals of type [forall a : A, IsTrunc n (P a)]; and goals of type [IsTrunc n (A * B)] into the pair of goals of type [IsTrunc n A] and [IsTrunc n B]; rather than the other way around.  Ideally, we would add similar rules to transform hypotheses in the cases where we can do so.  This rule is not always the one we want, but it seems to heuristically capture the shape of most cases that we want the typeclass machinery to automatically infer.  That is, we often want to infer [IsTrunc n (A * B)] from [IsTrunc n A] and [IsTrunc n B], but we (probably) don't often need to do other simple things with [IsTrunc n (A * B)] which are broken by that reduction.
*)

(** *** Contractibility *)

(** A space [A] is contractible if there is a point [x : A] and a (pointwise) homotopy connecting the identity on [A] to the constant map at [x].  Thus an element of [contr A] is a pair whose first component is a point [x] and the second component is a pointwise retraction of [A] to [x]. *)

(** We use the [Contr_internal] record so as not to pollute typeclass search; we only do truncation typeclass search on the [IsTrunc] datatype, usually.  We will define a notation [Contr] which is equivalent to [Contr_internal], but picked up by typeclass search.  However, we must make [Contr_internal] a class so that we pick up typeclasses on [center] and [contr].  However, the only typeclass rule we register is the one that turns it into a [Contr]/[IsTrunc].  Unfortunately, this means that declaring an instance like [Instance contr_foo : Contr foo := { center := bar }.] will fail with mismatched instances/contexts.  Instead, we must iota expand such definitions to get around Coq's deficiencies, and write [Instance contr_foo : Contr foo := let x := {| center := bar |} in x.] *)
Class Contr_internal (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Arguments center A {_}.

(** *** Truncation levels *)

(** Truncation measures how complicated a type is in terms of higher path spaces. The (-2)-truncated types are the contractible ones, whose homotopy is completely trivial. The (n+1)-truncated types are those whose path spaces are n-truncated.

   Thus, (-1)-truncated means "the space of paths between any two points is contactible". Such a space is necessarily a sub-singleton: any two points are connected by a path which is unique up to homotopy. In other words, (-1)-truncated spaces are truth values (we call them "propositions").

   Next, 0-truncated means "the space of paths between any two points is a sub-singleton". Thus, two points might not have any paths between them, or they have a unique path. Such a space may have many points but it is discrete in the sense that all paths are trivial. We call such spaces "sets".
*)

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Scheme trunc_index_ind := Induction for trunc_index Sort Type.
Scheme trunc_index_rec := Minimality for trunc_index Sort Type.

(* See comment above about the tactic [induction]. *)
Definition trunc_index_rect := trunc_index_ind.

(** We will use [Notation] for [trunc_index]es, so define a scope for them here. *)
Delimit Scope trunc_scope with trunc.
Bind Scope trunc_scope with trunc_index.
Arguments trunc_S _%trunc_scope.

(** Include the basic numerals, so we don't need to go through the coercion from [nat], and so that we get the right binding with [trunc_scope]. *)
(** Note that putting the negative numbers at level 0 allows us to override the [- _] notation for negative numbers. *)
Notation "n .+1" := (trunc_S n) (at level 2, left associativity, format "n .+1") : trunc_scope.
Notation "n .+1" := (S n) (at level 2, left associativity, format "n .+1") : nat_scope.
Notation "n .+2" := (n.+1.+1)%trunc (at level 2, left associativity, format "n .+2") : trunc_scope.
Notation "n .+2" := (n.+1.+1)%nat (at level 2, left associativity, format "n .+2") : nat_scope.
Local Open Scope trunc_scope.
Notation "-2" := minus_two (at level 0) : trunc_scope.
Notation "-1" := (-2.+1) (at level 0) : trunc_scope.
Notation "0" := (-1.+1) : trunc_scope.
Notation "1" := (0.+1) : trunc_scope.
Notation "2" := (1.+1) : trunc_scope.

Fixpoint nat_to_trunc_index (n : nat) : trunc_index
  := match n with
       | 0%nat => 0
       | S n' => (nat_to_trunc_index n').+1
     end.

Coercion nat_to_trunc_index : nat >-> trunc_index.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | -2 => Contr_internal A
    | n'.+1 => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Arguments IsTrunc_internal n A : simpl nomatch.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

(** We use the priciple that we should always be doing typeclass resolution on truncation of non-equality types.  We try to change the hypotheses and goals so that they never mention something like [IsTrunc n (_ = _)] and instead say [IsTrunc (S n) _].  If you're evil enough that some of your paths [a = b] are n-truncated, but others are not, then you'll have to either reason manually or add some (local) hints with higher priority than the hint below, or generalize your equality type so that it's not a path anymore. *)

Typeclasses Opaque IsTrunc. (* don't auto-unfold [IsTrunc] in typeclass search *)

Arguments IsTrunc : simpl never. (* don't auto-unfold [IsTrunc] with [simpl] *)

Global Instance istrunc_paths (A : Type) n `{H : IsTrunc n.+1 A} (x y : A)
: IsTrunc n (x = y)
  := H x y. (* but do fold [IsTrunc] *)

Hint Extern 0 => progress change IsTrunc_internal with IsTrunc in * : typeclass_instances. (* Also fold [IsTrunc_internal] *)

(** Picking up the [forall x y, IsTrunc n (x = y)] instances in the hypotheses is much tricker.  We could do something evil where we declare an empty typeclass like [IsTruncSimplification] and use the typeclass as a proxy for allowing typeclass machinery to factor nested [forall]s into the [IsTrunc] via backward reasoning on the type of the hypothesis... but, that's rather complicated, so we instead explicitly list out a few common cases.  It should be clear how to extend the pattern. *)
Hint Extern 10 =>
progress match goal with
           | [ H : forall x y : ?T, IsTrunc ?n (x = y) |- _ ]
             => change (IsTrunc n.+1 T) in H
           | [ H : forall (a : ?A) (x y : @?T a), IsTrunc ?n (x = y) |- _ ]
             => change (forall a : A, IsTrunc n.+1 (T a)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (x y : @?T a b), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a), IsTrunc n.+1 (T a b)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (c : @?C a b) (x y : @?T a b c), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a) (c : C a b), IsTrunc n.+1 (T a b c)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (c : @?C a b) (d : @?D a b c) (x y : @?T a b c d), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a) (c : C a b) (d : D a b c), IsTrunc n.+1 (T a b c d)) in H; cbv beta in H
         end.

Notation Contr := (IsTrunc -2).
Notation IsHProp := (IsTrunc -1).
Notation IsHSet := (IsTrunc 0).

Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.

(** *** Simple induction *)

(** The following tactic is designed to be more or less interchangeable with [induction n as [ | n' IH ]] whenever [n] is a [nat] or a [trunc_index].  The difference is that it produces proof terms involving [match] and [fix] explicitly rather than [nat_ind] or [trunc_index_ind], and therefore does not introduce higher universe parameters. *)

Ltac simple_induction n n' IH :=
  generalize dependent n;
  fix IH 1;
  intros [| n'];
  [ clear IH | specialize (IH n') ].

(** *** Truncated relations  *)

(** Hprop-valued relations.  Making this a [Notation] rather than a [Definition] enables typeclass resolution to pick it up easily.  We include the base type [A] in the notation since otherwise e.g. [forall (x y : A) (z : B x y), IsHProp (C x y z)] will get displayed as [forall (x : A), is_mere_relation (C x)].  *)
Notation is_mere_relation A R := (forall (x y : A), IsHProp (R x y)).

(** *** Function extensionality *)

(** The function extensionality axiom is formulated as a class. To use it in a theorem, just assume it with [`{Funext}], and then you can use [path_forall], defined below.  If you need function extensionality for a whole development, you can assume it for an entire Section with [Context `{Funext}].  *)
(** We use a dummy class and an axiom to get universe polymorphism of [Funext] while still tracking its uses.  Coq's universe polymorphism is parametric; in all definitions, all universes are quantified over before any other variables.  It's impossible to state a theorem like [(forall i : Level, P i) -> Q] (e.g., "if [C] has all limits of all sizes, then [C] is a preorder" isn't statable).*  By making [isequiv_apD10] an [Axiom] rather than a per-theorem hypothesis, we can use it at multiple incompatible universe levels.  By only allowing use of the axiom when we have a [Funext] in the context, we can still track what theorems depend on it (because their type will mention [Funext]).

    By giving [Funext] a field who's type is an axiom, we guarantee that we cannot construct a fresh instance of [Funext] without [admit]; there's no term of type [dummy_funext_type] floating around.  If we did not give [Funext] and fields, then we could accidentally manifest a [Funext] using, e.g., [constructor], and then we wouldn't have a tag on the theorem that did this.

    As [Funext] is never actually used productively, we toss it in [Type0] and make it [Monomorphic] so it doesn't add more universes.

    * That's not technically true; it might be possible to get non-parametric universe polymorphism using [Module]s and ([Module]) Functors; we can use functors to quantify over a [Module Type] which requires a polymorphic proof of a given hypothesis, and then use that hypothesis polymorphically in any theorem we prove in our new [Module] Functor.  But that is far beyond the scope of this file. *)
Monomorphic Axiom dummy_funext_type : Type0.
Monomorphic Class Funext := { dummy_funext_value : dummy_funext_type }.
Axiom isequiv_apD10 : forall `{Funext} (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).
Global Existing Instance isequiv_apD10.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g
  :=
  (@apD10 A P f g)^-1.

Definition path_forall2 `{Funext} {A B : Type} {P : A -> B -> Type} (f g : forall x y, P x y) :
  (forall x y, f x y = g x y) -> f = g
  :=
  (fun E => path_forall f g (fun x => path_forall (f x) (g x) (E x))).


(** *** Tactics *)

(** We declare some more [Hint Resolve] hints, now in the "hint database" [path_hints].  In general various hints (resolve, rewrite, unfold hints) can be grouped into "databases". This is necessary as sometimes different kinds of hints cannot be mixed, for example because they would cause a combinatorial explosion or rewriting cycles.

   A specific [Hint Resolve] database [db] can be used with [auto with db].

   The hints in [path_hints] are designed to push concatenation *outwards*, eliminate identities and inverses, and associate to the left as far as  possible. *)

(** TODO: think more carefully about this.  Perhaps associating to the right would be more convenient? *)
Hint Resolve
  @idpath @inverse
 : path_hints.

Hint Resolve @idpath : core.

Ltac path_via mid :=
  apply @concat with (y := mid); auto with path_hints.

(** We put [Empty] here, instead of in [Empty.v], because [Ltac done] uses it. *)
Inductive Empty : Type1 := .

Scheme Empty_ind := Induction for Empty Sort Type.
Scheme Empty_rec := Minimality for Empty Sort Type.
Definition Empty_rect := Empty_ind.

Definition not (A:Type) : Type := A -> Empty.
Notation "~ x" := (not x) : type_scope.
Hint Unfold not: core.
Notation "x <> y  :>  T" := (not (x = y :> T))
(at level 70, y at next level, no associativity) : type_scope.
Notation "x <> y" := (x <> y :> _) (at level 70, no associativity) : type_scope.

Definition complement {A} (R : relation A) : relation A :=
  fun x y => ~ (R x y).

Typeclasses Opaque complement.

Class Irreflexive {A} (R : relation A) :=
  irreflexivity : Reflexive (complement R).

Class Asymmetric {A} (R : relation A) :=
  asymmetry : forall {x y}, R x y -> (complement R y x : Type).

(** Likewise, we put [Unit] here, instead of in [Unit.v], because [Trunc] uses it. *)
Inductive Unit : Type1 :=
    tt : Unit.

Scheme Unit_ind := Induction for Unit Sort Type.
Scheme Unit_rec := Minimality for Unit Sort Type.
Definition Unit_rect := Unit_ind.

(** ** Decidable equality *)

(* NB: This has to come after our definition of [not], so that it refers to our [not] rather than the one in [Coq.Logic]. *)
Class Decidable (A : Type) :=
  dec : A + (~ A).
Arguments dec A {_}.

Class DecidablePaths (A : Type) :=
  dec_paths : forall (x y : A), Decidable (x = y).
Global Existing Instance dec_paths.

(** *** Pointed types *)

(** A space is pointed if that space has a point. *)
Class IsPointed (A : Type) := point : A.
Definition pointedType := { u : Type & IsPointed u }.
Arguments point A {_}.

(** *** Homotopy fibers *)

(** Homotopy fibers are homotopical inverse images of points.  *)

Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.

(** Ssreflect tactics, adapted by Robbert Krebbers *)
Ltac done :=
  trivial; intros; solve
    [ repeat first
      [ solve [trivial]
      | solve [symmetry; trivial]
      | reflexivity
      (* Discriminate should be here, but it doesn't work yet *)
      (* | discriminate *)
      | contradiction
      | split ]
    | match goal with
      H : ~ _ |- _ => solve [destruct H; trivial]
      end ].
Tactic Notation "by" tactic(tac) :=
  tac; done.

(** A convenient tactic for using function extensionality. *)
Ltac by_extensionality x :=
  intros; unfold compose;
  match goal with
  | [ |- ?f = ?g ] => eapply path_forall; intro x;
      match goal with
        | [ |- forall (_ : prod _ _), _ ] => intros [? ?]
        | [ |- forall (_ : sigT _ _), _ ] => intros [? ?]
        | _ => intros
    end;
    simpl; auto with path_hints
  end.

(** Test if a tactic succeeds, but always roll-back the results *)
Tactic Notation "test" tactic3(tac) :=
  try (first [ tac | fail 2 tac "does not succeed" ]; fail tac "succeeds"; [](* test for [t] solved all goals *)).

(** [not tac] is equivalent to [fail tac "succeeds"] if [tac] succeeds, and is equivalent to [idtac] if [tac] fails *)
Tactic Notation "not" tactic3(tac) := try ((test tac); fail 1 tac "succeeds").

(** Removed auto. We can write "by (path_induction;auto with path_hints)"
 if we want to.*)
Ltac path_induction :=
  intros; repeat progress (
    match goal with
      | [ p : ?x = ?y  |- _ ] => not constr_eq x y; induction p
    end
  ).

(** The tactic [f_ap] is a replacement for the previously existing standard library tactic [f_equal].  This tactic works by repeatedly applying the fact that [f = g -> x = y -> f x = g y] to turn, e.g., [f x y = f z w] first into [f x = f z] and [y = w], and then turns the first of these into [f = f] and [x = z].  The [done] tactic is used to detect the [f = f] case and finish, and the [trivial] is used to solve, e.g., [x = x] when using [f_ap] on [f y x = f z x].  This tactic only works for non-dependently-typed functions; we cannot express [y = w] in the first example if [y] and [w] have different types.  If and when Arnaud's new-tacticals branch lands, and we can have a goal which depends on the term used to discharge another goal, then this tactic should probably be generalized to deal with dependent functions. *)
Ltac f_ap :=
  idtac;
  lazymatch goal with
    | [ |- ?f ?x = ?g ?x ] => apply (@apD10 _ _ f g);
                             try (done || f_ap)
    | _ => apply ap11;
          [ done || f_ap
          | trivial ]
  end.

(** [expand] replaces both terms of an equality (either [paths] or [pointwise_paths] in the goal with their head normal forms *)
Ltac expand :=
  idtac;
  match goal with
    | [ |- ?X = ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' = Y')
    | [ |- ?X == ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' == Y')
  end; simpl.

(** [atomic x] is the same as [idtac] if [x] is a variable or hypothesis, but is [fail 0] if [x] has internal structure. *)
Ltac atomic x :=
  idtac;
  match x with
    | ?f _ => fail 1 x "is not atomic"
    | (fun _ => _) => fail 1 x "is not atomic"
    | forall _, _ => fail 1 x "is not atomic"
    | _ => idtac
  end.

(** [transparent assert (H : T)] is like [assert (H : T)], but leaves the body transparent. *)
(** Since binders don't respect [fresh], we use a name unlikely to be reused. *)
Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" :=
  refine (let __transparent_assert_hypothesis := (_ : type) in _);
  [
  | ((* We cannot use the name [__transparent_assert_hypothesis], due to some infelicities in the naming of bound variables.  So instead we pull the bottommost hypothesis. *)
    let H := match goal with H := _ |- _ => constr:(H) end in
    rename H into name) ].

(** [transparent eassert] is like [transparent assert], but allows holes in the type, which will be turned into evars. *)
Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" "by" tactic3(tac) := let name := fresh "H" in transparent assert (name : type); [ solve [ tac ] | ].
Tactic Notation "transparent" "eassert" "(" ident(name) ":" open_constr(type) ")" := transparent assert (name : type).
Tactic Notation "transparent" "eassert" "(" ident(name) ":" open_constr(type) ")" "by" tactic3(tac) := transparent assert (name : type) by tac.
