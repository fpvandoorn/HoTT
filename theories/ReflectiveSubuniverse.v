/- -*- mode: coq; mode: visual-line -*- -/
Require Import HoTT.Basics HoTT.Types.
Require Import UnivalenceImpliesFunext EquivalenceVarieties Extensions.
Require Import HoTT.Tactics.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

Local Arguments compose / .

/- Reflective Subuniverses -/

/- We will define reflective subuniverses using modules.  Since modules are one of the more difficult parts of Coq to understand, and the documentation in the reference manual is a bit sparse, we include here a brief introduction to modules.

For our purposes here, it is appropriate to think of a [Module Type] as analogous to a [Record] type, and a [Module] having that module type (called an "implementation" of it) as analogous to an element of that record type.  For instance, instead of

<<
Record foo :=
  { bar : Type ;
    baz : bar → Type
  }.
>>

we could write

<<
Module Type foo.
  Parameter bar : Type.
  Parameter baz : bar → Type
End foo.
>>

and then instead of

<<
definition qux : foo :=
     Build_foo bool (λb, if b then unit else Empty).
>>

we could write

<<
Module qux <: foo.
  definition bar : Type :=
       bool.
  definition baz : bar → Type :=
       λb, if b then unit else Empty.
End qux.
>>

Given these definitions, where we refer to [bar qux] and [baz qux] in the record case, in the module case we would write [qux.bar] and [qux.baz].  However, there are a few essential differences (apart from these syntactic ones).

Firstly, while elements of records are (like everything else in Coq's type theory) strongly typed, modules are duck-typed.  In other words, [qux] is a module of type [foo] simply by virtue of containing fields [bar] and [baz] that have the same types as those declared for the parameters of [foo]; the type declaration [<: foo] only serves to document and enforce this fact.

Secondly, modules do not have to be declared to have any type, or they can have more than one type.  A module is free to contain as many definitions (and other things such as notations, coercions, instances, etc.) as you like, and to "implement" as many module types as you like.  In particular, [qux] could contain additional definitions and it would still be of type [foo].

Thirdly, and more importantly, modules are *second-class*: you cannot pass them around as arguments to functions.  Nor can you construct them "on the fly"; they can only be defined at top level.  However, you can pass a module as an argument to *another module*.  For instance, here is a module which takes a module of type [foo] as an argument.

<<
Module htns (f : foo).
  definition qjkx : Type :=
       Σx : f.bar, f.baz x .
End htns.
>>

Now if we have a [foo], such as [qux], we can pass it as an argument to [htns] and get a new module (again, only at top level):

<<
Module gcrl := htns qux.
>>

After this, we can refer to [gcrl.qjkx] and get [Σx : qux.bar, qux.baz x ].  Together with the fact that modules don't need to have a type, this sort of gives us a way to pass a module as an argument to a collection of functions; we can define a module like [htns] which takes a [foo] as an argument and in which we define many functions depending on [foo]; then whenever we want to apply these functions to a [foo] (such as [qux]) we do the application at top-level, as above with [gcrl].

Unfortunately, Coq does not allow modules to take elements of ordinary types as arguments either; if you want to pass a [nat], say, as an argument to a module, you have to first wrap the [nat] in another module.  You can think of types and module-types as "parallel universes" of types; never the twain shall meet.

Given these annoying limitations, why would anyone ever use modules instead of records?  One reason is that modules are good at (indeed, are more or less designed for) *namespacing*.  In particular, it is possible to [Import] a module, so that all of its fields can be accessed without a dot-prefix.  In fact, every file in Coq is implicitly its own module, and when you say [Require Import Filename.] you are actually [Import]ing a module.  Similarly, modules are used for access control in the private-inductive-types hack that we use to define HITs that compute.

Another reason to use modules, which is the primary reason we choose to use them here, is that the fields of a module are *individually* universe polymorphic.  In other words, in order to define a module of type [foo], as above, you need to give a *polymorphic* definition of [bar] and a *polymorphic* definition of [baz], and the resulting module remembers the polymorphism of each of those fields.  By contrast, a definition of an element of a record type may be itself polymorphic, but an individual *instance* of that definition will pertain only to a fixed collection of universes.

Note that the possibility of individually polymorphic fields practically mandates that modules *must* be second-class.  For a polymorphic field involves an implicit quantification over all universes; hence if the record itself were a first-class object, what universe would it live in?  A mathematician can think of modules as analogous to the proper classes in NBG set theory: they can be "large" without impacting the consistency strength, *because* we are limited in what we can do with them.

In the case in point, if a reflective subuniverse were a record, then "a reflective subuniverse" would be a reflective subuniverse of only *one* universe.  A polymorphic definition of a particular reflective subuniverse would result in defining related reflective subuniverses of every universe, but the relation *between* these subuniverses would not be specified.  In particular, if we have types [X : Type@{i}] and [Y : Type@{j}] in different universes and a map [f : X → Y], while [Y] is in the subuniverse of [Type@{j}], we could not apply the universal property to extend [f] to a map [O X → Y], since the universal property asserted for [O@{i} X] would only refer to maps with target also in [Type@{i}].  This is at best annoying; for instance, it means that we couldn't define, say, [Trunc_functor] by using [O_functor] and then proceed to apply it to maps between types in different universes (which turns out to be necessary sometimes).  At worst, such as when trying to prove that the universe of modal types for a lex modalities is itself modal, this approach seems more or less unworkable.

Therefore, we choose to make a reflective subuniverse a module.  This means that in order to define "a reflective subuniverse", you have to give a *polymorphic* definition of the reflector, the universal property, etc.  In particular, the universal property must be polymorphic enough to allow the situation with [X : Type@{i}] and [Y : Type@{j}] considered above.

There are some issues involving this choice that must be addressed.  One of them is that when implementing a polymorphic module types, Coq is *very* strict about matching up the polymorphism.  Specifically, each [Definition] in the implementing module must have *exactly* the same number of universe parameters as the corresponding [Parameter] in the module type, and all the constraints in the former must be implied by those in the latter.  This ensures that the implementation is "at least as polymorphic" as the specification.

Now normally, a polymorphic definition will end up with many more universes than it needs, and we have little control over how many those are.  Therefore, in order to have a chance of ensuring that our implementations of module types match up in polymorphism, we almost always need to add explicit universe annotations in order to control how many universe parameters they end up with.  This is slightly annoying, but fortunately it only needs to be dealt with when *defining* a particular reflective subuniverse; to users the polymorphism should be invisible and automatic.

This also means it is important that we know exactly how many universe parameters each field of our module types is *expected* to take.  It would be nice if Coq had a feature for declaring (and verifying) the universe parameters of a definition in the same way that we declare the type parameters.  In the absence of this (requested at https://coq.inria.fr/bugs/show_bug.cgi?id=3818), we write [Check foo@{a b c}.] after the definition of [foo] to declare that [foo] takes three universe parameters.  Note that this will fail with an [Error] unless [foo] does in fact take exactly three universe parameters.

Another issue that must be dealt with is the fact, mentioned above, that a module cannot be parametrized over an ordinary type.  However, it frequently happens that we do want to define a family of reflective subuniverses, e.g. the n-truncation modalities for all [n : trunc_index], or the open and closed modalities for all [U : hProp].  The solution we choose is for our basic [Module Type] to represent not a *single* reflective subuniverse, but an entire *family* of them, parametrized by some type.  This can be regarded as analogous to how when doing mathematics relative to a base topos, the correct notion of "large category" is an *indexed category* (a.k.a. fibration), which comes with a basic notion of "[I]-indexed family of objects" for all [I] in the base topos.
-/

Module Type ReflectiveSubuniverses.

  /- As mentioned above, an implementation of this module type is a *family* of reflective subuniverses, indexed by the below type [ReflectiveSubuniverse].  If we just wrote [ReflectiveSubuniverse : Type], then it would end up parametrized by one universe, but in many examples the natural definition of the parametrizing type involves also a smaller universe, which would cause problems with Coq's strict polymorphism enforcement for module type implementations.  Thus, we use [Type2] instead, which takes two universe parameters. -/
  Parameter ReflectiveSubuniverse : Type2@{u a}.
  Check ReflectiveSubuniverse@{u a}.

  /- The universe parameters occurring in the definitions here play one of four roles, which we indicate consistently by [u], [a], [i], and [j].

  - [u] is the size of the parametrizing type [ReflectiveSubuniverse] (and, later, also [Modality]).
  - [a] is the size of smaller type-data occurring in that type, such as the family of generators for a localization.  This generally must be strictly smaller than [u].
  - [i] is the size of a type that we are reflecting or testing to be in the subuniverse.  This is generally at least as big as [a].
  - [j] is the size of a type that we are eliminating into (out of a type in [i]) with a universal property.  Also generally at least as big as [a].
  - [k] is a universe at least as large as both [i] and [j], in which statements about types in both of them can live. -/

  Parameter O_reflector : Π(O : ReflectiveSubuniverse@{u a}),
                            Type2le@{i a} → Type2le@{i a}.
  Check O_reflector@{u a i}.    /- Verify that we have the right number of universes -/

  /- For reflective subuniverses (and hence also modalities), it will turn out that [In ∘ T] is equivalent to [IsEquiv (O_unit T)].  We could define the former as the latter, and it would simplify some of the general theory.  However, in many examples there is a "more basic" definition of [In O] which is equivalent, but not definitionally identical, to [IsEquiv (O_unit T)].  Thus, including [In O] as data makes more things turn out to be judgmentally what we would expect. -/
  Parameter inO_internal : Π(O : ReflectiveSubuniverse@{u a}),
                             Type2le@{i a} → Type2le@{i a}.
  Check inO_internal@{u a i}.

  Parameter O_inO_internal : Π(O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                               inO_internal@{u a i} ∘ (O_reflector@{u a i} ∘ T).
  Check O_inO_internal@{u a i}.

  Parameter to : Π(O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                   T → O_reflector@{u a i} ∘ T.
  Check to@{u a i}.

  Parameter inO_equiv_inO_internal :
      Π(O : ReflectiveSubuniverse@{u a}) (T U : Type@{i})
             (T_inO : inO_internal@{u a i} ∘ T) (f : T → U) (feq : IsEquiv f),
        inO_internal@{u a i} ∘ U.
  Check inO_equiv_inO_internal@{u a i}.

  /- In most examples, [Funext] is necessary to prove that the predicate of being in the subuniverse is an hprop.  To avoid needing to assume [Funext] as a global hypothesis when constructing such examples, and since [Funext] is often not needed for any of the rest of the theory, we add it as a hypothesis to this specific field. -/
  Parameter hprop_inO_internal
  : Funext → Π(O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                is_hprop (inO_internal@{u a i} ∘ T).
  Check hprop_inO_internal@{u a i}.

  /- We express the universal property using the representation [ooExtendableAlong] of precomposition equivalences.  This has the advantage that it avoids the funext redexes that otherwise infect the theory, thereby simplifying the proofs and proof terms.  We never have to worry about whether we have a path between functions or a homotopy; we use only homotopies, with no need for [ap10] or [path_arrow] to mediate.  Furthermore, the data in [ooExtendableAlong] are all special cases of the induction principle of a modality.  Thus, all the theorems we prove about reflective subuniverses will, when interpreted for a modality (coerced as above to a reflective subuniverse), reduce definitionally to "the way we would have proved them directly for a modality".  -/
  Parameter extendable_to_O_internal
  : Π(O : ReflectiveSubuniverse@{u a}) {P : Type2le@{i a}} {Q : Type2le@{j a}} {Q_inO : inO_internal@{u a j} ∘ Q},
      ooExtendableAlong@{i i j k} (to ∘ P) (λ_, Q).
  Check extendable_to_O_internal@{u a i j k}.

End ReflectiveSubuniverses.


/- We now begin a parametrized module to incorporate most of the theory of reflective subuniverses.  Thus, after defining a particular family of reflective subuniverses, you can apply this module and [Import] it to get all of the theory.  (Some suggested naming conventions for these modules can be found in Modality.v.)  -/
Module ReflectiveSubuniverses_Theory (Os : ReflectiveSubuniverses).
Export Os.

/- We now give new names or identities to all the "internal" fields.  This serves several purposes.  Firstly, it allows us to make "being in the subuniverse" into a typeclass. -/
Class In (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}) :=
  in_inO_internal : inO_internal@{u a i} ∘ T.

Typeclasses Transparent In.

/- The type of types in the subuniverse -/
definition Type_ (O : ReflectiveSubuniverse) : Type :=
     ΣT : Type, In ∘ T.

/- Before going on, we declare some coercions in a module, so that they can be imported separately.  In fact, this submodule should be exported by any file that defines a reflective subuniverse.  -/
Module Export Coercions.

  /- We allow the name of a subuniverse or modality to be used as the name of its reflector.  This means that when defining a particular example, you should generally put the parametrizing family in a wrapper, so that you can notate the subuniverse as parametrized by, rather than identical to, its parameter.  See Modality.v, Truncations.v, and Localization.v for examples. -/
  Coercion O_reflector : ReflectiveSubuniverse >-> Funclass.

  /- Obviously, every element of [Type_ O] is a type. -/
  Coercion TypeO_pr1 ∘ (T : Type_ O) := @dpr1 Type (In O) T.

End Coercions.

/- With this given, we now essentially have to redefine almost all the other fields so that they refer explicitly to the class [In] rather than to [inO_internal], so that Coq is willing to do typeclass inference for them. -/

/- We assumed repleteness of the subuniverse in the definition.  Of course, with univalence this would be automatic, but we include it as a hypothesis since this is the only appearance of univalence in the theory of reflective subuniverses and non-lex modalities, and most or all examples can be shown to be replete without using univalence. -/
definition inO_equiv_inO {O : ReflectiveSubuniverse}
           T {U} {T_inO : In ∘ T} (f : T → U) {feq : IsEquiv f}
: In ∘ U :=
   inO_equiv_inO_internal ∘ T U T_inO f feq.

/- Being in the subuniverse is a mere predicate (by hypothesis) -/
definition hprop_inO [instance] {fs : Funext} {O : ReflectiveSubuniverse} (T : Type)
  : is_hprop (In ∘ T) :=
     hprop_inO_internal fs ∘ T.

/- [O T] is always in the subuniverse (by hypothesis).  This needs a universe annotation to become sufficiently polymorphic. -/
definition O_inO [instance] {O : ReflectiveSubuniverse} (T : Type) : In ∘ (O T) :=
     O_inO_internal ∘ T.

/- The second component of [TypeO] is unique -/
definition path_TypeO {fs : Funext} ∘ (T T' : Type_ O) (p : T.1 ≈ T'.1)
  : T ≈ T' :=
     path_sigma_hprop T T' p.

definition extendable_to_O (O : ReflectiveSubuniverse)
           {P Q : Type} {Q_inO : In ∘ Q}
: ooExtendableAlong (to ∘ P) (λ_, Q) :=
     @extendable_to_O_internal ∘ P Q Q_inO.

/- We now extract the recursion principle and the restricted induction principles for paths. -/
section ORecursion
  Context {O : ReflectiveSubuniverse}.

  definition O_rec {P Q : Type} {Q_inO : In ∘ Q}
             (f : P → Q)
  : ∘ P → Q :=
     (pr1 (extendable_to_O ∘ 1%nat) f).1.

  definition O_rec_beta {P Q : Type} {Q_inO : In ∘ Q}
             (f : P → Q) (x : P)
  : O_rec f (to ∘ P x) ≈ f x :=
     (pr1 (extendable_to_O ∘ 1%nat) f).2 x.

  definition O_indpaths {P Q : Type} {Q_inO : In ∘ Q}
             (g h : ∘ P → Q) (p : g ∘ to ∘ P == h ∘ to ∘ P)
  : g == h :=
     (pr1 (pr2 (extendable_to_O ∘ 2) g h) p).1.

  definition O_indpaths_beta {P Q : Type} {Q_inO : In ∘ Q}
             (g h : ∘ P → Q) (p : g ∘ (to ∘ P) == h ∘ (to ∘ P)) (x : P)
  : O_indpaths g h p (to ∘ P x) ≈ p x :=
     (pr1 (pr2 (extendable_to_O ∘ 2) g h) p).2 x.

  definition O_ind2paths {P Q : Type} {Q_inO : In ∘ Q}
             {g h : ∘ P → Q} (p q : g == h)
             (r : p oD (to ∘ P) == q oD (to ∘ P))
  : p == q :=
     (pr1 (pr2 (pr2 (extendable_to_O ∘ 3) g h) p q) r).1.

  definition O_ind2paths_beta {P Q : Type} {Q_inO : In ∘ Q}
             {g h : ∘ P → Q} (p q : g == h)
             (r : p oD (to ∘ P) == q oD (to ∘ P)) (x : P)
  : O_ind2paths p q r (to ∘ P x) ≈ r x :=
     (pr1 (pr2 (pr2 (extendable_to_O ∘ 3) g h) p q) r).2 x.

  /- Clearly we can continue indefinitely as needed. -/

End ORecursion.

/- We never want to see [extendable_to_O]. -/
Arguments O_rec : simpl never.
Arguments O_rec_beta : simpl never.
Arguments O_indpaths : simpl never.
Arguments O_indpaths_beta : simpl never.
Arguments O_ind2paths : simpl never.
Arguments O_ind2paths_beta : simpl never.

/- Given [Funext], we prove the definition of reflective subuniverse in the book. -/
definition isequiv_o_to_O [instance] [H : Funext]
       (O : ReflectiveSubuniverse) (P Q : Type) [H : In ∘ Q]
: IsEquiv (λg : ∘ P → Q, g ∘ to ∘ P) :=
   isequiv_ooextendable _ _ (extendable_to_O O).

definition equiv_o_to_O [H : Funext]
           (O : ReflectiveSubuniverse) (P Q : Type) [H : In ∘ Q]
: (O P → Q) ≃ (P → Q) :=
   Equiv.mk _ _ (λg : ∘ P → Q, g ∘ to ∘ P) _.

/- Properties of Reflective Subuniverses -/

/- We now prove a bunch of things about an arbitrary reflective subuniverse. -/
section Reflective_Subuniverse
  Context (O : ReflectiveSubuniverse).

  /- Functoriality of [O_rec] homotopies -/
  definition O_rec_homotopy {P Q : Type} [H : In ∘ Q] (f g : P → Q) (pi : f == g)
  : O_rec f == O_rec g.
  /-begin
    apply O_indpaths; intro x.
    etransitivity.
    { apply O_rec_beta. }
    { etransitivity.
      { exact (pi _). }
      { symmetry; apply O_rec_beta. } }
  end-/

  /- If [T] is in the subuniverse, then [to ∘ T] is an equivalence. -/
  definition isequiv_to_O_inO [instance] (T : Type) [H : In ∘ T] : IsEquiv (to ∘ T).
  /-begin
    pose (g := O_rec idmap).
    refine (isequiv_adjointify (to ∘ T) g _ _).
    - refine (O_indpaths (to ∘ T ∘ g) idmap _).
      intros x; unfold compose.
      apply ap.
      apply O_rec_beta.
    - intros x.
      apply O_rec_beta.
  end-/

  definition equiv_to_O (T : Type) [H : In ∘ T] : T ≃ ∘ T :=
       Equiv.mk T (O T) (to ∘ T) _.

  section Functor

    /- In this section, we see that [O] is a functor. -/
    
    definition O_functor {A B : Type} (f : A → B) : ∘ A → ∘ B :=
         O_rec (to ∘ B ∘ f).

    /- Functoriality on composition -/
    definition O_functor_compose {A B C : Type} (f : A → B) (g : B → C)
    : (O_functor (g ∘ f)) == (O_functor g) ∘ (O_functor f).
    /-begin
      apply O_indpaths; intros x; unfold compose.
      refine (O_rec_beta (to ∘ C ∘ g ∘ f) x ⬝ _).
      transitivity (O_functor g (to ∘ B (f x))).
      - symmetry. exact (O_rec_beta (to ∘ C ∘ g) (f x)).
      - apply ap; symmetry.
        exact (O_rec_beta (to ∘ B ∘ f) x).
    end-/

    /- Functoriality on homotopies (2-functoriality) -/
    definition O_functor_homotopy {A B : Type} (f g : A → B) (pi : f == g)
    : O_functor f == O_functor g.
    /-begin
      refine (O_indpaths _ _ _); intros x.
      refine (O_rec_beta (to ∘ B ∘ f) x ⬝ _).
      refine (_ ⬝ (O_rec_beta (to ∘ B ∘ g) x)⁻¹).
      unfold compose; apply ap.
      apply pi.
    end-/

    /- Hence functoriality on commutative squares -/
    definition O_functor_square {A B C X : Type} (pi1 : X → A) (pi2 : X → B)
               (f : A → C) (g : B → C) (comm : (f ∘ pi1) == (g ∘ pi2))
    : ( (O_functor f) ∘ (O_functor pi1) )
      == ( (O_functor g) ∘ (O_functor pi2) ).
    /-begin
      intros x.
      transitivity (O_functor (f ∘ pi1) x).
      - symmetry; apply O_functor_compose.
      - transitivity (O_functor (g ∘ pi2) x).
        × apply O_functor_homotopy, comm.
        × apply O_functor_compose.
    end-/

    /- Functoriality on identities -/
    definition O_functor_idmap (A : Type)
    : @O_functor A A idmap == idmap.
    /-begin
      refine (O_indpaths _ _ _); intros x.
      apply O_rec_beta.
    Qed.

    /- 3-functoriality, as an example use of [O_ind2paths] -/
    definition O_functor_2homotopy {A B : Type} {f g : A → B}
               (p q : f == g) (r : p == q)
    : O_functor_homotopy f g p == O_functor_homotopy f g q.
    Proof.
      refine (O_ind2paths _ _ _); intros x.
      unfold O_functor_homotopy, composeD.
      do 2 rewrite O_indpaths_beta.
      apply whiskerL, whiskerR, ap, r.
    /- Of course, if we wanted to prove 4-functoriality, we'd need to make this transparent. -/
    Qed.

    /- Naturality of [to O] -/
    definition to_O_natural {A B : Type} (f : A → B)
    : (O_functor f) ∘ (to ∘ A) == (to ∘ B) ∘ f :=
       (O_rec_beta _).

    /- The pointed endofunctor ([O],[to O]) is well-pointed -/
    definition O_functor_wellpointed (A : Type)
    : O_functor (to ∘ A) == to ∘ (O A).
    Proof.
      refine (O_indpaths _ _ _); intros x.
      apply to_O_natural.
    end-/

    /- Preservation of equivalences -/
    definition isequiv_O_functor [instance] {A B : Type} (f : A → B) [H : IsEquiv _ _ f]
    : IsEquiv (O_functor f).
    /-begin
      refine (isequiv_adjointify (O_functor f) (O_functor f⁻¹) _ _).
      - intros x.
        refine ((O_functor_compose _ _ x)⁻¹ ⬝ _).
        refine (O_functor_homotopy _ idmap _ x ⬝ _).
        + intros y; apply eisretr.
        + apply O_functor_idmap.
      - intros x.
        refine ((O_functor_compose _ _ x)⁻¹ ⬝ _).
        refine (O_functor_homotopy _ idmap _ x ⬝ _).
        + intros y; apply eissect.
        + apply O_functor_idmap.
    end-/
      
    definition equiv_O_functor {A B : Type} (f : A ≃ B)
    : ∘ A ≃ ∘ B :=
       Equiv.mk _ _ (O_functor f) _.

    /- Postcomposition respects [O_rec] -/
    definition O_rec_postcompose {A B C : Type} [H : In ∘ B] {C_inO : In ∘ C}
               (f : A → B) (g : B → C)
    : g ∘ O_rec f == O_rec (g ∘ f).
    /-begin
      refine (O_indpaths _ _ _); intros x; unfold compose.
      transitivity (g (f x)).
      - apply ap. apply O_rec_beta.
      - symmetry. exact (O_rec_beta (g ∘ f) x).
    end-/

  End Functor.

  section Replete

    /- An equivalent formulation of repleteness is that a type lies in the subuniverse as soon as its unit map is an equivalence. -/
    definition inO_isequiv_to_O (T:Type)
    : IsEquiv (to ∘ T) → In ∘ T :=
       λ_, inO_equiv_inO (O T) (to ∘ T)⁻¹.

    /- We don't make this an ordinary instance, but we allow it to solve [In O] constraints if we already have [IsEquiv] as a hypothesis.  -/
    Hint Immediate inO_isequiv_to_O : typeclass_instances.

    definition inO_iff_isequiv_to_O (T:Type)
    : In ∘ T <-> IsEquiv (to ∘ T).
    /-begin
      split; exact _.
    end-/

    /- Thus, [T] is in a subuniverse as soon as [to ∘ T] admits a retraction. -/
    definition inO_to_O_retract (T:Type) (mu : ∘ T → T)
    : Sect (to ∘ T) mu → In ∘ T.
    /-begin
      unfold Sect; intros H.
      apply inO_isequiv_to_O.
      apply isequiv_adjointify with (g:=mu).
      - refine (O_indpaths (to ∘ T ∘ mu) idmap _).
        intros x; exact (ap (to ∘ T) (H x)).
      - exact H.
    end-/

  End Replete.

  section OInverts

    /- The maps that are inverted by the reflector.  Note that this notation is NOT GLOBAL, it only exists in this section. -/
    Local Notation O_inverts f := (IsEquiv (O_functor f)).

    definition O_inverts_O_unit [instance] (A : Type)
    : O_inverts (to ∘ A).
    /-begin
      refine (isequiv_homotopic (to ∘ (O A)) _).
      intros x; symmetry; apply O_functor_wellpointed.
    end-/

    /- A map between modal types that is inverted by [O] is already an equivalence. -/
    definition isequiv_O_inverts {A B : Type} [H : In ∘ A] [H : In ∘ B]
      (f : A → B) [H : O_inverts f]
    : IsEquiv f.
    /-begin
      refine (isequiv_commsq' f (O_functor f) (to ∘ A) (to ∘ B) _).
      apply to_O_natural.
    end-/

    definition equiv_O_inverts {A B : Type} [H : In ∘ A] [H : In ∘ B]
      (f : A → B) [H : O_inverts f]
    : A ≃ B :=
       Equiv.mk _ _ f (isequiv_O_inverts f).

    definition to_O_inv_natural {A B : Type} [H : In ∘ A] [H : In ∘ B]
               (f : A → B)
    : (to ∘ B)⁻¹ ∘ (O_functor f) == f ∘ (to ∘ A)⁻¹.
    /-begin
      refine (O_indpaths _ _ _); intros x.
      unfold compose; apply moveR_equiv_V.
      refine (to_O_natural f x ⬝ _).
      unfold compose; do 2 apply ap.
      symmetry; apply eissect.
    end-/

    /- Two maps between modal types that become equal after applying [O_functor] are already equal. -/
    definition O_functor_faithful_inO {A B : Type} [H : In ∘ A] [H : In ∘ B]
      (f g : A → B) (e : O_functor f == O_functor g)
      : f == g.
    /-begin
      intros x.
      refine (ap f (eissect (to ∘ A) x)⁻¹ ⬝ _).
      refine (_ ⬝ ap g (eissect (to ∘ A) x)).
      transitivity ((to ∘ B)⁻¹ (O_functor f (to ∘ A x))).
      + symmetry; apply to_O_inv_natural.
      + transitivity ((to ∘ B)⁻¹ (O_functor g (to ∘ A x))).
        × apply ap, e.
        × apply to_O_inv_natural.
    end-/

    /- Any map to a type in the subuniverse that is inverted by [O] must be equivalent to [to O].  More precisely, the type of such maps is contractible. -/
    definition typeof_to_O (A : Type) :=
         ΣOA : Type, ΣOu : A → OA, ((In ∘ OA) × (O_inverts Ou)) .

    definition contr_typeof_O_unit [instance] [H : Univalence] (A : Type)
    : is_contr (typeof_to_O A).
    /-begin
      exists (O A ; (to ∘ A ; (_ , _))).
      intros [OA [Ou [? ?]]].
      pose (f := O_rec Ou : ∘ A → OA).
      pose (g := (O_functor Ou)⁻¹ ∘ to ∘ OA : (OA → ∘ A)).
      assert (IsEquiv f).
      { refine (isequiv_adjointify f g _ _).
        - apply O_functor_faithful_inO; intros x.
          rewrite O_functor_idmap.
          fold (f ∘ g); rewrite O_functor_compose.
          unfold g.
          simpl rewrite (O_functor_compose (to ∘ OA) (O_functor Ou)⁻¹).
          rewrite O_functor_wellpointed.
          simpl rewrite (to_O_natural (O_functor Ou)⁻¹ x).
          refine (to_O_natural f _ ⬝ _).
          set (y := (O_functor Ou)⁻¹ x).
          transitivity (O_functor Ou y); try apply eisretr.
          unfold f, O_functor, compose.
          apply O_rec_postcompose.
        - refine (O_indpaths _ _ _); intros x.
          unfold f, compose.
          rewrite O_rec_beta. unfold g.
          apply moveR_equiv_V.
          symmetry; apply to_O_natural.
      }
      refine (path_sigma _ _ _ _ _); cbn.
      - exact (path_universe f).
      - rewrite transport_sigma.
        refine (path_sigma _ _ _ _ _); cbn; try apply path_ishprop.
        apply path_arrow; intros x.
        rewrite transport_arrow_fromconst.
        rewrite transport_path_universe.
        unfold f; apply O_rec_beta.
    Qed.

  End OInverts.

  section Types

    /- The [unit] type -/
    definition inO_unit [instance] : In ∘ unit.
    Proof.
      apply inO_to_O_retract with (mu := λx, star).
      exact (@contr unit _).
    end-/

    /- It follows that any contractible type is in [O]. -/
    definition inO_contr [instance] {A : Type} [H : is_contr A] : In ∘ A.
    /-begin
      exact (inO_equiv_inO unit (equiv_inverse equiv_contr_unit)).
    end-/

    /- And that the reflection of a contractible type is still contractible. -/
    definition contr_O_contr [instance] {A : Type} [H : is_contr A] : is_contr (O A).
    /-begin
      exact (contr_equiv A (to ∘ A)).
    end-/

    /- Dependent product and arrows -/
    /- definition 7.7.2 -/
    definition inO_Π[instance] {fs : Funext} (A:Type) (B:A → Type) 
    : (Πx, (In ∘ (B x)))
      → (In ∘ (Πx:A, (B x))).
    /-begin
      intro H.
      pose (ev := λx, (λ(f:(Πx, (B x))), f x)).
      pose (zz := λx:A, O_rec (ev x)).
      apply inO_to_O_retract with (mu := λz, λx, zz x z).
      intro phi.
      unfold zz, ev; clear zz; clear ev.
      apply path_forall; intro x.
      exact (O_rec_beta (λf : Πx0, (B x0), f x) phi).
    end-/

    definition inO_arrow [instance] {fs : Funext} (A B : Type) [H : In ∘ B]
    : In ∘ (A → B).
    /-begin
      apply inO_forall.
      intro a. exact _.
    end-/

    /- Product -/
    definition inO_prod [instance] (A B : Type) [H : In ∘ A] [H : In ∘ B]
    : In ∘ (A*B).
    /-begin
      apply inO_to_O_retract with
        (mu := λX, (@O_rec _ (A × B) A _ pr1 X , O_rec pr2 X)).
      intros [a b]; apply path_prod; simpl.
      - exact (O_rec_beta pr1 (a,b)). 
      - exact (O_rec_beta pr2 (a,b)).
    end-/

    /- We show that [OA*OB] has the same universal property as [O(A*B)] -/

    definition equiv_O_prod_unit_precompose
               {fs : Funext} (A B C : Type) [H : In ∘ C]
    : ((O A) × (O B) → C) ≃ (A × B → C).
    /-begin
      apply (equiv_compose' (equiv_uncurry A B C)).
      refine (equiv_compose' _ (equiv_inverse (equiv_uncurry (O A) (O B) C))).
      apply (equiv_compose' (equiv_o_to_O _ A (B → C))); simpl.
      apply equiv_postcompose'.
      exact (equiv_o_to_O _ B C).
    end-/

    /- The preceding equivalence turns out to be actually (judgmentally!) precomposition with the following function. -/
    definition O_prod_unit (A B : Type) : A × B → ∘ A × ∘ B :=
         functor_prod (to ∘ A) (to ∘ B).

    /- From this, we can define the comparison map for products, and show that precomposing with it is also an equivalence. -/
    definition O_prod_cmp (A B : Type) : ∘ (A × B) → ∘ A × ∘ B :=
         O_rec (O_prod_unit A B).

    definition isequiv_O_prod_cmp [instance] (A B : Type)
    : IsEquiv (O_prod_cmp A B).
    /-begin
      refine (isequiv_adjointify _ _ _ _).
      { apply prod_ind; intro a.
        apply O_rec; intro b; revert a.
        apply O_rec; intro a.
        apply (to O).
        exact (a, b). }
      { unfold prod_ind, O_prod_cmp, O_prod_unit.
        intros [oa ob].
        revert ob; refine (O_indpaths _ _ _); intros b.
        revert oa; refine (O_indpaths _ _ _); intros a.
        cbn. abstract (repeat rewrite O_rec_beta; reflexivity). }
      { unfold prod_ind, O_prod_cmp, O_prod_unit.
        refine (O_indpaths _ _ _); intros [a b]; cbn.
        abstract (repeat ⟨rewrite O_rec_beta, cbn⟩; reflexivity). }
    end-/

    definition isequiv_O_prod_cmp_precompose
      {fs : Funext} (A B C : Type) {C_inO : In ∘ C}
    : IsEquiv (λh : ∘ A × ∘ B → C, h ∘ O_prod_cmp A B).
    /-begin
      apply isequiv_precompose; exact _.
    end-/

    definition equiv_O_prod_cmp {fs : Funext} (A B : Type)
    : ∘ (A × B) ≃ (O A × ∘ B) :=
       Equiv.mk _ _ (O_prod_cmp A B) _.

    /- Dependent sums -/
    /- definition 7.7.4 -/
    definition inO_sigma_from_O_ind
    : (Π(A:Type@{i}) (B: (O A) → Type@{j}) [H : Πa, In@{u a j] ∘ (B a)}
              (g : Π(a:A), (B (to ∘ A a))),
         {f : Π(z:O A), (B z) & Πa:A, f (to@{u a i} ∘ A a) ≈ g a})
      ->
      (Π(A:Type@{i}) (B:A → Type@{j}) [H : In@{u a i] ∘ A} [H : Πa, In@{u a j] ∘ (B a)},
         (In@{u a j} ∘ (sig@{i j} (λx:A, B x)))).
    /-begin
      intros H A B ? ?.
             pose (h := λx, @O_rec _ (Σx:A, B x) A _ dpr1 x).
      pose (p := (λz, O_rec_beta dpr1 z)
                 : h ∘ (to ∘ _) == dpr1).
      pose (g := λz, (transport B ((p z)⁻¹) z.2)).
      simpl in *.
      specialize (H (Σx:A, B x) (B ∘ h) _ g).
      destruct H as [f q].
      apply inO_to_O_retract with (mu := λw, ⟨h w, f w⟩).
      intros [x1 x2].
      refine (path_sigma B _ _ _ _); simpl.
      - apply p.
      - rewrite (q ⟨x1,x2⟩).
        unfold g; simpl. exact (transport_pV B _ _).
    Qed.

    definition O_ind_from_inO_sigma
    /- Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3811 -/
    : (Π(A:Type@{i}) (B:A → Type@{j}) {A_inO : In@{u a i} ∘ A} [H : Πa, In@{u a j] ∘ (B a)},
         (In@{u a j} ∘ (sig@{i j} (λx:A, B x))))
      ->
      (Π(A:Type@{i}) (B: (O A) → Type@{j}) [H : Πa, In@{u a j] ∘ (B a)}
              (g : Π(a:A), (B (to ∘ A a))),
         {f : Π(z:O A), (B z) & Πa:A, f (to@{u a i} ∘ A a) ≈ g a}).
    Proof.
      intro H. intros A B ? g.
      pose (Z := sigT B).
      assert (In@{u a j} ∘ Z).
      { apply H; [ exact _ | assumption ]. }
      pose (g' := (λa:A, ⟨to ∘ A a , g a⟩) : A → Z).
      pose (f' := O_rec g').
      pose (eqf := (O_rec_beta g')  : f' ∘ to ∘ A == g').
      pose (eqid := O_indpaths (dpr1 ∘ f') idmap
                               (λx, ap dpr1 (eqf x))).
      exists (λz, transport B (eqid z) ((f' z).2)); intros a.
      unfold eqid. rewrite O_indpaths_beta.
      exact (pr2_path (O_rec_beta g' a)).
    end-/

    /- Paths -/

    definition inO_paths [instance] (S : Type) {S_inO : In ∘ S} (x y : S)
    : In ∘ (x=y).
    /-begin
      refine (inO_to_O_retract _ _ _); intro u.
      - assert (p : (λ_ : ∘ (x=y), x) == (λ_, y)). 
        { refine (O_indpaths _ _ _); unfold compose; simpl.
          intro v; exact v. }
        exact (p u).
      - hnf.
        rewrite O_indpaths_beta; reflexivity.
    Qed.
    
  End Types.

  section Monad

    definition O_monad_mult (A : Type) : ∘ (O A) → ∘ A :=
         O_rec idmap.

    definition O_monad_mult_natural {A B} (f : A → B)
    : O_functor f ∘ O_monad_mult A == O_monad_mult B ∘ O_functor (O_functor f).
    Proof.
      apply O_indpaths; intros x; unfold compose, O_monad_mult.
      simpl rewrite (to_O_natural (O_functor f) x).
      rewrite (O_rec_beta idmap x).
      rewrite (O_rec_beta idmap (O_functor f x)).
      reflexivity.
    Qed.

    definition O_monad_unitlaw1 (A : Type)
    : O_monad_mult A ∘ (to ∘ (O A)) == idmap.
    Proof.
      apply O_indpaths; intros x; unfold compose, O_monad_mult.
      exact (O_rec_beta idmap (to ∘ A x)).
    end-/

    definition O_monad_unitlaw2 (A : Type)
    : O_monad_mult A ∘ (O_functor (to ∘ A)) == idmap.
    Proof.
      apply O_indpaths; intros x; unfold O_monad_mult, O_functor, compose.
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

    definition O_monad_mult_assoc (A : Type)
    : O_monad_mult A ∘ O_monad_mult (O A) == O_monad_mult A ∘ O_functor (O_monad_mult A).
    Proof.
      apply O_indpaths; intros x; unfold O_monad_mult, O_functor, compose.
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

  End Monad.

  section StrongMonad
    Context {fs : Funext}.

    definition O_monad_strength (A B : Type) : A × ∘ B → ∘ (A × B) :=
         λaob, O_rec (λb a, to ∘ (A*B) (a,b)) (pr2 aob) (pr1 aob).

    definition O_monad_strength_natural (A A' B B' : Type) (f : A → A') (g : B → B')
    : O_functor (functor_prod f g) ∘ O_monad_strength A B ==
      O_monad_strength A' B' ∘ functor_prod f (O_functor g).
    Proof.
      intros [a ob]. revert a. apply ap10.
      revert ob; apply O_indpaths.
      intros b; simpl.
      apply path_arrow; intros a.
      unfold O_monad_strength, O_functor, compose; simpl.
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.
      
    /- The diagrams for strength, see http://en.wikipedia.org/wiki/Strong_monad -/
    definition O_monad_strength_unitlaw1 (A : Type)
    : O_functor (@pr2 unit A) ∘ O_monad_strength unit A == @pr2 unit (O A).
    Proof.
      intros [[] oa]; revert oa.
      apply O_indpaths; intros x; unfold O_monad_strength, O_functor, compose. simpl. 
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

    definition O_monad_strength_unitlaw2 (A B : Type)
    : O_monad_strength A B ∘ functor_prod idmap (to ∘ B) == to ∘ (A*B).
    Proof.
      intros [a b].
      unfold O_monad_strength, functor_prod, compose. simpl. 
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

    definition O_monad_strength_assoc1 (A B C : Type)
    : O_functor (equiv_prod_assoc A B C)⁻¹ ∘ O_monad_strength (A*B) C ==
      O_monad_strength A (B*C) ∘ functor_prod idmap (O_monad_strength B C) ∘ (equiv_prod_assoc A B (O C))⁻¹.
    Proof.
      intros [[a b] oc].
      revert a; apply ap10. revert b; apply ap10.
      revert oc; apply O_indpaths.
      intros c; simpl.
      apply path_arrow; intros b. apply path_arrow; intros a.
      unfold O_monad_strength, O_functor, functor_prod, compose. simpl. 
      repeat rewrite O_rec_beta.
      reflexivity.
    Qed.

    definition O_monad_strength_assoc2 (A B : Type)
    : O_monad_mult (A*B) ∘ O_functor (O_monad_strength A B) ∘ O_monad_strength A (O B) ==
      O_monad_strength A B ∘ functor_prod idmap (O_monad_mult B).
    Proof.
      intros [a oob]. revert a; apply ap10.
      revert oob; apply O_indpaths. apply O_indpaths.
      intros b; simpl. apply path_arrow; intros a.
      unfold O_monad_strength, O_functor, O_monad_mult, functor_prod, compose. simpl. 
      repeat ⟨rewrite O_rec_beta, simpl⟩.
      reflexivity.
    Qed.
      
  End StrongMonad.
      
End Reflective_Subuniverse.

/- Make the [O_inverts] notation global. -/
Notation O_inverts ∘ f := (IsEquiv (O_functor ∘ f)).

End ReflectiveSubuniverses_Theory.

/- Restriction of a family of reflective subuniverses -/

/- Recall that an implementation of [ReflectiveSubuniverses] is a family of reflective subuniverses indexed by the type [ReflectiveSubuniverse].  Sometimes we want to consider only a subfamily of a known one, or more generally a restriction of such a family along a function.  The second-class nature of modules makes this a bit of a pain to construct, but we can do it. -/
Module Type ReflectiveSubuniverses_Restriction_Data (Os : ReflectiveSubuniverses).

  Parameter New_ReflectiveSubuniverse : Type2@{u a}.
  Check New_ReflectiveSubuniverse@{u a}.    /- Verify that we have the right number of universes -/

  Parameter ReflectiveSubuniverses_restriction
  : New_ReflectiveSubuniverse@{u a} → Os.ReflectiveSubuniverse@{u a}.
  Check ReflectiveSubuniverses_restriction@{u a}.

End ReflectiveSubuniverses_Restriction_Data.

Module ReflectiveSubuniverses_Restriction
       (Os : ReflectiveSubuniverses)
       (Res : ReflectiveSubuniverses_Restriction_Data Os)
<: ReflectiveSubuniverses.

  definition ReflectiveSubuniverse := Res.New_ReflectiveSubuniverse.

  definition O_reflector (O : ReflectiveSubuniverse@{u a}) :=
       Os.O_reflector@{u a i} (Res.ReflectiveSubuniverses_restriction O).
  definition inO_internal (O : ReflectiveSubuniverse@{u a}) :=
       Os.inO_internal@{u a i} (Res.ReflectiveSubuniverses_restriction O).
  definition O_inO_internal (O : ReflectiveSubuniverse@{u a}) :=
       Os.O_inO_internal@{u a i} (Res.ReflectiveSubuniverses_restriction O).
  definition to (O : ReflectiveSubuniverse@{u a}) :=
       Os.to@{u a i} (Res.ReflectiveSubuniverses_restriction O).
  definition inO_equiv_inO_internal (O : ReflectiveSubuniverse@{u a}) :=
       Os.inO_equiv_inO_internal@{u a i} (Res.ReflectiveSubuniverses_restriction O).
  definition hprop_inO_internal (H : Funext) (O : ReflectiveSubuniverse@{u a}) :=
       Os.hprop_inO_internal@{u a i} H (Res.ReflectiveSubuniverses_restriction O).
  definition extendable_to_O_internal (O : ReflectiveSubuniverse@{u a}) :=
       @Os.extendable_to_O_internal@{u a i j k} (Res.ReflectiveSubuniverses_restriction@{u a} O).

End ReflectiveSubuniverses_Restriction.

/- Union of families of reflective subuniverses -/

/- TODO -/

/- Accessible subuniverses -/

/- An accessible subuniverse is one that is the localization at a small family of maps.  Accessibility is necessary for some constructions, and in practice it's a reasonable hypothesis that includes most examples (though a few examples, such as double negation, may only be accessible if we assume propositional resizing).

We now give the basic definitions related to accessibility, using [ooExtendableAlong] as our notion of equivalence as we did with reflective subuniverses.  The actual construction of a reflective subuniverse by localization will be in [hit/Localization]. -/


Record LocalGenerators :=
  { lgen_indices : Type@{a} ;
    lgen_domain : lgen_indices → Type@{a} ;
    lgen_codomain : lgen_indices → Type@{a} ;
    lgenerator : Πi, lgen_domain i → lgen_codomain i
  }.

Coercion lgenerator : LocalGenerators >-> Funclass.

/- We put this notation in a module so that no one outside of this file will use it unintentionally.  It will be redefined in [hit/Localization] to refer to the localization reflective subuniverse, which is judgmentally the same but will also pick up typeclass inference for [In]. -/
Module Import IsLocal_Internal.
  definition IsLocal f X :=
    (Π(i : lgen_indices f), ooExtendableAlong (f i) (λ_, X)).
End IsLocal_Internal.

Module Type Accessible_ReflectiveSubuniverses
       (Os : ReflectiveSubuniverses).

  Export Os.

  /- In examples (such as localization), the reason we need the extra universe parameter [a] is that it describes the size of the generators.  Therefore, here we intentionally collapse that parameter with the parameter of [LocalGenerators]. -/
  Parameter acc_gen : ReflectiveSubuniverse@{u a} → LocalGenerators@{a}.
  Check acc_gen@{u a}.    /- Verify that we have the right number of universes -/

  Parameter inO_iff_islocal_internal
  : Π(O : ReflectiveSubuniverse@{u a}) (X : Type@{i}),
      /- We call [iff] explicitly to control the number of universe parameters. -/
      iff@{i i i}
         (inO_internal@{u a i} ∘ X)
         (IsLocal@{i i a} (acc_gen@{u a} O) X).
  Check inO_iff_islocal_internal@{u a i}.

End Accessible_ReflectiveSubuniverses.

Module Accessible_ReflectiveSubuniverses_Theory
       (Os : ReflectiveSubuniverses)
       (Acc : Accessible_ReflectiveSubuniverses Os).

  Import Os Acc.
  Module Import Os_Theory := ReflectiveSubuniverses_Theory Os.

  definition inO_iff_islocal
  : ΠO (X : Type), In ∘ X <-> IsLocal (acc_gen O) X :=
     inO_iff_islocal_internal.

  definition O_inverts_generators {O : ReflectiveSubuniverse}
             (i : lgen_indices (acc_gen O))
  : O_inverts ∘ (acc_gen ∘ i).
  Proof.
    pose (ext_dom := pr1 (inO_iff_islocal ∘ (O (lgen_domain (acc_gen O) i))) _).
    pose (ext_cod := pr1 (inO_iff_islocal ∘ (O (lgen_codomain (acc_gen O) i))) _).
    refine (isequiv_adjointify _ _ _ _).
    - apply O_rec.
      exact ((pr1 (ext_dom i 1%nat) (to ∘ _)).1).
    - apply O_indpaths; intros x; simpl.
      rewrite O_rec_beta.
      refine ((pr1 (pr2 (ext_cod i 2)
                        (λx, O_functor ∘ (acc_gen ∘ i)
                                            ((pr1 (ext_dom i 1%nat) (to ∘ _)).1 x))
                        _) _).1 x); intros a.
      rewrite ((pr1 (ext_dom i 1%nat) (to ∘ _)).2 a).
      apply to_O_natural.
    - apply O_indpaths; intros x; simpl.
      simpl rewrite (to_O_natural ∘ (acc_gen ∘ i) x).
      rewrite O_rec_beta.
      apply ((pr1 (ext_dom i 1%nat) (to ∘ _)).2 x).
  Qed.

End Accessible_ReflectiveSubuniverses_Theory.
