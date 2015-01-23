/- -*- mode: coq; mode: visual-line -*- -/

/- Factorizations and factorization systems. -/

Require Import HoTT.Basics HoTT.Types.
Require Import HProp UnivalenceImpliesfunext Extensions.
Require Import HoTT.Tactics.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

/- Factorizations -/

section Factorization

  /- It's important that these are all declared with a single [Context] command, so that the marker [@{i}] refers to the same universe level in all of them. -/
  Context {class1 class2 : Π(X Y : Type@{i}), (X → Y) → Type@{i}}
          {Π(X Y : Type@{i}) (g:X->Y), is_hprop (class1 _ _ g)}
          {Π(X Y : Type@{i}) (g:X->Y), is_hprop (class2 _ _ g)}
          {A B : Type@{i}} {f : A → B}.

  /- A factorization of [f] into a first factor lying in [class1] and a second factor lying in [class2]. -/
  Record Factorization :=
    { intermediate : Type ;
      factor1 : A → intermediate ;
      factor2 : intermediate → B ;
      fact_factors : factor2 ∘ factor1 ∼ f ;
      inclass1 : class1 _ _ factor1 ;
      inclass2 : class2 _ _ factor2
    }.

  definition issig_Factorization :
    { I : Type & { g : A → I & { h : I → B & { p : h ∘ g ∼ f &
      Σgin1 : class1 _ _ g, class2 _ _ h }}}}
      ≃ Factorization.
  /-begin
    issig Build_Factorization intermediate factor1 factor2 fact_factors inclass1 inclass2.
  end-/

  /- This enables [simpl rewrite] to unfold [compose]. -/
  Local Arguments compose / .

  /- A path between factorizations is equivalent to a structure of the following sort. -/
  Record PathFactorization {fact fact' : Factorization} :=
    { path_intermediate : intermediate fact ≃ intermediate fact' ;
      path_factor1 : path_intermediate ∘ factor1 fact ∼ factor1 fact' ;
      path_factor2 : factor2 fact ∼ factor2 fact' ∘ path_intermediate ;
      path_fact_factors : Πa, path_factor2 (factor1 fact a)
                          ⬝ ap (factor2 fact') (path_factor1 a)
                          ⬝ fact_factors fact' a
                          = fact_factors fact a
    }.

  /- It's easy to extract such a structure from an actual path between factorizations. -/
  definition pathfactorization_path (fact fact' : Factorization)
    : (fact = fact') → @PathFactorization fact fact'.
  /-begin
    intros p.
    refine (Build_PathFactorization fact fact' _ _ _ _); destruct p.
    - exact (equiv_idmap (intermediate fact)).
    - exact (λa, 1).
    - exact (λx, 1).
    - exact (λa, concat_1p _).
  end-/

  /- The converse, however, is more work. In the proof of definition 7.6.6, the book glosses over this theorem with the phrase "by univalence and the characterization of paths and transport in Sigma-types, function types, and path types".  Which is arguably fair informally, because it's "obvious", but it turns out to be a good deal of work to keep track of all the transport lemmas and apply naturality in the right places. -/
  section PathFactorization
    Context [H : Univalence] {fact fact' : Factorization}
            (pf : @PathFactorization fact fact').

    /- Let's give short names to the fields of [pf]. -/
    Let II := path_intermediate pf.
    Let ff1 := path_factor1 pf.
    Let ff2 := path_factor2 pf.
    Let fff := path_fact_factors pf.

    /- Each of those fields now induces a corresponding (dependent) path.  The first one is easy. -/
    Local definition II' : intermediate fact = intermediate fact' :=
         path_universe II.

    /- The second is slightly harder, but at least its type is obvious. -/
    Local definition ff1'
      : transport (λX, A → X) II' (factor1 fact) = factor1 fact'.
    /-begin
      apply path_arrow; intros a.
      refine (transport_arrow_fromconst (C := idmap) _ _ a ⬝ _).
      etransitivity; [ apply transport_path_universe | ].
      apply ff1.
    end-/

    /- The type of the third is just like the type of the second, but its proof is a bit more complicated because the type of [ff2] isn't exactly the way it appears naturally here. -/
    Local definition ff2'
      : transport (λX, X → B) II' (factor2 fact) = factor2 fact'.
    /-begin
      apply path_arrow; intros a.
      refine (transport_arrow_toconst (B := idmap) _ _ a ⬝ _).
      etransitivity; [ apply ap, transport_path_universe_V | ].
      etransitivity; [ apply ff2 | ].
      unfold compose; apply ap.
      apply eisretr.
    end-/

    /- Finally, even the type of this one is rather intimidating.  It's hard to justify this type until you get to the end of the proof of [path_factorization], below, and see that it's exactly what we need to complete it.  We prove it separately first so that we can make it opaque for performance reasons (roughly a 2x speedup).  Note that we can't make [II'], [ff1'], or [ff2'] opaque, since they have to be unfolded in this proof and the next. -/
    Local definition fff' (a : A)
    : (transportD2 (λX, A → X) (λX, X → B)
                   (λX g h, {_ : Πa : A, h (g a) = f a &
                                  Σ_ : class1 A X g, class2 X B h})
                   II' (factor1 fact) (factor2 fact)
                   (fact_factors fact; ⟨inclass1 fact, inclass2 fact⟩)).1 a =
      ap (transport (λX, X → B) II' (factor2 fact))
        (transport_arrow_fromconst II' (factor1 fact) a
          ⬝ transport_path_universe II (factor1 fact a)
          ⬝ ff1 a)
        ⬝ transport_arrow_toconst II' (factor2 fact) (factor1 fact' a)
        ⬝ ap (factor2 fact) (transport_path_universe_V II (factor1 fact' a))
        ⬝ ff2 (II⁻¹ (factor1 fact' a))
        ⬝ ap (factor2 fact') (retr II (factor1 fact' a))
        ⬝ fact_factors fact' a.
    /-begin
      /- The name of the game is looking for naturality properties so that we can apply [fff], so [long_path_scope] is helpful to be able to see the shape of the goal better. -/
      Open Scope long_path_scope.
      /- Here is a fairly obvious beginning. -/
      rewrite (ap_transport_arrow_toconst (B := idmap) (C := B)).
      /- Now we set up for a naturality -/
      simpl rewrite (@ap_compose _ _ _ (transport idmap (path_universe II)⁻¹)
                                 (factor2 fact)).
      rewrite <- ap_p_pp; rewrite_moveL_Mp_p.
      /- We need to supply [ff2] here or else it will rewrite in the wrong place. -/
      simpl rewrite (concat_Ap ff2).
      /- Next is another naturality  -/
      simpl rewrite ap_compose.
      simpl rewrite <- ap_p_pp.
      repeat rewrite (ap_pp (transport idmap (path_universe II)⁻¹)).
      rewrite concat_pA_p.
      /- And another one -/
      repeat rewrite (ap_pp II).
      rewrite <- (ap_compose (II⁻¹) II); unfold compose.
      rewrite (concat_pA1_p (retr II) (ff1 a)).
      /- Now we use the triangle identity of our equivalence [II]. -/
      rewrite (ap_pp (factor2 fact')).
      unfold compose; rewrite eisadj.
      /- And one more naturality -/
      repeat rewrite concat_p_pp.
      repeat rewrite <- ap_pp.
      rewrite <- ap_compose.
      simpl rewrite <- (concat_Ap ff2).
      rewrite_moveL_Mp_p.
      /- Finally we can use [fff]! -/
      refine (_ ⬝ (fff a)⁻¹).
      do 2 rewrite_moveR_Vp_p.
      /- Now we still have a mess, but with a little futzing we can put it into a form that we can do path induction over.  The point is to make it all a function of [path_universe II].  In particular, we need to eliminate [sect II], which we do with [transport_path_universe_Vp]. -/
      rewrite (ap_pp (transport idmap (path_universe II)⁻¹)).
      with_rassoc ltac:(rewrite (ap_pp (factor2 fact))).
      unfold II'; rewrite transport_path_universe_Vp.
      /- This mess is completely general in [path_universe II]! -/
      fold II. set (p := path_universe II); clearbody p.
      case p; cbn. auto with path_hints.
      Close Scope long_path_scope.
    Qed.

    /- Finally, we're ready to prove the main theorem. -/
    definition path_factorization : fact = fact'.
    Proof.
      /- The idea is of course to decompose [Factorization] as a sigma and use [path_sigma] over and over again.  It's fairly easy to insert [II], [ff1], and [ff2] in the right places. -/
      apply ((ap issig_Factorization⁻¹)⁻¹); cbn.
      refine (path_sigma' _ II' _); cbn.
      refine (transport_sigma_' _ _ ⬝ _); cbn.
      refine (path_sigma' _ ff1' _); cbn.
      refine (transport_sigma' _ _ ⬝ _); cbn.
      refine (path_sigma' _ ff2' _); cbn.
      /- Now we have a gigantic mess, but fortunately it simplifies a great deal because the last two components are hprops. -/
      refine (transport_sigma (A := intermediate fact' → B)
                              (B := λg, g ∘ factor1 fact' ∼ f)
                              _ _ ⬝ _); cbn.
      refine (path_sigma' _ _ _); cbn.
      2:apply path_ishprop.
      /- It's still pretty scary-looking, but we press ahead undaunted, looking for transport redexes and path redexes. -/
      apply path_forall; intros a.
      unfold pointwise_paths.
      rewrite transport_pi_constant, transport_paths_Fl.
      unfold II', ff1', ff2'.
      rewrite ap_apply_l, ap10_path_arrow.
      rewrite transport_sigma_'; cbn.
      rewrite transport_pi_constant, transport_paths_Fl.
      simpl rewrite (@ap_compose _ _ _
                                 (λg:A->intermediate fact', g a)
                                 (λx, transport (λX, X → B) (path_universe II)
                                                     (factor2 fact) x)).
      rewrite ap_apply_l, ap10_path_arrow.
      /- Finally we can apply our monster lemma [fff']. -/
      do 2 apply moveR_Vp; repeat rewrite concat_p_pp.
      exact (fff' a).
    Qed.

  End PathFactorization.
End Factorization.

Arguments Factorization class1 class2 {A B} f.
Arguments PathFactorization {class1 class2 A B f} fact fact'.

/- This enables us to talk about "the image of a map" as a factorization but also as the intermediate object appearing in it, as is common in informal mathematics. -/
Coercion intermediate : Factorization >-> Sortclass.

/- Factorization Systems -/

/- A ("unique" or "orthogonal") factorization system consists of a couple of classes of maps, closed under composition, such that every map admits a unique factorization. -/
Record FactorizationSystem :=
  { class1 : Π{X Y : Type@{i}}, (X → Y) → Type ;
    ishprop_class1 : Π{X Y : Type@{i}} (g:X->Y), is_hprop (class1 g) ;
    class1_isequiv : Π{X Y : Type@{i}} (g:X->Y) {geq:is_equiv g}, class1 g ;
    class1_compose : Π{X Y Z : Type@{i}} (g:X->Y) (h:Y->Z),
                       class1 g → class1 h → class1 (h ∘ g) ;
    class2 : Π{X Y : Type@{i}}, (X → Y) → Type ;
    ishprop_class2 : Π{X Y : Type@{i}} (g:X->Y), is_hprop (class2 g) ;
    class2_isequiv : Π{X Y : Type@{i}} (g:X->Y) {geq:is_equiv g}, class2 g ;
    class2_compose : Π{X Y Z : Type@{i}} (g:X->Y) (h:Y->Z),
                       class2 g → class2 h → class2 (h ∘ g) ;
    /- Morally, the uniqueness of factorizations says that [Factorization class1 class2 f] is contractible.  However, in practice we always *prove* that by way of [path_factorization], and we frequently want to *use* the components of a [PathFactorization] as well.  Thus, as data we store the canonical factorization and a [PathFactorization] between any two such, and prove in a moment that this implies contractibility of the space of factorizations. -/
    factor : Π{X Y : Type@{i}} (f:X->Y), Factorization@{i i} (@class1) (@class2) f ;
    path_factor : Π{X Y : Type@{i}} (f:X->Y)
                         (fact : Factorization@{i i} (@class1) (@class2) f)
                         (fact' : Factorization@{i i} (@class1) (@class2) f),
                    PathFactorization@{i i i} fact fact'
  }.

Global Existing Instances ishprop_class1 ishprop_class2.

section FactSys

  Context [H : Univalence] (factsys : FactorizationSystem).

  definition Build_Factorization' {X Y} :=
       @Build_Factorization (@class1 factsys) (@class2 factsys) X Y.

  definition Build_PathFactorization' {X Y} :=
       @Build_PathFactorization (@class1 factsys) (@class2 factsys) X Y.

  /- The type of factorizations is, as promised, contractible. -/
  definition contr_factor {X Y} (f : X → Y)
  : is_contr (Factorization (@class1 factsys) (@class2 factsys) f).
  Proof.
    apply contr_inhabited_hprop.
    - apply hprop_allpath.
      intros fact fact'.
      apply path_factorization; try exact _.
      apply path_factor.
    - apply factor.
  end-/

  /- It follows that the left class is right-cancellable and the right class is left-cancellable. -/
  definition cancelR_class1 {X Y Z} (f : X → Y) (g : Y → Z)
  : class1 factsys f → class1 factsys (g ∘ f) → class1 factsys g.
  /-begin
    intros c1f c1gf.
    destruct (factor factsys g) as [I g1 g2 gf c1g1 c2g2].
    pose (fact  := Build_Factorization' (g ∘ f) Z (g ∘ f) (idmap)
                     (λx, 1) c1gf (class2_isequiv factsys idmap)).
    pose (fact' := Build_Factorization' (g ∘ f) I (g1 ∘ f) g2
                     (λx, gf (f x))
                     (class1_compose factsys f g1 c1f c1g1) c2g2).
    destruct (path_factor factsys (g ∘ f) fact fact')
             as [q q1 q2 qf]; simpl in *.
    refine (transport (class1 factsys) (path_arrow _ _ gf) _).
    refine (class1_compose factsys g1 g2 c1g1 _).
    refine (transport (class1 factsys) (path_arrow q⁻¹ g2 _)
                      (class1_isequiv factsys q⁻¹)).
    unfold pointwise_paths; equiv_intro q x.
    exact (sect q x ⬝ q2 x).
  end-/

  definition cancelL_class2 {X Y Z} (f : X → Y) (g : Y → Z)
  : class2 factsys g → class2 factsys (g ∘ f) → class2 factsys f.
  /-begin
    intros c2g c2gf.
    destruct (factor factsys f) as [I f1 f2 ff c1f1 c2f2].
    pose (fact  := Build_Factorization' (g ∘ f) X (idmap) (g ∘ f)
                     (λx, 1) (class1_isequiv factsys idmap) c2gf).
    pose (fact' := Build_Factorization' (g ∘ f) I f1 (g ∘ f2)
                     (λx, ap g (ff x))
                     c1f1 (class2_compose factsys f2 g c2f2 c2g)).
    destruct (path_factor factsys (g ∘ f) fact fact')
             as [q q1 q2 qf]; simpl in *.
    refine (transport (class2 factsys) (path_arrow _ _ ff) _).
    refine (class2_compose factsys f1 f2 _ c2f2).
    exact (transport (class2 factsys) (path_arrow q f1 q1)
                     (class2_isequiv factsys q)).
  end-/

  /- The two classes of maps are automatically orthogonal, i.e. any commutative square from a [class1] map to a [class2] map has a unique diagonal filler.  For now, we only bother to define the lift; in principle we ought to show that the type of lifts is contractible. -/
  Context {A B X Y : Type@{i}}
          (i : A → B) (c1i : class1 factsys i)
          (p : X → Y) (c2p : class2 factsys p)
          (f : A → X) (g : B → Y) (h : p ∘ f ∼ g ∘ i).

  /- First we factor [f] -/
  Let C  : Type         := intermediate (factor factsys f).
  Let f1 : A → C       := factor1      (factor factsys f).
  Let f2 : C → X       := factor2      (factor factsys f).
  Let ff : f2 ∘ f1 ∼ f := fact_factors (factor factsys f).

  /- and [g] -/
  Let D  : Type         := intermediate (factor factsys g).
  Let g1 : B → D       := factor1      (factor factsys g).
  Let g2 : D → Y       := factor2      (factor factsys g).
  Let gf : g2 ∘ g1 ∼ g := fact_factors (factor factsys g).

  /- Now we observe that [p ∘ f2] and [f1], and [g2] and [g1 ∘ i], are both factorizations of the common diagonal of the commutative square (for which we use [p ∘ f], but we could equally well use [g ∘ i]. -/
  Let fact  : Factorization (@class1 factsys) (@class2 factsys) (p ∘ f) :=
               Build_Factorization' (p ∘ f) C f1 (p ∘ f2)
                 (λa, ap p (ff a))
                 (inclass1 (factor factsys f))
                 (class2_compose factsys f2 p
                                 (inclass2 (factor factsys f))
                                 c2p).
  Let fact' : Factorization (@class1 factsys) (@class2 factsys) (p ∘ f) :=
               Build_Factorization' (p ∘ f) D (g1 ∘ i) g2
                 (λa, gf (i a) ⬝ (h a)⁻¹)
                 (class1_compose factsys i g1 c1i
                                 (inclass1 (factor factsys g)))
                 (inclass2 (factor factsys g)).

  /- Therefore, by the uniqueness of factorizations, we have an equivalence [q] relating them. -/
  Let q  : C ≃ D          := path_intermediate
                                 (path_factor factsys (p ∘ f) fact fact').
  Let q1 : q ∘ f1 ∼ g1 ∘ i := path_factor1
                                 (path_factor factsys (p ∘ f) fact fact').
  Let q2 : p ∘ f2 ∼ g2 ∘ q := path_factor2
                                 (path_factor factsys (p ∘ f) fact fact').

  /- Using this, we can define the lift. -/
  definition lift_factsys : B → X :=
       f2 ∘ q⁻¹ ∘ g1.

  /- And the commutative triangles making it a lift -/
  definition lift_factsys_tri1 : lift_factsys ∘ i ∼ f.
  /-begin
    intros x.
    refine (ap (f2 ∘ q⁻¹) (q1 x)⁻¹ ⬝ _); unfold compose.
    transitivity (f2 (f1 x)).
    + apply ap, eissect.
    + apply ff.
  end-/

  definition lift_factsys_tri2 : p ∘ lift_factsys ∼ g.
  /-begin
    intros x.
    refine (q2 _ ⬝ _); unfold compose.
    transitivity (g2 (g1 x)).
    + apply ap, eisretr.
    + apply gf.
  end-/

  /- Enable [simpl rewrite] to unfold [compose] and [lift_factsys] in the following proof.  It may not be obvious from the proof that the latter is necessary, but [lift_factsys] appears in the invisible implicit point-arguments of [paths].  One way to discover issues of that sort is to turn on printing of all implicit argumnets with [Set Printing All]; another is to use [Set Debug Tactic Unification] and inspect the output to see what [rewrite] is trying and failing to unify. -/
  Local Arguments compose / .
  Local Arguments lift_factsys / .

  /- And finally prove that these two triangles compose to the given commutative square. -/
  definition lift_factsys_square (x : A)
  : ap p (lift_factsys_tri1 x)⁻¹ ⬝ lift_factsys_tri2 (i x) = h x.
  /-begin
    unfold lift_factsys_tri1, lift_factsys_tri2.
    Open Scope long_path_scope.
    /- First we use the one aspect of the uniqueness of factorizations that we haven't mentioned yet. -/
    pose (r := path_fact_factors (path_factor factsys (p ∘ f) fact fact') x
            : q2 (f1 x) ⬝ ap g2 (q1 x) ⬝ (gf (i x) ⬝ (h x)⁻¹) = ap p (ff x)).
    rewrite concat_p_pp in r.
    apply moveL_pM, moveR_Vp in r.
    refine (_ ⬝ r); clear r.
    /- Now we can cancel some whiskered paths on both sides. -/
    repeat rewrite inv_pp; repeat rewrite ap_pp; rewrite ap_V.
    repeat rewrite concat_pp_p; apply whiskerL.
    repeat rewrite concat_p_pp; apply whiskerR.
    /- Next we set up for a naturality. -/
    rewrite ap_compose, <- ap_pp, <- inv_pp.
    simpl rewrite <- ap_pp.
    rewrite <- ap_V, <- ap_compose.
    simpl rewrite (concat_Ap q2).
    /- Now we can cancel another path -/
    rewrite concat_pp_p; apply whiskerL.
    /- And set up for an application of [ap]. -/
    simpl rewrite ap_compose.
    simpl rewrite <- ap_pp.
    apply ap.
    /- Now we apply the triangle identity [adj]. -/
    rewrite inv_pp, ap_pp, ap_V.
    simpl rewrite <- eisadj.
    /- Finally, we rearrange and it becomes a naturality square. -/
    rewrite concat_pp_p; apply moveR_Vp.
    rewrite <- ap_V, inv_V, <- ap_compose.
    exact (concat_A1p (retr q) (q1 x)).
    Close Scope long_path_scope.
  Qed.

End FactSys.

section FactsysExtensions
  Context {factsys : FactorizationSystem} {ua : Univalence}.

  /- We can deduce the lifting property in terms of extensions fairly easily from the version in terms of commutative squares. -/
  definition extension_factsys {A B : Type}
             (f : A → B) {c1f : class1 factsys f}
             (P : B → Type) (c2P : class2 factsys (@dpr1 B P))
             (d : Πa:A, P (f a))
  : ExtensionAlong f P d.
  Proof.
    pose (e := lift_factsys factsys f c1f dpr1 c2P
                            (λa, ⟨f a , d a⟩) idmap
                            (λa, 1)).
    pose (e2 := lift_factsys_tri2 factsys f c1f dpr1 c2P
                            (λa, ⟨f a , d a⟩) idmap
                            (λa, 1)).
    exists (λa, (e2 a) ▹ (e a).2).
    intros a.
    pose (e1 := lift_factsys_tri1 factsys f c1f dpr1 c2P
                            (λa, ⟨f a , d a⟩) idmap
                            (λa, 1) a
                : e (f a) = ⟨f a , d a⟩).
    pose (e3 := moveL_M1 _ _ (((ap_V _ _)⁻¹ @@ 1)
                ⬝ lift_factsys_square factsys f c1f dpr1 c2P
                            (λa, ⟨f a , d a⟩) idmap
                            (λa, 1) a)
                : e2 (f a) = pr1_path e1).
    refine (ap (λp, transport P p (e (f a)).2) e3 ⬝ _).
    exact (pr2_path e1).
  end-/

End FactsysExtensions.
