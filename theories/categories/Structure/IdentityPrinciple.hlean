/- The Structure Identity Principle -/
Require Import Category.Core Category.Univalent Category.Morphisms.
Require Import Structure.Core.
Require Import HProp Types.Sigma Types.Record Trunc Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope category_scope.
Local Open Scope morphism_scope.
Local Open Scope structure_scope.

/- Quoting the Homotopy Type Theory Book (with slight changes for
    notational consistency): -/

/- definition (Structure identity principle): If [X] is a category and
    [(P, H)] is a standard notion of structure over [X], then the
    precategory [Str_{(P, H)}(X)] is a category. -/
section sip
  Variable X : PreCategory.
  Variable P : NotionOfStructure X.
  Context [H : IsCategory X].
  Context [H : @IsStandardNotionOfStructure X P].

  Let StrX := @precategory_of_structures X P.

  definition sip_isotoid_helper (xa yb : StrX)
             (f : xa <~=~> yb)
  : xa.1 <~=~> yb.1.
  /-begin
    exists (PreCategoryOfStructures.f (f : morphism _ _ _)).
    exists (PreCategoryOfStructures.f f⁻¹).
    - exact (ap (@PreCategoryOfStructures.f _ _ _ _) (@left_inverse _ _ _ _ f)).
    - exact (ap (@PreCategoryOfStructures.f _ _ _ _) (@right_inverse _ _ _ _ f)).
  end-/

  definition sip_isotoid_helper_refl (xa : StrX)
  : @sip_isotoid_helper xa xa (reflexivity _) = reflexivity _.
  /-begin
    unfold sip_isotoid_helper, reflexivity, isomorphic_refl.
    apply ap.
    apply path_ishprop.
  end-/

  definition sip_helper x y (p : x = y) (a : P x) (b : P y)
  : transport P p a = b
    <-> is_structure_homomorphism P _ _ (idtoiso X p) a b *
        is_structure_homomorphism P _ _ (idtoiso X p)⁻¹ b a.
  /-begin
    split.
    - intros; path_induction; split; apply reflexivity.
    - intros [H0 H1]; path_induction; simpl in *.
      apply antisymmetry_structure; assumption.
  end-/

  definition sip_isotoid (xa yb : StrX)
             (f : xa <~=~> yb)
  : xa = yb.
  /-begin
    refine (path_sigma_uncurried
              _ _ _
              (isotoid
                 X
                 xa.1
                 yb.1
                 (sip_isotoid_helper f);
               _)).
    apply sip_helper; simpl.
    split;
      lazymatch goal with
        | [ |- context[idtoiso ?X ((isotoid ?X ?x ?y) ?m)] ]
          => pose proof (retr (@idtoiso X x y) m) as H';
             pattern (idtoiso X ((isotoid X x y) m))
      end;
      refine (transport _ H'⁻¹ _); clear H'; simpl;
      apply PreCategoryOfStructures.h.
  end-/

  definition sip_isotoid_refl xa
  : @sip_isotoid xa xa (reflexivity _) = reflexivity _.
  /-begin
    refine (_ ⬝ eta_path_sigma_uncurried _).
    refine (ap (path_sigma_uncurried _ _ _) _).
    apply equiv_path_sigma_hprop.
    simpl.
    refine (_ ⬝ retr (isotoid X xa.1 xa.1) 1%path).
    apply ap.
    apply sip_isotoid_helper_refl.
  end-/

  definition path_f_idtoiso_precategory_of_structures xa yb (p : xa = yb)
  : PreCategoryOfStructures.f (idtoiso (precategory_of_structures P) p : morphism _ _ _)
    = idtoiso X p..1.
  /-begin
    induction p; reflexivity.
  end-/

  definition structure_identity_principle_helper
        (xa yb : StrX)
        (x : xa <~=~> yb)
  : PreCategoryOfStructures.f
      (idtoiso (precategory_of_structures P) (sip_isotoid x) : morphism _ _ _)
    = PreCategoryOfStructures.f (x : morphism _ _ _).
  /-begin
    refine (path_f_idtoiso_precategory_of_structures _ ⬝ _).
    refine ((ap _ (ap _ _))
              ⬝ (ap (@morphism_isomorphic _ _ _)
                    (retr (@idtoiso X xa.1 yb.1) (sip_isotoid_helper _)))).
    exact (pr1_path_sigma_uncurried _).
  end-/

  Global Instance structure_identity_principle
  : IsCategory (precategory_of_structures P).
  /-begin
    intros xa yb.
    refine (isequiv_adjointify
              _ (@sip_isotoid xa yb)
              _ _);
      intro; simpl in *.
    - abstract (
          apply path_isomorphic; simpl;
          apply PreCategoryOfStructures.path_morphism;
          apply structure_identity_principle_helper
        ).
    - abstract (induction x; apply sip_isotoid_refl).
  end-/
End sip.
