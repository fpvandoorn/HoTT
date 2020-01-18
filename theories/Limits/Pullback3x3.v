Require Import HoTT.Basics HoTT.Types.
Require Import Fibrations.
Require Import Limits.Pullback.
Require Import WildCat.
Require Import Cubical.PathSquare.
Require Import PathAny.

Section FunctorPullback.

  Context {A1 B1 C1 A2 B2 C2}
          (f1 : B1 -> A1) (g1 : C1 -> A1)
          (f2 : B2 -> A2) (g2 : C2 -> A2)
          (h : A1 -> A2) (k : B1 -> B2) (l : C1 -> C2)
          (p : f2 o k == h o f1) (q : h o g1 == g2 o l).

  Definition functor_pullback' : Pullback f1 g1 -> Pullback f2 g2
    := functor_sigma k
        (fun b1 => (functor_sigma l
                     (fun c1 e1 => p b1 @ ap h e1 @ q c1))).

  Definition functor_equiv_path_pullback_square {x y : Pullback f1 g1}
    (p1 : x.1 = y.1) (p2 : x.2.1 = y.2.1) (r : PathSquare x.2.2 y.2.2 (ap f1 p1) (ap g1 p2)) 
    : PathSquare ((functor_pullback' x).2).2 ((functor_pullback' y).2).2 (ap f2 (ap k p1)) (ap g2 (ap l p2)).
Proof.
  refine (sq_concat_v (sq_concat_v _ _) _).
  1: { refine (sq_ccGc _ _). 1: refine (ap_compose _ _ _). apply (ap_nat' p p1). }
  2: { refine (sq_cccG _ _). 1: refine (ap_compose _ _ _). apply (ap_nat' q p2). }
  refine (sq_ccGG _ _ _). 1-2: refine (ap_compose' _ _ _)^.
  apply sq_ap. exact r.
Defined.

  Definition functor_equiv_path_pullback {x y : Pullback f1 g1}
    (p1 : x.1 = y.1) (p2 : x.2.1 = y.2.1) (r : PathSquare x.2.2 y.2.2 (ap f1 p1) (ap g1 p2)) 
    : ap (functor_pullback') (equiv_path_pullback x y (p1; p2; r)) = 
    equiv_path_pullback (functor_pullback' x) (functor_pullback' y) 
     (ap k p1; ap l p2; functor_equiv_path_pullback_square p1 p2 r).
Proof.

Admitted.


End FunctorPullback.

Section Pullback3x3.
Context 
  {A00 : Type} {A02 : Type} {A04 : Type}
  {A20 : Type} {A22 : Type} {A24 : Type}
  {A40 : Type} {A42 : Type} {A44 : Type}
  {f01 : A00 $-> A02} {f03 : A04 $-> A02}
  {f10 : A00 $-> A20} {f12 : A02 $-> A22} {f14 : A04 $-> A24}
  {f21 : A20 $-> A22} {f23 : A24 $-> A22}
  {f30 : A40 $-> A20} {f32 : A42 $-> A22} {f34 : A44 $-> A24}
  {f41 : A40 $-> A42} {f43 : A44 $-> A42}
  (H11 : Square f01 f21 f10 f12) (H13 : Square f03 f23 f14 f12)
  (H31 : Square f41 f21 f30 f32) (H33 : Square f43 f23 f34 f32).

  Local Definition AX0 := Pullback f10 f30.
  Local Definition AX2 := Pullback f12 f32.
  Local Definition AX4 := Pullback f14 f34.

  Local Definition fX1
    := functor_pullback' f10 f30 f12 f32 f21 f01 f41 H11 (transpose H31).

  Local Definition fX3
    := functor_pullback' f14 f34 f12 f32 f23 f03 f43 H13 (transpose H33).

  Local Definition AXO := Pullback fX1 fX3.

  Local Definition A0X := Pullback f01 f03.
  Local Definition A2X := Pullback f21 f23.
  Local Definition A4X := Pullback f41 f43.

  Local Definition f1X
    := functor_pullback' f01 f03 f21 f23 f12 f10 f14 (transpose H11) H13.

  Local Definition f3X
    := functor_pullback' f41 f43 f21 f23 f32 f30 f34 (transpose H31) H33.

  Local Definition AOX := Pullback f1X f3X.

  Definition to : AXO -> AOX.
  Proof.
    intros [[x00 [x40 p20]] [[x04 [x44 p24]] q]].
    revert q.
    equiv_intro 
      (equiv_path_pullback (fX1 (x00; x40; p20)) (fX3 (x04; x44; p24))) q.
    simpl in q. destruct q as [p02 [p42 q]].
    simple refine ((x00; x04; p02); (x40; x44; p42); _); cbn beta.
    apply equiv_path_pullback. simpl.
    refine (p20; p24; _).
    apply sq_tr, sq_move_23, sq_move_24, sq_move_31 ^-1, sq_move_14, q.
  Defined.

  Definition from : AOX -> AXO.
  Proof.
    intros [[x00 [x04 p02]] [[x40 [x44 p42]] q]].
    revert q.
    equiv_intro 
      (equiv_path_pullback (f1X (x00; x04; p02)) (f3X (x40; x44; p42))) q.
    simpl in q. destruct q as [p20 [p24 q]].
    simple refine ((x00; x40; p20); (x04; x44; p24); _); cbn beta.
    apply equiv_path_pullback. simpl.
    refine (p02; p42; _).
    apply sq_move_14, sq_move_31, sq_move_24 ^-1, sq_move_23 ^-1, sq_tr, q.
  Defined.

Local Open Scope path_scope.
  Theorem pullback3x3 : AXO <~> AOX.
  Proof.
    apply (equiv_adjointify to from).
    { intros [[x00 [x04 p02]] [[x40 [x44 p42]] q]].
      revert q.
      equiv_intro 
        (equiv_path_pullback (f1X (x00; x04; p02)) (f3X (x40; x44; p42))) q.
      simpl in q. destruct q as [p20 [p24 q]].
      unfold from; rewrite equiv_ind_comp.
      unfold to; rewrite equiv_ind_comp.
      apply equiv_path_pullback. unfold pr1, pr2. srefine (_; _; _).
      + apply equiv_path_pullback. srefine (1; 1; sq_refl_h _). 
      + apply equiv_path_pullback. srefine (1; 1; sq_refl_h _).
      + unfold pr1, pr2. 
        rewrite eisretr, eissect, eisretr, eisretr, sq_tr_sq_tr, !functor_equiv_path_pullback.

       }
    (** Pullbacks commute with sigmas. *)
    (** Pullbacks commute with paths. *)
  Admitted.

End Pullback3x3.