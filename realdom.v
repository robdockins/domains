Require Import QArith.
Require Import Setoid.

Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import directed.
Require Import plotkin.
Require Import joinable.
Require Import approx_rels.
Require Import profinite.
Require Import cusl.


Record rational_interval
  := RatInt
  { rint_start : Q
  ; rint_end   : Q
  ; rint_proper : rint_start <= rint_end
  }.

Definition in_interval (q:Q) (ri:rational_interval) :=
  rint_start ri <= q <= rint_end ri.

Definition in_interior (q:Q) (ri:rational_interval) :=
  rint_start ri < q /\ q < rint_end ri.


Definition rint_ord (i1 i2:rational_interval) :=
  forall q, in_interval q i2 -> in_interval q i1.


Lemma rint_ord_test (i1 i2:rational_interval) :
  rint_ord i1 i2 <->
  (rint_start i1 <= rint_start i2 /\
   rint_end i2 <= rint_end i1).
Proof.
  split; intros.
  split.
  destruct (H (rint_start i2)).
  hnf.
  split; auto.
  apply Qle_refl.
  apply rint_proper.
  auto.
  destruct (H (rint_end i2)).
  hnf.
  split; auto.
  apply rint_proper.
  apply Qle_refl.
  auto.
  hnf; intros.
  destruct H.
  destruct H0.
  split.
  apply Qle_trans with (rint_start i2); auto.
  apply Qle_trans with (rint_end i2); auto.
Qed.

Program Definition rint_opp (r:rational_interval) : rational_interval
  := RatInt (Qopp (rint_end r)) (Qopp (rint_start r)) _.
Next Obligation.
  intros. apply Qopp_le_compat. apply rint_proper.
Qed.

Program Definition rint_plus (r1 r2:rational_interval) : rational_interval
  := RatInt (rint_start r1 + rint_start r2) (rint_end r1 + rint_end r2) _.
Next Obligation.
  intros; apply Qplus_le_compat; apply rint_proper.
Qed.

Lemma rint_opp_correct r q :
  in_interval (Qopp q) (rint_opp r) <-> in_interval q r.
Proof.
  split; intros [??]; split.
  simpl in H0.
  rewrite <- (Qopp_involutive (rint_start r)).
  rewrite <- (Qopp_involutive q).
  apply Qopp_le_compat. auto.
  rewrite <- (Qopp_involutive (rint_end r)).
  rewrite <- (Qopp_involutive q).
  apply Qopp_le_compat. auto.
  simpl.
  apply Qopp_le_compat. auto.
  apply Qopp_le_compat. auto.
Qed.

Lemma rint_plus_correct r1 r2 q:
  in_interval q (rint_plus r1 r2) <-> 
  exists q1 q2,
    in_interval q1 r1 /\ in_interval q2 r2 /\ q == q1 + q2.
Proof.
  split; intros.
  destruct H. simpl in *.
  destruct (Qlt_le_dec q (rint_end r1 + rint_start r2)).
  exists (q - rint_start r2), (rint_start r2).
  split; split.
  rewrite <- (Qplus_le_l _ _ (rint_start r2)). ring_simplify. auto.
  rewrite <- (Qplus_le_r _ _ (rint_start r2)). 
  ring_simplify. rewrite Qplus_comm. apply Qlt_le_weak. auto.
  split. apply Qle_refl. apply rint_proper.
  ring_simplify. apply Qeq_refl.
  
  exists (rint_end r1). exists (q - rint_end r1).
  repeat split.
  apply rint_proper. apply Qle_refl.
  rewrite <- (Qplus_le_r _ _ (rint_end r1)). ring_simplify. auto.
  rewrite <- (Qplus_le_l _ _ (rint_end r1)). ring_simplify. auto.
  ring.

  destruct H as [q1 [q2 [?[??]]]].
  red. rewrite H1. simpl.
  destruct H. destruct H0.
  split; apply Qplus_le_compat; auto.
Qed.




Program Definition rint_preord_mixin :
  Preord.mixin_of rational_interval :=
  Preord.Mixin rational_interval rint_ord _ _.
Next Obligation.
  repeat intro; auto.
Qed.
Next Obligation.
  repeat intro; eauto.
Qed.

Canonical Structure rint_preord :=
  Preord.Pack rational_interval rint_preord_mixin.

Definition rint_dec : forall x y:rational_interval,
  { x ≤ y }+{x ≰ y }.
Proof.
  intros.
  destruct (Qlt_le_dec (rint_start y) (rint_start x)).
  right; intro.
  apply rint_ord_test in H.
  destruct H.
  assert (rint_start y < rint_start y).
  eapply Qlt_le_trans. apply q. auto.
  red in H1. omega.
  destruct (Qlt_le_dec (rint_end x) (rint_end y)).
  right; intro.  
  apply rint_ord_test in H.
  destruct H.
  assert (rint_end x < rint_end x).
  eapply Qlt_le_trans. apply q0. auto.
  red in H1. omega.
  left. apply rint_ord_test.
  split; auto.
Qed.


Definition Z_enum (n:N) :=
  match n with
  | N0 => Some Z0
  | Npos xH => None
  | Npos (xO p) => Some (Zpos p)
  | Npos (xI p) => Some (Zneg p)
  end.

Definition pos_enum (n:N) :=
  match n with
  | N0 => None
  | Npos p => Some p
   end.

Definition Q_enum (n:N) :=
  let (p,q) := pairing.unpairing n in
    match Z_enum p, pos_enum q with
    | Some n1, Some n2 => Some (n1#n2)%Q
    | _, _ => None
    end.
     
Definition rint_enum (n:N) :=
  let (p,q) := pairing.unpairing n in
    match Q_enum p, Q_enum q with
    | Some n1, Some n2 =>
      match Qlt_le_dec n2 n1 with
      | left _  => None
      | right H => Some (RatInt n1 n2 H)
      end
    | _, _ => None
    end.


Lemma Z_enum_complete : 
  forall z:Z, exists n:N,
    Z_enum n = Some z.
Proof.  
  intros. destruct z.
  exists N0. simpl; auto.
  exists (Npos (xO p)). simpl. auto.
  exists (Npos (xI p)). simpl. auto.
Qed.

Lemma pos_enum_complete : 
  forall p:positive, exists n:N,
    pos_enum n = Some p.
Proof.  
  intros.
  exists (Npos p). simpl. auto.
Qed.

Lemma Q_enum_complete :
  forall q:Q, exists n:N,
    Q_enum n = Some q.
Proof.
  intros.  
  destruct q.
  destruct (Z_enum_complete Qnum) as [p ?].
  destruct (pos_enum_complete Qden) as [q ?].
  exists (pairing.pairing (p,q)).
  unfold Q_enum.
  rewrite pairing.unpairing_pairing.
  rewrite H. rewrite H0. auto.
Qed.

Lemma rint_enum_complete :
  forall i:rint_preord, exists n:N,
    exists i', rint_enum n = Some i' /\ i ≈ i'.
Proof.
  intros. 
  destruct (Q_enum_complete (rint_start i)).
  destruct (Q_enum_complete (rint_end i)).
  exists (pairing.pairing (x,x0)).
  unfold rint_enum.
  case_eq (Qlt_le_dec (rint_end i) (rint_start i)).
  intros.
  elimtype False.
  generalize (rint_proper i). intros.
  assert (rint_end i < rint_end i).
  eapply Qlt_le_trans. apply q. auto.
  red in H3. simpl in H3. omega.
  intros.
  exists (RatInt (rint_start i) (rint_end i) q).
  rewrite pairing.unpairing_pairing.
  rewrite H. rewrite H0.
  rewrite H1. split; auto.
  destruct i as [m n R]. simpl in *.
  red. simpl. split; hnf; simpl;
    unfold in_interval; simpl; intros; auto.
Qed.


Program Definition rint_eff : effective_order rint_preord :=
  EffectiveOrder rint_preord rint_dec rint_enum _.
Next Obligation.
  intros. hnf; simpl; intros.
  destruct (rint_enum_complete x) as [n [i' [??]]].
  exists n. rewrite H. auto.
Qed.

Lemma rint_cusl : cusl rint_preord.
Proof.
  constructor.
  intros.
  
  destruct (Qlt_le_dec (rint_start x) (rint_start y)) as [H|H].
  destruct (Qlt_le_dec (rint_end x) (rint_end y)) as [H0|H0].
  destruct (Qlt_le_dec (rint_end x) (rint_start y)) as [H1|H1].

  right.
  intros.
  apply rint_ord_test in H2.
  apply rint_ord_test in H3.
  intuition.
  generalize (rint_proper z). intros.
  assert (rint_end x < rint_end x).
  apply Qlt_le_trans with (rint_start y); auto.
  apply Qle_trans with (rint_start z); auto.
  apply Qle_trans with (rint_end z); auto.
  red in H7. omega.
  left.
  exists (RatInt _ _ H1).
  split; simpl; intros.
  apply rint_ord_test. simpl.
  split; auto.
  apply Qlt_le_weak; auto.
  apply Qle_refl.
  split; auto.
  apply rint_ord_test. simpl.
  split.
  apply Qle_refl.
  apply Qlt_le_weak; auto.

  intros.
  apply rint_ord_test. simpl.
  apply rint_ord_test in H2; destruct H2.
  apply rint_ord_test in H3; destruct H3.
  split; auto.
  
  left.
  exists y.
  split.
  apply rint_ord_test.
  split; auto.
  apply Qlt_le_weak. auto.
  split; auto.

  destruct (Qlt_le_dec (rint_end x) (rint_end y)) as [H0|H0].
  left.
  exists x.
  split. auto.
  split; auto.
  apply rint_ord_test.
  split; auto.
  apply Qlt_le_weak. auto.

  destruct (Qlt_le_dec (rint_end y) (rint_start x)) as [H1|H1].
  right. intros.
  apply rint_ord_test in H2.
  apply rint_ord_test in H3.
  destruct H2. destruct H3.
  assert (rint_end y < rint_end y).
  apply Qlt_le_trans with (rint_start x); auto.
  apply Qle_trans with (rint_start z); auto.
  apply Qle_trans with (rint_end z); auto.
  apply rint_proper.
  red in H6. omega.
  
  left. exists (RatInt _ _ H1).
  split.
  apply rint_ord_test. simpl.
  split; auto. apply Qle_refl.
  split.
  apply rint_ord_test. simpl.
  split; auto. apply Qle_refl.
  intros.
  apply rint_ord_test. simpl.
  apply rint_ord_test in H2.
  apply rint_ord_test in H3.
  intuition.
Qed.

Lemma rint_plotkin : plotkin_order true rint_preord.
Proof.
  apply cusl_plotkin.
  apply rint_eff.
  apply rint_cusl.
Qed.


Program Definition Qpreord_mixin : Preord.mixin_of Q :=
  Preord.Mixin Q Qeq Qeq_refl Qeq_trans.
Canonical Structure Qpreord := Preord.Pack Q Qpreord_mixin.

Program Definition Qpreord_eff : effective_order Qpreord :=
  EffectiveOrder Qpreord Qeq_dec Q_enum _.
Next Obligation.
  intros.
  destruct (Q_enum_complete x) as [n ?].
  exists n. rewrite H. auto.
Qed.

Lemma Q_has_normals : has_normals Qpreord Qpreord_eff true.
Proof.
  repeat intro. exists X.
  split. red; auto.
  split; auto. intros.
  repeat intro. exists z.
  split.
  repeat intro. apply H in H0.
  apply finsubset_elem in H0. destruct H0; auto.
  intros. rewrite <- H1. auto.
  apply finsubset_elem. 
  intros. rewrite <- H0. auto.
  split; auto.
  destruct Hinh0.
  apply H in H0.
  apply finsubset_elem in H0.
  destruct H0. 
  apply member_eq with x; auto.
  split; auto.
  red. simpl. red in H1. simpl in H1.
  apply Qeq_sym. auto.
  intros. rewrite <- H1; auto.
Qed.

Definition Q_plotkin : plotkin_order true Qpreord
  := norm_plt Qpreord Qpreord_eff true Q_has_normals.

Definition QDom : ∂PLT :=
  PLT.Ob true Q
     (PLT.Class true Q Qpreord_mixin Qpreord_eff Q_plotkin).

Definition RealDom : ∂PLT := 
  PLT.Ob true rational_interval
     (PLT.Class true rational_interval rint_preord_mixin rint_eff rint_plotkin).


Definition in_interval_dec (q:Q) (r:rational_interval) :
  { in_interval q r } + { ~in_interval q r }.
Proof.
  destruct (Qlt_le_dec q (rint_start r)).    
  right; intros [??].
  assert (q < q).
  apply Qlt_le_trans with (rint_start r); auto.
  red in H1. abstract omega.
  destruct (Qlt_le_dec (rint_end r) q).
  right; intros [??].
  assert (rint_end r < rint_end r).
  apply Qlt_le_trans with q; auto.
  red in H1. abstract omega.
  left. split; auto.
Defined.

Definition in_interior_dec (q:Q) (r:rational_interval) :
  { in_interior q r } + { ~in_interior q r }.
Proof.
  destruct (Qlt_le_dec (rint_start r) q).
  destruct (Qlt_le_dec q (rint_end r)).
  left; split; auto.
  right; intros [??].
  assert (q < q).
  apply Qlt_le_trans with (rint_end r); auto.
  red in H1. abstract omega.
  right; intros [??].
  assert (rint_start r < rint_start r).
  apply Qlt_le_trans with q; auto.
  red in H1. abstract omega.
Defined.


Definition way_inside (x y:rational_interval) :=
  rint_start y < rint_start x /\
  rint_end x < rint_end y.

Lemma way_inside_dec x y : { way_inside x y } + { ~way_inside x y }.
Proof.
  destruct (Qlt_le_dec (rint_start y) (rint_start x)).
  destruct (Qlt_le_dec (rint_end x) (rint_end y)).
  left. split; auto.
  right; intros [??].
  assert (rint_end x < rint_end x).
  eapply Qlt_le_trans; eauto.
  red in H1; omega.
  right; intros [??].
  assert (rint_start y < rint_start y).
  eapply Qlt_le_trans; eauto.
  red in H1; omega.
Qed.

Definition canon_rel : erel RealDom RealDom :=
  esubset_dec (prod_preord RealDom RealDom)
     (fun x => way_inside (fst x) (snd x))
     (fun x => way_inside_dec (fst x) (snd x))
     (eprod rint_enum rint_enum).

Lemma canon_rel_elem x y :
   (x,y) ∈ canon_rel <-> way_inside x y.
Proof.
  unfold canon_rel. rewrite esubset_dec_elem.
  simpl. intuition.
  apply eprod_elem; split.
  destruct (rint_enum_complete x) as [n [r' [??]]]; auto.
  exists n. rewrite H0. auto.
  destruct (rint_enum_complete y) as [n [r' [??]]]; auto.
  exists n. rewrite H0. auto.
  simpl; intros.
  destruct H. destruct H0.
  destruct H. destruct H1.
  apply rint_ord_test in H.
  apply rint_ord_test in H1.
  apply rint_ord_test in H3.
  apply rint_ord_test in H4.
  split.
  intuition.
  eapply Qle_lt_trans; eauto.
  eapply Qlt_le_trans; eauto.
  intuition.
  eapply Qle_lt_trans; eauto.
  eapply Qlt_le_trans; eauto.
Qed.

Require Import Qminmax.

Program Definition canon : RealDom → RealDom :=
  PLT.Hom true RealDom RealDom canon_rel _ _.
Next Obligation.
  intros.
  apply canon_rel_elem in H1. apply canon_rel_elem.
  apply rint_ord_test in H.
  apply rint_ord_test in H0. red in H1. red.
  intuition.
  eapply Qle_lt_trans; eauto.
  eapply Qlt_le_trans; eauto.
  eapply Qle_lt_trans; eauto.
  eapply Qlt_le_trans; eauto.
Qed.
Next Obligation.
  intro q. apply prove_directed; auto.
  intros r1 r2 ? ?.
  rewrite erel_image_elem in H.
  rewrite erel_image_elem in H0.
  apply canon_rel_elem in H.
  apply canon_rel_elem in H0.
  destruct H. destruct H0.
  assert (Qmax (rint_start r1) (rint_start r2) <= Qmin (rint_end r1) (rint_end r2)).
  apply Q.max_case; intros.
  rewrite <- H3; auto.
  apply Q.min_case; intros.
  rewrite <- H3; auto.
  apply rint_proper.
  apply Qlt_le_weak.
  apply Qlt_trans with (rint_start q); auto.
  apply Qle_lt_trans with (rint_end q); auto.
  apply rint_proper.
  apply Q.min_case; intros.
  rewrite <- H3; auto.
  apply Qlt_le_weak.
  apply Qlt_trans with (rint_start q); auto.
  apply Qle_lt_trans with (rint_end q); auto.
  apply rint_proper.
  apply rint_proper.
  exists (RatInt _ _ H3).
  split; simpl.
  apply rint_ord_test; split; simpl.
  apply Q.le_max_l.
  apply Q.le_min_l.
  split; simpl.
  apply rint_ord_test; split; simpl.
  apply Q.le_max_r.
  apply Q.le_min_r.
  apply erel_image_elem.
  apply canon_rel_elem.
  split; simpl.
  apply Q.max_case; intros; auto.
  rewrite <- H4; auto.
  apply Q.min_case; intros; auto.
  rewrite <- H4; auto.
Qed.

Lemma Q_dense (q1 q2:Q) :
  q1 < q2 -> exists q', q1 < q' /\ q' < q2.
Proof.
  intros.
  exists ((q1+q2) / (2#1)).
  split.
  rewrite <- (Qmult_lt_r _ _ (2#1)). 2: reflexivity.
  field_simplify.
  apply Qle_lt_trans with (q1 + q1)%Q.
  field_simplify. apply Qle_refl.
  apply Qlt_le_trans with (q1 + q2)%Q.
  apply Qplus_lt_r; auto.
  field_simplify.
  field_simplify.
  apply Qle_refl.
  rewrite <- (Qmult_lt_r _ _ (2#1)). 2: reflexivity.
  field_simplify.
  apply Qlt_le_trans with (q2 + q2)%Q.
  apply Qle_lt_trans with (q1 + q2)%Q.
  field_simplify.
  field_simplify.
  apply Qle_refl.
  apply Qplus_lt_l; auto.
  field_simplify.
  apply Qle_refl.
Qed.

Lemma canon_idem : canon ∘ canon ≈ canon.
Proof.
  split; hnf; simpl; intros.
  destruct a as [a b].
  apply PLT.compose_hom_rel in H.
  destruct H as [q [??]].
  simpl in *.
  rewrite canon_rel_elem in H.
  rewrite canon_rel_elem in H0.
  rewrite canon_rel_elem.
  red in H, H0. red. intuition.
  eapply Qlt_trans; eauto.
  eapply Qlt_trans; eauto.
  destruct a as [a b]. simpl. apply PLT.compose_hom_rel.
  apply canon_rel_elem in H.
  destruct H.
  destruct (Q_dense (rint_start b) (rint_start a)) as [m [??]]; auto.
  destruct (Q_dense (rint_end a) (rint_end b)) as [n [??]]; auto.
  assert (m <= n).
  apply Qlt_le_weak.
  eapply Qlt_trans; eauto.
  eapply Qle_lt_trans; eauto.
  apply rint_proper.
  exists (RatInt m n H5).
  split; simpl; rewrite canon_rel_elem.
  split; simpl; auto.
  split; simpl; auto.
Qed.


Definition injq_rel (q:Q) : erel unitpo RealDom :=
  esubset_dec (prod_preord unitpo RealDom)
     (fun x => in_interior q (snd x))
     (fun x => in_interior_dec q (snd x))
     (eprod (single tt) rint_enum).

Lemma injq_rel_elem (q:Q) (u:unit) (r:rational_interval) :
  (u, r) ∈ injq_rel q <-> in_interior q r.
Proof.
  destruct u.
  unfold injq_rel. rewrite esubset_dec_elem.
  simpl. intuition.
  apply eprod_elem.
  split.
  apply single_axiom; auto.
  destruct (rint_enum_complete r) as [n [r' [??]]]; auto.
  exists n. rewrite H0. auto.
  intros. destruct H. 
  destruct H. destruct H1.
  destruct x. destruct y. simpl in *.
  apply rint_ord_test in H3. destruct H3.
  destruct H0. split.
  eapply Qle_lt_trans; eauto.
  eapply Qlt_le_trans; eauto.
Qed.



Program Definition injq (q:Q) : 1 → RealDom :=
  PLT.Hom true 1 RealDom (injq_rel q) _ _.
Next Obligation.
  intros. apply injq_rel_elem in H1. apply injq_rel_elem.
  apply rint_ord_test in H0. destruct H0.
  destruct H1. split.
  eapply Qle_lt_trans; eauto.
  eapply Qlt_le_trans; eauto.
Qed.
Next Obligation.
  intros. intro.
  apply prove_directed; simpl; auto.
  intros r1 r2 ? ?.
  apply erel_image_elem in H.
  apply erel_image_elem in H0.
  apply injq_rel_elem in H.
  apply injq_rel_elem in H0.
  destruct H. destruct H0.
  assert (Qmax (rint_start r1) (rint_start r2) <= Qmin (rint_end r1) (rint_end r2)).
  apply Q.max_case; intros.
  rewrite <- H3; auto.
  apply Q.min_case; intros.
  rewrite <- H3; auto.
  apply rint_proper.
  apply Qlt_le_weak.
  apply Qlt_trans with q; auto.
  apply Q.min_case; intros.
  rewrite <- H3; auto.
  apply Qlt_le_weak.
  apply Qlt_trans with q; auto.
  apply rint_proper.
  exists (RatInt _ _ H3).
  split; simpl.
  apply rint_ord_test; split; simpl.
  apply Q.le_max_l.
  apply Q.le_min_l.
  split; simpl.
  apply rint_ord_test; split; simpl.
  apply Q.le_max_r.
  apply Q.le_min_r.
  apply erel_image_elem.
  apply injq_rel_elem.
  split; simpl.
  apply Q.max_case; intros; auto.
  rewrite <- H4; auto.
  apply Q.min_case; intros; auto.
  rewrite <- H4; auto.
Qed.


Lemma rint_enum_complete' x: x ∈ (rint_enum : eset rint_preord).
Proof.
  destruct (rint_enum_complete x) as [n [x' [??]]].  
  exists n. rewrite H. auto.
Qed.


Definition real_opp_rel : erel rint_preord rint_preord :=
  esubset_dec (prod_preord rint_preord rint_preord)
     (fun xy => snd xy ≤ rint_opp (fst xy))
     (fun xy => rint_dec _ _)
     (eprod rint_enum rint_enum).

Lemma real_opp_rel_elem x y :
  (x,y) ∈ real_opp_rel <-> y ≤ rint_opp x.
Proof.
  unfold real_opp_rel. rewrite esubset_dec_elem.
  simpl; intuition.
  apply eprod_elem; split; apply rint_enum_complete'.
  simpl; intros.
  destruct x0; destruct y0.
  destruct H as [[??][??]]. simpl in *.
  rewrite H3. rewrite H0.
  apply rint_ord_test.
  apply rint_ord_test in H. destruct H.
  simpl. split; apply Qopp_le_compat; auto.
Qed.

Program Definition real_opp : RealDom → RealDom :=
  PLT.Hom true RealDom RealDom real_opp_rel _ _.
Next Obligation.
  simpl; intros.
  apply real_opp_rel_elem in H1. apply real_opp_rel_elem.
  rewrite H0. rewrite H1.
  apply rint_ord_test. simpl.
  apply rint_ord_test in H. destruct H.
  split; apply Qopp_le_compat; auto.
Qed.
Next Obligation.
  repeat intro.
  exists (rint_opp x).
  split.
  red; intros.
  apply H in H0. apply erel_image_elem in H0.
  apply real_opp_rel_elem in H0. auto.
  apply erel_image_elem.
  apply real_opp_rel_elem. auto.
Qed.


Definition real_plus_rel : erel (prod_preord rint_preord rint_preord) rint_preord :=
  esubset_dec (prod_preord (prod_preord rint_preord rint_preord) rint_preord)
     (fun xyz => (snd xyz) ≤ rint_plus (fst (fst xyz)) (snd (fst xyz)))
     (fun xyz => rint_dec _ _)
     (eprod (eprod rint_enum rint_enum) rint_enum).

Lemma real_plus_rel_elem x y z :
  (x,y,z) ∈ real_plus_rel <-> z ≤ rint_plus x y.
Proof.
  unfold real_plus_rel. rewrite esubset_dec_elem. simpl.
  intuition. apply eprod_elem. split.
  apply eprod_elem; split; apply rint_enum_complete'. apply rint_enum_complete'.
  simpl. intros.
  destruct x0 as [[??]?]. simpl in *.
  destruct y0 as [[??]?]. simpl in *.
  destruct H as [[[??]?][[??]?]] . simpl in *.
  rewrite H5. rewrite H0.
  unfold rint_plus.
  apply rint_ord_test. simpl.
  apply rint_ord_test in H; destruct H.
  split; apply Qplus_le_compat; auto.
  apply rint_ord_test in H1; destruct H1. auto.
  apply rint_ord_test in H1; destruct H1. auto.
Qed.

Program Definition real_plus : (RealDom ⊗ RealDom) → RealDom :=
  PLT.Hom true (RealDom ⊗ RealDom) RealDom real_plus_rel _ _.
Next Obligation.
  intros. 
  destruct x. destruct x'.
  rewrite real_plus_rel_elem in H1. rewrite real_plus_rel_elem.
  transitivity y; auto.
  rewrite H1.
  destruct H. simpl in *.
  apply rint_ord_test. simpl.
  apply rint_ord_test in H.
  apply rint_ord_test in H2.
  split; apply Qplus_le_compat; intuition.
Qed.
Next Obligation.
  intro. destruct x as [x y]. apply prove_directed; simpl; auto.
  intros. apply erel_image_elem in H. apply erel_image_elem in H0.
  apply real_plus_rel_elem in H.
  apply real_plus_rel_elem in H0.
  exists (rint_plus x y). split; auto. split; auto.
  apply erel_image_elem.
  apply real_plus_rel_elem. auto.
Qed.


Lemma real_plus_comm_le A (g h:A → RealDom) :
  real_plus ∘ 《 g, h 》 ≤ real_plus ∘ 《 h, g 》.
Proof.
  red; intros [x y] H.
  apply PLT.compose_hom_rel in H. apply PLT.compose_hom_rel.
  destruct H as [[a b] [??]].
  rewrite (PLT.pair_hom_rel _ _ _ _ g h) in H. destruct H.
  exists (b,a). split.
  apply PLT.pair_hom_rel. split; auto.
  simpl in *. apply real_plus_rel_elem in H0. apply real_plus_rel_elem.
  rewrite H0.
  apply rint_ord_test. simpl; split.
  rewrite Qplus_comm; apply Qle_refl.
  rewrite Qplus_comm; apply Qle_refl.
Qed.

Lemma real_plus_comm A (g h:A → RealDom) :
  real_plus ∘ 《 g, h 》 ≈ real_plus ∘ 《 h, g 》.
Proof.
  split; apply real_plus_comm_le; auto.
Qed.

Lemma real_plus_assoc A (f g h:A → RealDom) :
  real_plus ∘ 《 f, real_plus ∘ 《 g, h 》 》 ≈
  real_plus ∘ 《 real_plus ∘ 《 f, g 》, h 》.
Proof.
  split; intros [x y] H.  
  apply PLT.compose_hom_rel in H. apply PLT.compose_hom_rel.
  destruct H as [[a b] [??]].
  rewrite (PLT.pair_hom_rel _ _ _ _ f (real_plus ∘ 《g,h》)) in H. destruct H.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [[c d] [??]].
  rewrite (PLT.pair_hom_rel _ _ _ _ g h) in H1. destruct H1.
  exists (rint_plus a c,d).
  split.
  apply PLT.pair_hom_rel.
  split; auto.
  apply PLT.compose_hom_rel.
  exists (a,c). split.
  apply PLT.pair_hom_rel. split; auto.
  simpl. apply real_plus_rel_elem. auto.
  simpl. apply real_plus_rel_elem. 
  apply real_plus_rel_elem in H0. rewrite H0.
  apply real_plus_rel_elem in H2. 
  apply rint_ord_test in H2.
  simpl in H2. destruct H2.
  apply rint_ord_test.
  split; simpl.
  rewrite <- Qplus_assoc.
  apply Qplus_le_compat. apply Qle_refl. auto.
  rewrite <- Qplus_assoc.
  apply Qplus_le_compat. apply Qle_refl. auto.
  
  apply PLT.compose_hom_rel in H.  
  destruct H as [[a b][??]].
  apply (PLT.pair_hom_rel _ _ _ _ (real_plus ∘ 《f, g》) h) in H.
  destruct H.
  apply PLT.compose_hom_rel in H.  
  destruct H as [[c d][??]].
  apply PLT.compose_hom_rel.
  apply (PLT.pair_hom_rel _ _ _ _ f g) in H. destruct H.
  exists (c, rint_plus d b).
  split.
  apply PLT.pair_hom_rel. split; auto.
  apply PLT.compose_hom_rel.
  exists (d,b). split.
  apply PLT.pair_hom_rel. split; auto.
  simpl. apply real_plus_rel_elem. auto.
  apply real_plus_rel_elem.
  apply real_plus_rel_elem in H0.
  apply real_plus_rel_elem in H2.
  apply rint_ord_test in H2.
  rewrite H0.
  apply rint_ord_test. unfold rint_plus; simpl.
  do 2 rewrite Qplus_assoc.
  split. apply Qplus_le_compat.
  simpl in H2; destruct H2; auto.
  apply Qle_refl.
  apply Qplus_le_compat.
  simpl in H2; destruct H2; auto.
  apply Qle_refl.
Qed.

Lemma real_plus_0 A (h: A → RealDom) :
  real_plus ∘ 《 h, injq 0 ∘ PLT.terminate true A 》 ≈ h.
Proof.
  split; hnf; simpl; intros.
  destruct a as [a r].
  apply PLT.compose_hom_rel in H.
  destruct H as [[m n] [??]]. simpl in *.
  apply real_plus_rel_elem in H0.
  rewrite (PLT.pair_hom_rel _ _ _ _ h (injq 0 ∘ PLT.terminate true A) a m n) in H.
  destruct H.
  apply PLT.hom_order with a m; auto.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [u [??]]. destruct u.
  simpl in H2. apply injq_rel_elem in H2.
  hnf; simpl; intros. apply H0.
  apply rint_plus_correct.
  exists q. exists 0%Q. split; auto. split; auto.
  destruct H2; split.
  apply Qlt_le_weak; auto.
  apply Qlt_le_weak; auto.
  ring.

  destruct a as [a r]; simpl.
  apply PLT.compose_hom_rel.
  exists (r, (RatInt 0 0 (Qle_refl 0))%Q).
  split; simpl.
  rewrite (PLT.pair_hom_rel _ _ _ _ h (injq 0 ∘ PLT.terminate true A)).
  split; auto.
  apply PLT.compose_hom_rel.
  exists tt. split; simpl.
  apply eprod_elem. split.
  apply eff_complete. apply single_axiom; auto.
  apply injq_rel_elem. hnf; simpl. split; apply Qle_refl.
  apply real_plus_rel_elem.
  apply rint_ord_test; simpl.
  split; ring_simplify; apply Qle_refl.
Qed.

Lemma real_opp_0 A (h : A → RealDom) :
  real_plus ∘ 《 h, real_opp ∘ h 》 ≤ injq 0 ∘ PLT.terminate true A.
Proof.
  intros [??] ?.
  apply PLT.compose_hom_rel in H.
  apply PLT.compose_hom_rel.
  exists tt. split; simpl.
  apply eprod_elem. split.
  apply eff_complete. apply single_axiom. auto.
  destruct H as [[a b][??]].
  apply (PLT.pair_hom_rel _ _ _ _ h (real_opp ∘ h)) in H. destruct H.
  simpl in H0. apply real_plus_rel_elem in H0.
  apply injq_rel_elem.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [q [??]].
  simpl in H2.
  apply real_opp_rel_elem in H2.
  apply H0. hnf; simpl.
  apply rint_ord_test in H2. simpl in H2.
  destruct H2.
  destruct (PLT.hom_directed true _ _ h c (a::q::nil)%list) as [z [??]].
  exists a. apply cons_elem; auto.
  red; intros. apply erel_image_elem.
  apply cons_elem in H4. destruct H4.
  apply PLT.hom_order with c a; auto.
  apply cons_elem in H4. destruct H4.
  apply PLT.hom_order with c q; auto.
  apply nil_elem in H4. elim H4.
  apply erel_image_elem in H5.
  assert (a ≤ z).
    apply H4. apply cons_elem; auto.
  assert (q ≤ z).
    apply H4. apply cons_elem. right. apply cons_elem; auto.
  apply rint_ord_test in H6.
  apply rint_ord_test in H7.
  destruct H6. destruct H7.
  split. apply Qle_trans with (rint_start z + -rint_end q)%Q.
  apply Qplus_le_compat; auto.
  rewrite <- (Qplus_le_l _ _ (rint_end q)).
  ring_simplify.
  apply Qle_trans with (rint_end z); auto. apply rint_proper.
  apply Qle_trans with (rint_end z + -rint_start q)%Q.
  rewrite <- (Qplus_le_l _ _ (rint_start q)).
  ring_simplify.
  apply Qle_trans with (rint_start z); auto. apply rint_proper.
  apply Qplus_le_compat; auto.
Qed.

Lemma Q_real_opp_compat q :
  real_opp ∘ injq q ≈ injq (Qopp q).
Proof.
  split; intros.
  intros [??] ?. apply PLT.compose_hom_rel in H.
  destruct H as [r [??]].
  simpl in *.
  apply injq_rel_elem in H.
  apply real_opp_rel_elem in H0.
  apply injq_rel_elem.
  apply H0.
  apply rint_opp_correct. auto.
  
  intros [??] ?. apply PLT.compose_hom_rel.
  exists (rint_opp c0).
  split. simpl. apply injq_rel_elem.
  red. rewrite <- (Qopp_involutive q).
  simpl in H. apply injq_rel_elem in H.
  destruct H. split; simpl.
  apply Qopp_le_compat; auto.
  apply Qopp_le_compat; auto.
  simpl. apply real_opp_rel_elem.
  apply rint_ord_test. simpl.
  rewrite Qopp_involutive.
  rewrite Qopp_involutive.
  split; apply Qle_refl.
Qed.

Lemma Q_real_plus_compat q q1 q2 :
  real_plus ∘ 《 injq q1, injq q2 》 ≈ injq q <-> q1 + q2 == q.
Proof.
  split; intros.
  destruct H.
  assert ((tt, RatInt q q (Qle_refl q)) ∈ PLT.hom_rel (real_plus ∘ 《 injq q1, injq q2 》)).
  apply H0.
  simpl. apply injq_rel_elem.
  split; simpl; apply Qle_refl.
  rewrite (PLT.compose_hom_rel _ _ _ _ 《injq q1, injq q2》 real_plus) in H1.
  destruct H1 as [[a b][??]].
  simpl in H2. apply real_plus_rel_elem in H2.
  apply rint_ord_test in H2. simpl in H2.
  destruct H2.
  apply (PLT.pair_hom_rel _ _ _ _ (injq q1) (injq q2)) in H1.
  destruct H1. simpl in H1. simpl in H4.
  apply injq_rel_elem in H1.
  apply injq_rel_elem in H4.
  hnf in H1. hnf in H4.
  assert (rint_end a + rint_end b <= rint_start a + rint_end b).
  apply Qle_trans with q; auto.
  apply Qle_trans with (rint_start a + rint_start b)%Q; auto.
  apply Qplus_le_compat.
  apply Qle_refl. apply rint_proper.
  rewrite (Qplus_le_l _ _ (rint_end b)) in H5.
  assert (rint_start a == rint_end a).
  apply Qle_antisym; auto.
  apply rint_proper.
  rewrite H6 in H1.
  assert (q1 == rint_end a).
  apply Qle_antisym; destruct H1; auto.
  rewrite H6 in H2.
  assert (rint_start b == rint_end b).
  apply Qle_antisym. apply rint_proper.
  rewrite <- (Qplus_le_r _ _ (rint_end a)).
  apply Qle_trans with q; auto.
  assert (q2 == rint_end b).
  apply Qle_antisym; destruct H4; auto.
  rewrite <- H8; auto.
  rewrite H7. rewrite H9.
  apply Qle_antisym; auto.
  rewrite H8 in H2; auto.
  
  split; intros [u a] H0.
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [[b c][??]].
  apply (PLT.pair_hom_rel _ _ _ _ (injq q1) (injq q2)) in H0.
  destruct H0.
  simpl in H0. apply injq_rel_elem in H0.
  simpl in H2. apply injq_rel_elem in H2.
  simpl in H1. apply real_plus_rel_elem in H1.
  simpl. apply injq_rel_elem.
  apply H1.
  hnf. rewrite <- H. simpl.
  destruct H0; destruct H2.
  split; apply Qplus_le_compat; auto.
  simpl in H0.
  apply injq_rel_elem in H0.
  apply PLT.compose_hom_rel.
  exists (RatInt q1 q1 (Qle_refl q1), RatInt q2 q2 (Qle_refl q2)).
  split.
  apply PLT.pair_hom_rel. split; simpl.
  apply injq_rel_elem. split; simpl; apply Qle_refl.
  apply injq_rel_elem. split; simpl; apply Qle_refl.
  simpl. apply real_plus_rel_elem.
  apply rint_ord_test. simpl.
  rewrite H. auto.
Qed.
