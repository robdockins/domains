Require Import QArith.
Require Import Setoid.
Require Import Coq.Program.Basics.
Require Import Lia.

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

Require Import rational_intervals.

Require Import Qminmax.


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
  - right; intro.
    apply rint_ord_test in H.
    destruct H.
    assert (rint_start y < rint_start y).
    { eapply Qlt_le_trans. apply q. auto. }
    red in H1. lia.
  - destruct (Qlt_le_dec (rint_end x) (rint_end y)).
    + right; intro.  
      apply rint_ord_test in H.
      destruct H.
      assert (rint_end x < rint_end x).
      { eapply Qlt_le_trans. apply q0. auto. }
      red in H1. lia.
    + left. apply rint_ord_test.
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
  - intros.
    elimtype False.
    generalize (rint_proper i). intros.
    assert (rint_end i < rint_end i).
    { eapply Qlt_le_trans. apply q. auto. }
    red in H3. simpl in H3. lia.
  - intros.
    exists (RatInt (rint_start i) (rint_end i) q).
    rewrite pairing.unpairing_pairing.
    rewrite H. rewrite H0.
    rewrite H1. split; auto.
    destruct i as [m n R]. simpl in *.
    red. simpl.
    split; hnf; simpl;
      unfold in_interval; simpl; intros; auto.
Qed.


Lemma rint_enum_complete' x: x ∈ (rint_enum : eset rint_preord).
Proof.
  destruct (rint_enum_complete x) as [n [x' [??]]].  
  exists n. rewrite H. auto.
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
  - destruct (Qlt_le_dec (rint_end x) (rint_end y)) as [H0|H0].
    + destruct (Qlt_le_dec (rint_end x) (rint_start y)) as [H1|H1].
      * right.
        intros.
        apply rint_ord_test in H2.
        apply rint_ord_test in H3.
        intuition.
        generalize (rint_proper z). intros.
        assert (rint_end x < rint_end x).
        { apply Qlt_le_trans with (rint_start y); auto.
          apply Qle_trans with (rint_start z); auto.
          apply Qle_trans with (rint_end z); auto.
        } 
        red in H7. lia.
      * left.
        exists (RatInt _ _ H1).
        split; simpl; intros.
        ** apply rint_ord_test. simpl.
           split; auto.
           *** apply Qlt_le_weak; auto.
           *** apply Qle_refl.
        ** split; auto.
           *** apply rint_ord_test. simpl.
               split.
               **** apply Qle_refl.
               **** apply Qlt_le_weak; auto.

           *** intros.
               apply rint_ord_test. simpl.
               apply rint_ord_test in H2; destruct H2.
               apply rint_ord_test in H3; destruct H3.
               split; auto.
  
    + left.
      exists y.
      split.
      * apply rint_ord_test.
        split; auto.
        apply Qlt_le_weak. auto.
      * split; auto.

  - destruct (Qlt_le_dec (rint_end x) (rint_end y)) as [H0|H0].
    + left.
      exists x.
      split; auto.
      split; auto.
      apply rint_ord_test.
      split; auto.
      apply Qlt_le_weak. auto.

    + destruct (Qlt_le_dec (rint_end y) (rint_start x)) as [H1|H1].
      * right. intros.
        apply rint_ord_test in H2.
        apply rint_ord_test in H3.
        destruct H2. destruct H3.
        assert (rint_end y < rint_end y).
        { apply Qlt_le_trans with (rint_start x); auto.
          apply Qle_trans with (rint_start z); auto.
          apply Qle_trans with (rint_end z); auto.
          apply rint_proper.
        } 
        red in H6. lia.
  
      * left. exists (RatInt _ _ H1).
        split.
        ** apply rint_ord_test. simpl.
           split; auto. apply Qle_refl.
        ** split.
           *** apply rint_ord_test. simpl.
               split; auto. apply Qle_refl.
           *** intros.
               apply rint_ord_test. simpl.
               apply rint_ord_test in H2.
               apply rint_ord_test in H3.
               intuition.
Qed.

Lemma rint_plotkin : plotkin_order true rint_preord.
Proof.
  apply cusl_plotkin.
  - apply rint_eff.
  - apply rint_cusl.
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
  split; [ red; auto |].
  split; auto.
  repeat intro. exists z.
  split.
  - repeat intro. apply H in H0.
    apply finsubset_elem in H0.
    + destruct H0; auto.
    + intros. rewrite <- H2. auto.
  - apply finsubset_elem. 
    + intros. rewrite <- H0. auto.
    + split; auto.
      destruct Hinh0.
      apply H in H0.
      apply finsubset_elem in H0.
      * destruct H0. 
        apply member_eq with x; auto.
        split; auto.
        red. simpl. red in H1. simpl in H1.
        apply Qeq_sym. auto.
      * intros. rewrite <- H2; auto.
Qed.

Definition Q_plotkin : plotkin_order true Qpreord
  := norm_plt Qpreord Qpreord_eff true Q_has_normals.

Definition QDom : ∂PLT :=
  PLT.Ob true Q
     (PLT.Class true Q Qpreord_mixin Qpreord_eff Q_plotkin).


Definition PreRealDom : ∂PLT :=
  PLT.Ob true rational_interval
     (PLT.Class true rational_interval rint_preord_mixin rint_eff rint_plotkin).


Definition canonical (A:∂PLT) (f : A → PreRealDom) :=
  forall a x, (a,x) ∈ PLT.hom_rel f  ->
    exists x', (a,x') ∈ PLT.hom_rel f /\ way_inside x' x.


Definition canon_rel : erel PreRealDom PreRealDom :=
  esubset_dec (prod_preord PreRealDom PreRealDom)
     (fun x => way_inside (fst x) (snd x))
     (fun x => way_inside_dec (fst x) (snd x))
     (eprod rint_enum rint_enum).

Lemma canon_rel_elem x y :
   (x,y) ∈ canon_rel <-> way_inside x y.
Proof.
  unfold canon_rel. rewrite esubset_dec_elem.
  - simpl. intuition.
    apply eprod_elem; split.
    + destruct (rint_enum_complete x) as [n [r' [??]]]; auto.
      exists n. rewrite H0. auto.
    + destruct (rint_enum_complete y) as [n [r' [??]]]; auto.
      exists n. rewrite H0. auto.
  - simpl; intros.
    destruct H. destruct H0.
    destruct H. destruct H1.
    apply rint_ord_test in H.
    apply rint_ord_test in H1.
    apply rint_ord_test in H3.
    apply rint_ord_test in H4.
    split.
    + intuition.
      eapply Qle_lt_trans; eauto.
      eapply Qlt_le_trans; eauto.
    + intuition.
      eapply Qle_lt_trans; eauto.
      eapply Qlt_le_trans; eauto.
Qed.


Program Definition canon : PreRealDom → PreRealDom :=
  PLT.Hom true PreRealDom PreRealDom canon_rel _ _.
Next Obligation.
  intros.
  apply canon_rel_elem in H1. apply canon_rel_elem.
  apply rint_ord_test in H.
  apply rint_ord_test in H0. red in H1. red.
  intuition.
  - eapply Qle_lt_trans; eauto.
    eapply Qlt_le_trans; eauto.
  - eapply Qle_lt_trans; eauto.
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
  { apply Q.max_case; intros.
    - rewrite <- H3; auto.
    - apply Q.min_case; intros.
      + rewrite <- H3; auto.
      + apply rint_proper.
      + apply Qlt_le_weak.
        apply Qlt_trans with (rint_start q); auto.
        apply Qle_lt_trans with (rint_end q); auto.
        apply rint_proper.
    - apply Q.min_case; intros.
      + rewrite <- H3; auto.
      + apply Qlt_le_weak.
        apply Qlt_trans with (rint_start q); auto.
        apply Qle_lt_trans with (rint_end q); auto.
        apply rint_proper.
      + apply rint_proper.
  }
  exists (RatInt _ _ H3).
  split; simpl.
  - apply rint_ord_test; split; simpl.
    + apply Q.le_max_l.
    + apply Q.le_min_l.
  - split; simpl.
    + apply rint_ord_test; split; simpl.
      * apply Q.le_max_r.
      * apply Q.le_min_r.
    + apply erel_image_elem.
      apply canon_rel_elem.
      split; simpl.
      * apply Q.max_case; intros; auto.
        rewrite <- H4; auto.
      * apply Q.min_case; intros; auto.
        rewrite <- H4; auto.
Qed.


Lemma canon_idem : canon ∘ canon ≈ canon.
Proof.
  split; hnf; simpl; intros.
  - destruct a as [a b].
    apply PLT.compose_hom_rel in H.
    destruct H as [q [??]].
    simpl in *.
    rewrite canon_rel_elem in H.
    rewrite canon_rel_elem in H0.
    rewrite canon_rel_elem.
    red in H, H0. red. intuition.
    + eapply Qlt_trans; eauto.
    + eapply Qlt_trans; eauto.
  - destruct a as [a b]. simpl. apply PLT.compose_hom_rel.
    apply canon_rel_elem in H.
    destruct H.
    destruct (Q_dense (rint_start b) (rint_start a)) as [m [??]]; auto.
    destruct (Q_dense (rint_end a) (rint_end b)) as [n [??]]; auto.
    assert (m <= n).
    { apply Qlt_le_weak.
      eapply Qlt_trans; eauto.
      eapply Qle_lt_trans; eauto.
      apply rint_proper.
    } 
    exists (RatInt m n H5).
    split; simpl; rewrite canon_rel_elem.
    + split; simpl; auto.
    + split; simpl; auto.
Qed.


Lemma canon_canonical (A:∂PLT) (f:A → PreRealDom) :
  canonical A (canon ∘ f).
Proof.
  red. intros.
  apply PLT.compose_hom_rel in H.
  destruct H as [x' [??]].
  simpl in H0.
  apply canon_rel_elem in H0.
  destruct H0.
  destruct (Q_dense _ _ H0) as [q1 [??]].
  destruct (Q_dense _ _ H1) as [q2 [??]].
  assert (q1 <= q2).
  { apply Qlt_le_weak.
    apply Qlt_trans with (rint_start x'); auto.
    apply Qle_lt_trans with (rint_end x'); auto.
    apply rint_proper.
  } 
  exists (RatInt q1 q2 H6).
  split; simpl.
  - apply PLT.compose_hom_rel.
    exists x'. split; auto.
    simpl. apply canon_rel_elem.
    split; simpl; auto.
  - split; simpl; auto.
Qed.

Lemma canon_canonical_iff (A:∂PLT) (f:A → PreRealDom) :
  canonical A f  <-> f ≈ canon ∘ f.
Proof.
  split; intros.
  - split; hnf; intros.
    + destruct a as [a x].
      hnf in H.
      destruct (H a x H0) as [x' [??]].
      apply PLT.compose_hom_rel.
      exists x'. split; auto.
      simpl. apply canon_rel_elem; auto.
    + destruct a as [a x].
      apply PLT.compose_hom_rel in H0.
      destruct H0 as [x' [??]].
      simpl in H1. apply canon_rel_elem in H1.
      apply PLT.hom_order with a x'; auto.
      apply rint_ord_test.
      destruct H1; split; apply Qlt_le_weak; auto.
  
  - hnf; simpl; intros.
    destruct H.
    apply H in H0.
    apply PLT.compose_hom_rel in H0.
    destruct  H0 as [x' [??]].
    exists x'. split; auto.
    simpl in H2. apply canon_rel_elem in H2; auto.
Qed.

Definition realdom_lt (A:∂PLT) (f g:A → PreRealDom) :=
  forall a, exists x y,
    (a,x) ∈ PLT.hom_rel f /\ 
    (a,y) ∈ PLT.hom_rel g /\
    rint_end x < rint_start y.

Definition realdom_lt' (A:∂PLT) (f g:A → PreRealDom) :=
  forall a (ε:Q), ε >= 0 -> exists x y,
    (a,x) ∈ PLT.hom_rel f /\ 
    (a,y) ∈ PLT.hom_rel g /\
    rint_end x < rint_start y + ε.

Definition realdom_le (A:∂PLT) (f g:A → PreRealDom) :=
  forall a (ε:Q), ε > 0 -> exists x y,
    (a,x) ∈ PLT.hom_rel f /\ 
    (a,y) ∈ PLT.hom_rel g /\
    rint_end x < rint_start y + ε.


Lemma realdom_lt_eq A f g :
  realdom_lt A f g <-> realdom_lt' A f g.
Proof.
  split; red; intros.
  - destruct (H a) as [x [y [?[??]]]].
    exists x. exists y. intuition.
    apply Qlt_le_trans with (rint_start y + 0)%Q; auto.
    + ring_simplify; auto.
    + apply Qplus_le_compat; auto. apply Qle_refl.
  
  - destruct (H a 0%Q) as [x [y [?[??]]]].
    + apply Qle_refl.
    + exists x. exists y. intuition.
      ring_simplify in H2. auto.
Qed.



Add Parametric Morphism (A:∂PLT) :
  (@realdom_lt A)
    with signature (Preord.ord_op _) ==> (Preord.ord_op _) ==> impl
    as realdom_lt_morphism.
Proof.
  repeat intro.
  destruct (H1 a) as [?[?[?[??]]]].
  exists x1. exists x2. intuition.
Qed.

Add Parametric Morphism (A:∂PLT) :
  (@realdom_lt A)
    with signature (eq_op _) ==> (eq_op _) ==> iff
    as realdom_lt_eq_morphism.
Proof.
  split; intros.
  - generalize (realdom_lt_morphism).
    unfold impl. intros. eapply H2; eauto.
  - generalize (realdom_lt_morphism).
    unfold impl. intros. eapply H2; eauto.
Qed.

Add Parametric Morphism (A:∂PLT) :
  (@realdom_le A)
    with signature (Preord.ord_op _) ==> (Preord.ord_op _) ==> impl
    as realdom_le_morphism.
Proof.
  repeat intro.
  destruct (H1 a ε H2) as [?[?[?[??]]]].
  exists x1. exists x2. intuition.
Qed.

Add Parametric Morphism (A:∂PLT) :
  (@realdom_le A)
    with signature (eq_op _) ==> (eq_op _) ==> iff
    as realdom_le_eq_morphism.
Proof.
  split; intros.
  - generalize (realdom_le_morphism).
    unfold impl. intros. eapply H2; eauto.
  - generalize (realdom_le_morphism).
    unfold impl. intros. eapply H2; eauto.
Qed.


Definition realdom_apart (A:∂PLT) (f g:A → PreRealDom) :=
  exists a x y,
    (a,x) ∈ PLT.hom_rel f /\ 
    (a,y) ∈ PLT.hom_rel g /\
    (rint_end x < rint_start y \/ rint_end y < rint_start x).

Definition realdom_converges (A:∂PLT) (f:A → PreRealDom) :=
  forall a ε, ε > 0 ->
    exists x, (a,x) ∈ PLT.hom_rel f /\
      rint_end x - rint_start x <= ε.

Lemma realdom_napart_common (A:∂PLT) (f g:A → PreRealDom) :
  ~realdom_apart A f g -> 
  forall a x y,
    (a,x) ∈ PLT.hom_rel f ->
    (a,y) ∈ PLT.hom_rel g ->
    exists q,
      in_interval q x /\
      in_interval q y.
Proof.
  intros.
  destruct (Qlt_le_dec (rint_end x) (rint_start y)).
  - elim H.
    exists a, x, y; intuition.
  - destruct (Qlt_le_dec (rint_end y) (rint_start x)).
    + elim H.
      exists a, x, y; intuition.

    + exists (Qmax (rint_start x) (rint_start y)).
      split.
      * hnf; split.
        ** apply Q.le_max_l.
        ** apply Q.max_case; auto.
           *** intros. rewrite <- H2; auto.
           *** apply rint_proper.
      * split.
        ** apply Q.le_max_r.
        ** apply Q.max_case; auto.
           *** intros. rewrite <- H2; auto.
           *** apply rint_proper.
Qed.


Lemma realdom_napart_le (A:∂PLT) (f g:A → PreRealDom) :
  canonical A f ->
  realdom_converges A g ->
  ~realdom_apart A f g ->
  f ≤ g.
Proof.
  repeat intro.
  destruct a as [a x].
  destruct (H a x) as [x' [??]]; auto.
  set (ε := Qmin (rint_start x' - rint_start x) (rint_end x - rint_end x')).
  destruct (H0 a ε) as [y [??]].
  - destruct H4.
    unfold ε.
    apply Q.min_case_strong; intros.
    + rewrite <- H6; auto.
    + rewrite <- (Qplus_lt_r _ _ (rint_start x)). ring_simplify. auto.
    + rewrite <- (Qplus_lt_r _ _ (rint_end x')). ring_simplify. auto.

  - destruct (realdom_napart_common A f g H1 a x' y) as [q [??]]; auto.
    destruct H7. destruct H8.
    apply PLT.hom_order with a y; auto.
    apply rint_ord_test.
    destruct H4.
    split.

    + rewrite <- (Qplus_le_l _ _ ε).
      apply Qle_trans with (rint_start x').
      * unfold ε.
        apply Q.min_case_strong.
        ** intros. rewrite <- H12; auto.
        ** intros. ring_simplify. apply Qle_refl.
        ** intros. 
           eapply Qle_trans.
           *** apply Qplus_le_r. apply H12.
           *** ring_simplify. apply Qle_refl.
      * apply Qle_trans with q; auto.
        apply Qle_trans with (rint_end y); auto.
        rewrite <- (Qplus_le_l _ _ (- rint_start y)).
        ring_simplify.
        ring_simplify in H6.
        auto.

    + rewrite <- (Qplus_le_l _ _ (- ε)).
      apply Qle_trans with (rint_end x').
      * apply Qle_trans with q; auto.
        apply Qle_trans with (rint_start y); auto.
        rewrite <- (Qplus_le_l _ _ (- rint_start y)).
        rewrite <- (Qplus_le_l _ _ ε).
        ring_simplify.
        ring_simplify in H6.
        auto.
      * unfold ε.
        apply Q.min_case_strong.
        ** intros. rewrite <- H12; auto.
        ** intros.
           rewrite <- (Qplus_le_l _ _ (rint_start x' - rint_start x)).
           eapply Qle_trans.
           *** apply Qplus_le_r. apply H12.
           *** ring_simplify. apply Qle_refl.
        ** intros.
           ring_simplify. apply Qle_refl.
Qed.


Lemma realdom_napart_eq A (f g:A → PreRealDom) :
  canonical A f ->
  canonical A g ->
  realdom_converges A f ->
  realdom_converges A g ->
  ~realdom_apart A f g -> 
  f ≈ g.
Proof.
  intros; split; apply realdom_napart_le; auto.
  intro. apply H3.
  destruct H4 as [a [x [y [?[??]]]]].
  exists a, y, x; intuition.
Qed.

Lemma realdom_le_napart A (f g:A → PreRealDom) :
  g ≤ f -> ~realdom_apart A f g.
Proof.
  intros. red; intros. 
  destruct H0 as [a [x [y [?[??]]]]].
  assert ((a,y) ∈ PLT.hom_rel f).
  { apply H; auto. }
  destruct (PLT.hom_directed true _ _ f a (x::y::nil)%list) as [q [??]].
  - exists x. apply cons_elem; auto.
  - red; intros. apply erel_image_elem.
    apply cons_elem in H4. destruct H4.
    + apply PLT.hom_order with a x; auto.
    + apply cons_elem in H4. destruct H4.
      * apply PLT.hom_order with a y; auto.
      * apply nil_elem in H4. elim H4.
  - apply erel_image_elem in H5.
    assert (x ≤ q).
    { apply H4. apply cons_elem; auto. }
    assert (y ≤ q).
    { apply H4. apply cons_elem; right. apply cons_elem; auto. }
    apply rint_ord_test in H6.
    apply rint_ord_test in H7.
    destruct H6. destruct H7.
    assert (rint_end q < rint_end q).
    { destruct H2.
      - eapply Qle_lt_trans; [ apply H8 |].
        eapply Qlt_le_trans; [ apply H2 |].
        apply Qle_trans with (rint_start q); auto.
        apply rint_proper.
      - eapply Qle_lt_trans; [ apply H9 |].
        eapply Qlt_le_trans; [ apply H2 |].
        apply Qle_trans with (rint_start q); auto.
        apply rint_proper.
    } 
    red in H10. lia.
Qed.

Lemma realdom_napart_eq_iff A (f g:A → PreRealDom) :
  canonical A f ->
  canonical A g ->
  realdom_converges A f ->
  realdom_converges A g ->
  (~realdom_apart A f g <-> f ≈ g).
Proof.
  intuition.
  - apply realdom_napart_eq; auto.
  - revert H4; apply realdom_le_napart; auto.
Qed.

Lemma realdom_apart_comm A (f g: A → PreRealDom) :
  realdom_apart A f g -> realdom_apart A g f.
Proof.
  unfold realdom_apart.
  intros [a [x [y [?[??]]]]].
  exists a, y, x; intuition.
Qed.

Lemma realdom_apart_cotransitive A (f g h:A → PreRealDom) :
  realdom_converges A h ->
  realdom_apart A f g ->
  realdom_apart A f h \/ realdom_apart A h g.
Proof.
  unfold realdom_apart; intuition.
  destruct H0 as [a [x [y [?[??]]]]].
  destruct H2.

  - set (ε := (rint_start y - rint_end x) / (2#1)%Q).
    assert (Hε : 0 < ε).
    { unfold ε.
      apply Qlt_shift_div_l.
      compute. auto.
      rewrite <- (Qplus_lt_l _ _ (rint_end x)).
      ring_simplify.
      auto.
    } 
    destruct (H a ε) as [q [??]]; auto.
    destruct (Qlt_le_dec (rint_end x) (rint_start q)).
    + left. exists a, x, q.
      intuition.
    + destruct (Qlt_le_dec (rint_end q) (rint_start y)).
      * right. exists a, q, y. intuition.
      * exfalso.
        assert (rint_start y <= ε + rint_end x).
        { apply Qle_trans with (rint_end q); auto.
          rewrite <- (Qplus_le_l _ _ (- rint_start q)).
          apply Qle_trans with ε.
          - ring_simplify.
            ring_simplify in H4; auto.
          - rewrite <- (Qplus_le_l _ _ (rint_start q)).
            ring_simplify.
            apply Qplus_le_r. auto.
        }
        assert (rint_start y - rint_end x <= ε).
        { unfold ε.
          rewrite <- (Qplus_le_l _ _ (rint_end x)).
          ring_simplify.
          unfold ε in H5.
          rewrite Qplus_comm. auto.
        } 
        assert (ε <= 0).
        rewrite <- (Qplus_le_l _ _ ε).
        ring_simplify.
        eapply Qle_trans; [ | apply H6 ].
        unfold ε. field_simplify.
        apply Qle_refl.
        assert (ε < ε).
        { apply Qle_lt_trans with 0%Q; auto. }
        red in H8. lia.

  - set (ε := (rint_start x - rint_end y) / (2#1)%Q).
    assert (Hε : 0 < ε).
    { unfold ε.
      apply Qlt_shift_div_l.
      - compute. auto.
      - rewrite <- (Qplus_lt_l _ _ (rint_end y)).
        ring_simplify.
        auto.
    } 
    destruct (H a ε) as [q [??]]; auto.
    destruct (Qlt_le_dec (rint_end y) (rint_start q)).
    + right. exists a, q, y.
      intuition.
    + destruct (Qlt_le_dec (rint_end q) (rint_start x)).
      * left. exists a, x, q. intuition.
      * exfalso.
  
        assert (rint_start x <= ε + rint_end y).
        { apply Qle_trans with (rint_end q); auto.
          rewrite <- (Qplus_le_l _ _ (- rint_start q)).
          apply Qle_trans with ε.
          - ring_simplify.
            ring_simplify in H4; auto.
          - rewrite <- (Qplus_le_l _ _ (rint_start q)).
            ring_simplify.
            apply Qplus_le_r. auto.
        } 
        assert (rint_start x - rint_end y <= ε).
        { unfold ε.
          rewrite <- (Qplus_le_l _ _ (rint_end y)).
          ring_simplify.
          unfold ε in H5.
          rewrite Qplus_comm. auto.
        } 
        assert (ε <= 0).
        { rewrite <- (Qplus_le_l _ _ ε).
          ring_simplify.
          eapply Qle_trans; [ | apply H6 ].
          unfold ε. field_simplify.
          apply Qle_refl.
        } 
        assert (ε < ε).
        { apply Qle_lt_trans with 0%Q; auto. }
        red in H8. lia.
Qed.


Lemma realdom_lt_apart (f g : 1 → PreRealDom) :
  realdom_apart 1 f g <-> (realdom_lt 1 f g \/ realdom_lt 1 g f).
Proof.
  split; intuition.
  - destruct H as [a [x [y [?[??]]]]].
    destruct H1; [ left | right ].
    + red; intros; exists x; exists y;
        destruct a; destruct a0; intuition.
    + red; intros; exists y; exists x;
        destruct a; destruct a0; intuition.

  - destruct (H0 tt) as [x[y[?[??]]]].
    exists tt, x, y; intuition.
  - destruct (H0 tt) as [x[y[?[??]]]].
    exists tt, y, x; intuition.
Qed.

Lemma realdom_lt_cotransitive (f g h:1 → PreRealDom) :
  realdom_converges 1 h ->
  realdom_lt 1 f g ->
  realdom_lt 1 f h \/ realdom_lt 1 h g.
Proof.
  intros.
  destruct (H0 tt) as [x[y [?[??]]]].

  set (ε := (rint_start y - rint_end x) / (2#1)%Q).
  assert (Hε : 0 < ε).
  { unfold ε.
    apply Qlt_shift_div_l.
    - compute. auto.
    - rewrite <- (Qplus_lt_l _ _ (rint_end x)).
      ring_simplify.
      auto.
  } 
  destruct (H tt ε) as [q [??]]; auto.
  destruct (Qlt_le_dec (rint_end x) (rint_start q)).
  - left. 
    red; intros. exists x. exists q.
    intuition.
  - destruct (Qlt_le_dec (rint_end q) (rint_start y)).
    + right. 
      red; intros. exists q. exists y. intuition.

    + exfalso.
      assert (rint_start y <= ε + rint_end x).
      { apply Qle_trans with (rint_end q); auto.
        rewrite <- (Qplus_le_l _ _ (- rint_start q)).
        apply Qle_trans with ε.
        - ring_simplify.
          ring_simplify in H5; auto.
        - rewrite <- (Qplus_le_l _ _ (rint_start q)).
          ring_simplify.
          apply Qplus_le_r. auto.
      } 
      assert (rint_start y - rint_end x <= ε).
      { unfold ε.
        rewrite <- (Qplus_le_l _ _ (rint_end x)).
        ring_simplify.
        unfold ε in H6.
        rewrite Qplus_comm. auto.
      } 
      assert (ε <= 0).
      { rewrite <- (Qplus_le_l _ _ ε).
        ring_simplify.
        eapply Qle_trans; [ | apply H7 ].
        unfold ε. field_simplify.
        apply Qle_refl.
      } 
      assert (ε < ε).
      { apply Qle_lt_trans with 0%Q; auto. }
      red in H9; lia.
Qed.

Lemma converges_maximal A (f g:A → PreRealDom) :
  canonical A g ->
  realdom_converges A f ->
  f ≤ g -> f ≈ g.
Proof.
  intros H H0 H1. split; auto.
  apply realdom_napart_le; auto.
  intro.
  destruct H2 as [a [r [s [?[??]]]]].
  apply H1 in H3.
  destruct (plt_hom_directed2 _ _ _ g a r s) as [t [?[??]]]; auto.
  apply rint_ord_test in H6.
  apply rint_ord_test in H7.
  intuition.
  - apply (Qlt_irrefl (rint_end r)).
    apply Qlt_le_trans with (rint_start s); auto.
    apply Qle_trans with (rint_start t); auto.
    apply Qle_trans with (rint_end t); auto.
    apply rint_proper.
  - apply (Qlt_irrefl (rint_end s)).
    apply Qlt_le_trans with (rint_start r); auto.
    apply Qle_trans with (rint_start t); auto.
    apply Qle_trans with (rint_end t); auto.
    apply rint_proper.
Qed.


Lemma realdom_converges_le A (f g:A → PreRealDom) :
  f ≤ g ->
  realdom_converges A f ->
  realdom_converges A g.
Proof.
  repeat intro.
  destruct (H0 a ε) as [r [??]]; auto.
  exists r; split; auto.
Qed.

Lemma realdom_lt_asym A (f g:A → PreRealDom) (a:A) :
  realdom_lt A f g -> realdom_lt A g f -> False.
Proof.
  unfold realdom_lt; intros.
  destruct (H a) as [x [y [?[??]]]].
  destruct (H0 a) as [p [q [?[??]]]].
  destruct (PLT.hom_directed _ _ _ f a (x::q::nil)%list) as [x' [??]]; auto.
  - exists x. apply cons_elem; auto.
  - red; intros ? HIN.
    apply erel_image_elem.
    apply cons_elem in HIN. destruct HIN as [HIN|HIN].
    + apply PLT.hom_order with a x; auto.
    + apply cons_elem in HIN. destruct HIN as [HIN|HIN].
      * apply PLT.hom_order with a q; auto.
      * apply nil_elem in HIN; elim HIN.
  - apply erel_image_elem in H8.
    assert (x ≤ x').
    { apply H7. apply cons_elem. auto. }
    assert (q ≤ x').
    { apply H7. apply cons_elem. right. apply cons_elem. auto. }
    apply rint_ord_test in H9.
    apply rint_ord_test in H10.
    destruct (PLT.hom_directed _ _ _ g a (y::p::nil)%list) as [y' [??]]; auto.
    + exists y. apply cons_elem; auto.
    + red; intros ? HIN.
      apply erel_image_elem.
      apply cons_elem in HIN. destruct HIN as [HIN|HIN].
      * apply PLT.hom_order with a y; auto.
      * apply cons_elem in HIN. destruct HIN as [HIN|HIN].
        ** apply PLT.hom_order with a p; auto.
        ** apply nil_elem in HIN; elim HIN.
    + apply erel_image_elem in H12.
      assert (y ≤ y').
      { apply H11. apply cons_elem. auto. }
      assert (p ≤ y').
      { apply H11. apply cons_elem. right. apply cons_elem. auto. }
      apply rint_ord_test in H13.
      apply rint_ord_test in H14.
      intuition.
      assert (rint_end x < rint_end x).
      { apply Qlt_le_trans with (rint_start y); auto.
        apply Qle_trans with (rint_start y'); auto.
        apply Qle_trans with (rint_end y').
        - apply rint_proper.
        - apply Qle_trans with (rint_end p); auto.
          apply Qlt_le_weak.
          apply Qlt_le_trans with (rint_start q); auto.
          apply Qle_trans with (rint_start x'); auto.
          apply Qle_trans with (rint_end x'); auto.
          apply rint_proper.
      } 
      red in H14. lia.
Qed.


Require Import cont_profinite.

Definition RealDom : c∂PLT :=
  cPLT.Ob true PreRealDom canon canon_idem.
