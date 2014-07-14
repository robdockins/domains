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


Program Definition canon : PreRealDom → PreRealDom :=
  PLT.Hom true PreRealDom PreRealDom canon_rel _ _.
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
  apply Qlt_le_weak.
  apply Qlt_trans with (rint_start x'); auto.
  apply Qle_lt_trans with (rint_end x'); auto.
  apply rint_proper.
  exists (RatInt q1 q2 H6).
  split; simpl.
  apply PLT.compose_hom_rel.
  exists x'. split; auto.
  simpl. apply canon_rel_elem.
  split; simpl; auto.
  split; simpl; auto.
Qed.

Lemma canon_canonical_iff (A:∂PLT) (f:A → PreRealDom) :
  canonical A f  <-> f ≈ canon ∘ f.
Proof.
  split; intros.
  split; hnf; intros.
  destruct a as [a x].
  hnf in H.
  destruct (H a x H0) as [x' [??]].
  apply PLT.compose_hom_rel.
  exists x'. split; auto.
  simpl. apply canon_rel_elem; auto.
  destruct a as [a x].
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [x' [??]].
  simpl in H1. apply canon_rel_elem in H1.
  apply PLT.hom_order with a x'; auto.
  apply rint_ord_test.
  destruct H1; split; apply Qlt_le_weak; auto.
  
  hnf; simpl; intros.
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
  destruct (H a) as [x [y [?[??]]]].
  exists x. exists y. intuition.
  apply Qlt_le_trans with (rint_start y + 0)%Q; auto.
  ring_simplify; auto.
  apply Qplus_le_compat; auto. apply Qle_refl.
  
  destruct (H a 0%Q) as [x [y [?[??]]]]. apply Qle_refl.
  exists x. exists y. intuition.
  ring_simplify in H2. auto.
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
  elim H.
  exists a, x, y; intuition.
  destruct (Qlt_le_dec (rint_end y) (rint_start x)).
  elim H.
  exists a, x, y; intuition.

  exists (Qmax (rint_start x) (rint_start y)).
  split.
  hnf; split.
  apply Q.le_max_l.
  apply Q.max_case; auto.
  intros. rewrite <- H2; auto.
  apply rint_proper.
  split.
  apply Q.le_max_r.
  apply Q.max_case; auto.
  intros. rewrite <- H2; auto.
  apply rint_proper.
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
  destruct H4.
  unfold ε.
  apply Q.min_case_strong; intros.
  rewrite <- H6; auto.
  rewrite <- (Qplus_lt_r _ _ (rint_start x)). ring_simplify. auto.
  rewrite <- (Qplus_lt_r _ _ (rint_end x')). ring_simplify. auto.

  destruct (realdom_napart_common A f g H1 a x' y) as [q [??]]; auto.
  destruct H7. destruct H8.
  apply PLT.hom_order with a y; auto.
  apply rint_ord_test.
  destruct H4.
  split.

  rewrite <- (Qplus_le_l _ _ ε).
  apply Qle_trans with (rint_start x').
  unfold ε.
  apply Q.min_case_strong. intros. rewrite <- H12; auto.
  intros. ring_simplify. apply Qle_refl.
  intros. 
  eapply Qle_trans.
  apply Qplus_le_r. apply H12.
  ring_simplify. apply Qle_refl.
  apply Qle_trans with q; auto.
  apply Qle_trans with (rint_end y); auto.
  rewrite <- (Qplus_le_l _ _ (- rint_start y)).
  ring_simplify.
  ring_simplify in H6.
  auto.

  rewrite <- (Qplus_le_l _ _ (- ε)).
  apply Qle_trans with (rint_end x').
  apply Qle_trans with q; auto.
  apply Qle_trans with (rint_start y); auto.
  rewrite <- (Qplus_le_l _ _ (- rint_start y)).
  rewrite <- (Qplus_le_l _ _ ε).
  ring_simplify.
  ring_simplify in H6.
  auto.
  unfold ε.
  apply Q.min_case_strong. intros. rewrite <- H12; auto.
  intros.
  rewrite <- (Qplus_le_l _ _ (rint_start x' - rint_start x)).
  eapply Qle_trans.
  apply Qplus_le_r. apply H12.
  ring_simplify. apply Qle_refl.
  intros.
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
  apply H; auto.
  destruct (PLT.hom_directed true _ _ f a (x::y::nil)%list) as [q [??]].
  exists x. apply cons_elem; auto.
  red; intros. apply erel_image_elem.
  apply cons_elem in H4. destruct H4.
  apply PLT.hom_order with a x; auto.
  apply cons_elem in H4. destruct H4.
  apply PLT.hom_order with a y; auto.
  apply nil_elem in H4. elim H4.
  apply erel_image_elem in H5.
  assert (x ≤ q).
  apply H4. apply cons_elem; auto.
  assert (y ≤ q).
  apply H4. apply cons_elem; right. apply cons_elem; auto.
  apply rint_ord_test in H6.
  apply rint_ord_test in H7.
  destruct H6. destruct H7.
  assert (rint_end q < rint_end q).
  destruct H2.
  eapply Qle_lt_trans. apply H8.
  eapply Qlt_le_trans. apply H2.
  apply Qle_trans with (rint_start q); auto.
  apply rint_proper.
  eapply Qle_lt_trans. apply H9.
  eapply Qlt_le_trans. apply H2.
  apply Qle_trans with (rint_start q); auto.
  apply rint_proper.
  red in H10. omega.
Qed.

Lemma realdom_napart_eq_iff A (f g:A → PreRealDom) :
  canonical A f ->
  canonical A g ->
  realdom_converges A f ->
  realdom_converges A g ->
  (~realdom_apart A f g <-> f ≈ g).
Proof.
  intuition.
  apply realdom_napart_eq; auto.
  revert H4; apply realdom_le_napart; auto.
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

  set (ε := (rint_start y - rint_end x) / (2#1)%Q).
  assert (Hε : 0 < ε).
    unfold ε.
    apply Qlt_shift_div_l.
    compute. auto.
    rewrite <- (Qplus_lt_l _ _ (rint_end x)).
    ring_simplify.
    auto.
  destruct (H a ε) as [q [??]]; auto.
  destruct (Qlt_le_dec (rint_end x) (rint_start q)).
  left. exists a, x, q.
  intuition.
  destruct (Qlt_le_dec (rint_end q) (rint_start y)).
  right. exists a, q, y. intuition.
  exfalso.
  assert (rint_start y <= ε + rint_end x).
  apply Qle_trans with (rint_end q); auto.
  rewrite <- (Qplus_le_l _ _ (- rint_start q)).
  apply Qle_trans with ε.
  ring_simplify.
  ring_simplify in H4; auto.
  rewrite <- (Qplus_le_l _ _ (rint_start q)).
  ring_simplify.
  apply Qplus_le_r. auto.
  assert (rint_start y - rint_end x <= ε).
  unfold ε.
  rewrite <- (Qplus_le_l _ _ (rint_end x)).
  ring_simplify.
  unfold ε in H5.
  rewrite Qplus_comm. auto.
  assert (ε <= 0).
  rewrite <- (Qplus_le_l _ _ ε).
  ring_simplify.
  eapply Qle_trans. 2: apply H6.
  unfold ε. field_simplify.
  apply Qle_refl.
  assert (ε < ε).
  apply Qle_lt_trans with 0%Q; auto.
  red in H8. omega.

  set (ε := (rint_start x - rint_end y) / (2#1)%Q).
  assert (Hε : 0 < ε).
    unfold ε.
    apply Qlt_shift_div_l.
    compute. auto.
    rewrite <- (Qplus_lt_l _ _ (rint_end y)).
    ring_simplify.
    auto.
  destruct (H a ε) as [q [??]]; auto.
  destruct (Qlt_le_dec (rint_end y) (rint_start q)).
  right. exists a, q, y.
  intuition.
  destruct (Qlt_le_dec (rint_end q) (rint_start x)).
  left. exists a, x, q. intuition.
  exfalso.
  
  assert (rint_start x <= ε + rint_end y).
  apply Qle_trans with (rint_end q); auto.
  rewrite <- (Qplus_le_l _ _ (- rint_start q)).
  apply Qle_trans with ε.
  ring_simplify.
  ring_simplify in H4; auto.
  rewrite <- (Qplus_le_l _ _ (rint_start q)).
  ring_simplify.
  apply Qplus_le_r. auto.
  assert (rint_start x - rint_end y <= ε).
  unfold ε.
  rewrite <- (Qplus_le_l _ _ (rint_end y)).
  ring_simplify.
  unfold ε in H5.
  rewrite Qplus_comm. auto.
  assert (ε <= 0).
  rewrite <- (Qplus_le_l _ _ ε).
  ring_simplify.
  eapply Qle_trans. 2: apply H6.
  unfold ε. field_simplify.
  apply Qle_refl.
  assert (ε < ε).
  apply Qle_lt_trans with 0%Q; auto.
  red in H8. omega.
Qed.


Lemma realdom_lt_apart (f g : 1 → PreRealDom) :
  realdom_apart 1 f g <-> (realdom_lt 1 f g \/ realdom_lt 1 g f).
Proof.
  split; intuition.
  destruct H as [a [x [y [?[??]]]]].
  destruct H1; [ left | right ].
  red; intros; exists x; exists y;
    destruct a; destruct a0; intuition.
  red; intros; exists y; exists x;
    destruct a; destruct a0; intuition.

  destruct (H0 tt) as [x[y[?[??]]]].
  exists tt, x, y; intuition.
  destruct (H0 tt) as [x[y[?[??]]]].
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
    unfold ε.
    apply Qlt_shift_div_l.
    compute. auto.
    rewrite <- (Qplus_lt_l _ _ (rint_end x)).
    ring_simplify.
    auto.
  destruct (H tt ε) as [q [??]]; auto.
  destruct (Qlt_le_dec (rint_end x) (rint_start q)).
  left. 
  red; intros. exists x. exists q.
  intuition.
  destruct (Qlt_le_dec (rint_end q) (rint_start y)).
  right. 
  red; intros. exists q. exists y. intuition.

  exfalso.
  assert (rint_start y <= ε + rint_end x).
  apply Qle_trans with (rint_end q); auto.
  rewrite <- (Qplus_le_l _ _ (- rint_start q)).
  apply Qle_trans with ε.
  ring_simplify.
  ring_simplify in H5; auto.
  rewrite <- (Qplus_le_l _ _ (rint_start q)).
  ring_simplify.
  apply Qplus_le_r. auto.
  assert (rint_start y - rint_end x <= ε).
  unfold ε.
  rewrite <- (Qplus_le_l _ _ (rint_end x)).
  ring_simplify.
  unfold ε in H6.
  rewrite Qplus_comm. auto.
  assert (ε <= 0).
  rewrite <- (Qplus_le_l _ _ ε).
  ring_simplify.
  eapply Qle_trans. 2: apply H7.
  unfold ε. field_simplify.
  apply Qle_refl.
  assert (ε < ε).
  apply Qle_lt_trans with 0%Q; auto.
  red in H9; omega.
Qed.



Require Import cont_profinite.

Definition RealDom : c∂PLT :=
  cPLT.Ob true PreRealDom canon canon_idem.

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


Program Definition injq (q:Q) : PLT.unit true → PreRealDom :=
  PLT.Hom true _ PreRealDom (injq_rel q) _ _.
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

Program Definition real_opp : PreRealDom → PreRealDom :=
  PLT.Hom true PreRealDom PreRealDom real_opp_rel _ _.
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

Program Definition real_plus : (PreRealDom ⊗ PreRealDom)%plt → PreRealDom :=
  PLT.Hom true (PreRealDom ⊗ PreRealDom)%plt PreRealDom real_plus_rel _ _.
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



Definition real_mult_rel : erel (prod_preord rint_preord rint_preord) rint_preord :=
  esubset_dec (prod_preord (prod_preord rint_preord rint_preord) rint_preord)
     (fun xyz => (snd xyz) ≤ rint_mult (fst (fst xyz)) (snd (fst xyz)))
     (fun xyz => rint_dec _ _)
     (eprod (eprod rint_enum rint_enum) rint_enum).

Lemma real_mult_rel_elem x y z :
  (x,y,z) ∈ real_mult_rel <-> z ≤ rint_mult x y.
Proof.
  unfold real_mult_rel. rewrite esubset_dec_elem. simpl.
  intuition. apply eprod_elem. split.
  apply eprod_elem; split; apply rint_enum_complete'. apply rint_enum_complete'.
  simpl. intros.
  destruct x0 as [[??]?]. simpl in *.
  destruct y0 as [[??]?]. simpl in *.
  destruct H as [[[??]?][[??]?]] . simpl in *.
  rewrite H5. rewrite H0.
  hnf; simpl; intros.
  apply rint_mult_correct in H6.
  apply rint_mult_correct.
  destruct H6 as [q1  [q2 [?[??]]]].
  exists q1. exists q2. intuition.
Qed.

Program Definition real_mult : (PreRealDom ⊗ PreRealDom)%plt → PreRealDom :=
  PLT.Hom true (PreRealDom ⊗ PreRealDom)%plt PreRealDom real_mult_rel _ _.
Next Obligation.
  intros. 
  destruct x. destruct x'.
  rewrite real_mult_rel_elem in H1. rewrite real_mult_rel_elem.
  transitivity y; auto.
  rewrite H1.
  hnf; intros.
  apply rint_mult_correct in H2.
  apply rint_mult_correct.
  destruct H2 as [q1 [q2 [?[??]]]].
  destruct H. simpl in*.
  exists q1. exists q2. intuition.
Qed.
Next Obligation.
  intro. destruct x as [x y]. apply prove_directed; simpl; auto.
  intros. apply erel_image_elem in H. apply erel_image_elem in H0.
  apply real_mult_rel_elem in H.
  apply real_mult_rel_elem in H0.
  exists (rint_mult x y). split; auto. split; auto.
  apply erel_image_elem.
  apply real_mult_rel_elem. auto.
Qed.

Definition rint_recip (x y:rational_interval) :=
  forall a, in_interval a x -> exists a', in_interior a' y /\ a * a' == 1.

Lemma rint_recip_dec x y : { rint_recip x y } + { ~rint_recip x y }.
Proof.
  destruct (in_interval_dec 0 x).
  right. repeat intro.
  red in H.
  destruct (H 0%Q i) as [a' [??]].
  ring_simplify  in H1.
  hnf in H1.
  simpl in H1.
  discriminate.

  destruct (Qlt_le_dec  (rint_start y) (1/rint_end x) ).
  destruct (Qlt_le_dec (1/rint_start x) (rint_end y) ).

  left. red. intros.
  assert (~ a == 0).
  intro. apply n.
  red. rewrite <- H0. auto.
  exists (1/a).
  split.
  split; auto.

  apply Qlt_le_trans with (1/rint_end x); auto.

  destruct (Qlt_le_dec 0 a).
  apply Qle_shift_div_l; auto.
    apply Qle_trans with (a / rint_end x).
    field_simplify. apply Qle_refl.
    intro. apply n.
    split. rewrite <- H1.
    apply rint_proper.
    rewrite H1. apply Qle_refl.
    intro. apply n.
    split; auto.
    rewrite <- H1.
    apply rint_proper.
    rewrite H1. apply Qle_refl.
    apply Qle_shift_div_r; auto.
    apply Qlt_le_trans with a; auto.
    destruct H; auto.
    ring_simplify.
    destruct H; auto.
  apply Qle_shift_div_l'; auto.
    apply Qle_lteq in q1. intuition.
    apply Qle_trans with (a / rint_end x).
    apply Qle_shift_div_l'.
    destruct (Qlt_le_dec (rint_end x) 0); auto.
    elim n.
    split; auto.
    apply Qle_trans with a; auto.
    destruct H; auto.
    ring_simplify.
    destruct H; auto.
    field_simplify. apply Qle_refl.
    intro. apply n.
    split. rewrite <- H1.
    apply rint_proper.
    rewrite <- H1. apply Qle_refl.
    intro. apply n.
    split. rewrite <- H1.
    apply rint_proper.
    rewrite <- H1. apply Qle_refl.
    
  apply Qle_lt_trans with (1/rint_start x); auto.
  destruct (Qlt_le_dec 0 a).
  apply Qle_shift_div_r; auto.
    apply Qle_trans with (a / rint_start x).
    apply Qle_shift_div_l.
    destruct (Qlt_le_dec 0 (rint_start x)); auto.
    elim n.
    split. auto. apply Qle_trans with a; intuition.
    destruct H; auto.
    ring_simplify.
    destruct H; auto.
    field_simplify. apply Qle_refl.
    intro. apply n.
    split. rewrite <- H1. apply Qle_refl.
    rewrite <- H1.
    apply rint_proper.
    intro. apply n.
    split; auto.
    rewrite H1.
    apply Qle_refl.
    rewrite <- H1. apply rint_proper.
  apply Qle_shift_div_r'; auto.
    apply Qle_lteq in q1.
    intuition.
    apply Qle_trans with (a / rint_start x).
    field_simplify. apply Qle_refl.
    intro. apply n.
    split. rewrite H1. apply Qle_refl.
    rewrite <- H1. apply rint_proper.
    intro. apply n.
    split. rewrite H1. apply Qle_refl.
    rewrite <- H1. apply rint_proper.
    apply Qle_shift_div_r'.
    apply Qle_lt_trans with a.
    destruct H; auto.
    apply Qle_lteq in q1. intuition.
    ring_simplify.
    destruct H; auto.
  rewrite Qmult_div_r; auto.
  apply Qeq_refl.

  right. intro.
    hnf in H.
    destruct (H (rint_start x)).
    split; auto. apply Qle_refl. apply rint_proper.
    destruct H0. destruct H0.
    rewrite <- H1 in q0.
    field_simplify in q0.
    assert (x0 < x0).
    apply Qlt_le_trans with (rint_end y); auto.
    field_simplify; auto.
    red in H3. omega.
    rewrite q0 in H1.
    ring_simplify in H1. compute in H1. discriminate.

  right. intro.
    hnf in H.
    destruct (H (rint_end x)).
    split; auto.
    apply rint_proper. apply Qle_refl.
    destruct H0. destruct H0.
    rewrite <- H1 in q.
    field_simplify in q.
    assert (x0 < x0).
    apply Qle_lt_trans with (rint_start y); auto.
    field_simplify. auto.
    red in H3. omega.
    rewrite q in H1.
    ring_simplify in H1.
    hnf in H1. simpl in H1.
    discriminate.
Qed.


Definition real_recip_rel : erel rint_preord rint_preord :=
  esubset_dec (prod_preord rint_preord rint_preord)
     (fun xy => rint_recip (fst xy) (snd xy))
     (fun xy => rint_recip_dec (fst xy) (snd xy))
     (eprod rint_enum rint_enum).

Lemma real_recip_rel_elem  x y :
  (x,y) ∈ real_recip_rel <-> rint_recip x y.
Proof.
  unfold real_recip_rel.
  rewrite esubset_dec_elem.
  simpl. intuition.
  apply eprod_elem.
  split.
  destruct (rint_enum_complete x) as [n [x' [??]]].
  exists n. rewrite H0. auto.
  destruct (rint_enum_complete y) as [n [y' [??]]].
  exists n. rewrite H0. auto.
  unfold rint_recip. simpl; intuition.
  destruct (H0 a0) as [q [??]]; auto.
  destruct H as [[??][??]]. simpl in *.
  apply H. auto.
  exists q. split; auto.
  destruct H as [[??][??]]. simpl in *.
  apply rint_ord_test in H6.
  destruct H6.
  destruct H2; split.
  apply Qle_lt_trans with (rint_start b); auto.
  apply Qlt_le_trans with (rint_end b); auto.
Qed.

Program Definition real_recip : PreRealDom → PreRealDom :=
  PLT.Hom _ PreRealDom PreRealDom real_recip_rel _ _ .
Next Obligation.
  intros.
  rewrite real_recip_rel_elem in H1.
  rewrite real_recip_rel_elem.
  red; intros.
  destruct (H1 a) as [q [??]].
  apply H. auto.
  exists q; split; auto.
  apply rint_ord_test in H0.
  destruct H0.
  destruct  H3; split.
  apply Qle_lt_trans with (rint_start y); auto.
  apply Qlt_le_trans with (rint_end y); auto.
Qed.
Next Obligation.
  red; intro.
  apply prove_directed; auto.
  intros. 
  apply erel_image_elem in H.
  apply erel_image_elem in H0.
  rewrite real_recip_rel_elem in H.
  rewrite real_recip_rel_elem in H0.
  destruct (H (rint_start x)) as [q1 [??]].
  split; auto.
  apply Qle_refl. apply rint_proper.
  destruct (H0 (rint_start x)) as [q2 [??]].
  split; auto.
  apply Qle_refl. apply rint_proper.
  assert (q1 == q2).
  assert (~ rint_start x == 0).
  intro.
  rewrite H5 in H2.
  ring_simplify in H2.
  compute in H2. discriminate.
  apply Qeq_trans with (1 / rint_start x).
  apply Qmult_inj_r with (rint_start x); auto.
  field_simplify; auto.
  rewrite Qmult_comm in H2.
  field_simplify in H2.
  field_simplify in H2.
  auto.
  apply Qmult_inj_r with (rint_start x); auto.
  field_simplify; auto.
  field_simplify in H4.
  field_simplify in H4.
  apply Qeq_sym. auto.

  assert (Qmax (rint_start x0) (rint_start y) <=
          Qmin (rint_end x0) (rint_end y)).
  apply Qle_trans with q1.
  apply Q.max_case.
  intros. rewrite <- H6; auto.
  destruct H1; intuition.
  rewrite H5.
  destruct H3; intuition.
  apply Q.min_case.
  intros. rewrite <- H6; auto.
  destruct H1; intuition.
  rewrite H5.
  destruct H3; intuition.
  exists (RatInt _ _ H6).
  split.
  apply rint_ord_test.
  split; simpl.
  apply Q.le_max_l.
  apply Q.le_min_l.
  split.
  apply rint_ord_test.
  split; simpl.
  apply Q.le_max_r.
  apply Q.le_min_r.
  rewrite erel_image_elem.
  apply real_recip_rel_elem.
  red. simpl; intros.
  clear q1 H1 H2 q2 H3 H4 H5.
  
  destruct (H a) as [q1 [??]]; auto.
  destruct (H0 a) as [q2 [??]]; auto.
  assert (q1 == q2).
  assert (~ a == 0).
  intro.
  rewrite H5 in H2.
  ring_simplify in H2.
  compute in H2. discriminate.
  apply Qeq_trans with (1 / a).
  apply Qmult_inj_r with a; auto.
  field_simplify; auto.
  rewrite Qmult_comm in H2.
  field_simplify in H2.
  field_simplify in H2.
  auto.
  apply Qmult_inj_r with a; auto.
  field_simplify; auto.
  field_simplify in H4.
  field_simplify in H4.
  apply Qeq_sym. auto.
  
  exists q1.
  split; auto.
  split; simpl; auto.
  apply Q.max_case.
  intros. rewrite <- H8; auto.
  destruct H1; auto.
  rewrite H5. destruct H3; auto.
  apply Q.min_case.
  intros. rewrite <- H8; auto.
  destruct H1; auto.
  rewrite H5.
  destruct H3; auto.
Qed.

(*
Lemma real_recip_le1 (A:∂PLT) (x: A → PreRealDom) :
  (real_mult ∘ 《 x, real_recip ∘ x 》≤ injq 1 ∘ PLT.terminate _ A)%plt.
Proof.
  hnf; intros.
  destruct a as [a r].
  apply PLT.compose_hom_rel in H.
  destruct H as [[x1 x2] [??]].
  rewrite (PLT.pair_hom_rel _ _ _ _ _ _ a x1 x2) in H. destruct H.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [x' [??]].
  simpl in H0.
  apply real_mult_rel_elem in H0.
  simpl in H2.
  apply real_recip_rel_elem in H2.
  red in H2.
  apply PLT.compose_hom_rel. exists tt.
  split. simpl.
  apply eprod_elem. split; auto.
  apply eff_complete.
  apply single_axiom. auto.
  simpl.
  apply injq_rel_elem.
admit.
Qed.
*)

Lemma real_mult_comm_le A (g h:A → PreRealDom) :
  real_mult ∘ 《 g, h 》%plt ≤ real_mult ∘ 《 h, g 》%plt.
Proof.
  red; intros [x y] H.
  apply PLT.compose_hom_rel in H. apply PLT.compose_hom_rel.
  destruct H as [[a b] [??]].
  rewrite (PLT.pair_hom_rel _ _ _ _ g h) in H. destruct H.
  exists (b,a). split.
  apply PLT.pair_hom_rel. split; auto.
  simpl in *. apply real_mult_rel_elem in H0. apply real_mult_rel_elem.
  rewrite H0.
  hnf; intros.
  apply rint_mult_swap. auto.
Qed.

Lemma real_mult_comm A (g h:A → PreRealDom) :
  real_mult ∘ 《 g, h 》%plt ≈ real_mult  ∘ 《 h, g 》%plt.
Proof.
  split; apply real_mult_comm_le; auto.
Qed.

Lemma real_plus_comm_le A (g h:A → PreRealDom) :
  real_plus ∘ 《 g, h 》%plt ≤ real_plus ∘ 《 h, g 》%plt.
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

Lemma real_plus_comm A (g h:A → PreRealDom) :
  real_plus ∘ 《 g, h 》%plt ≈ real_plus ∘ 《 h, g 》%plt.
Proof.
  split; apply real_plus_comm_le; auto.
Qed.

Lemma real_mult_assoc A (f g h:A → PreRealDom) :
  (real_mult ∘ 《 f, real_mult ∘ 《 g, h 》 》 ≈
   real_mult ∘ 《 real_mult ∘ 《 f, g 》, h 》)%plt.
Proof.
  split; intros [x y] H.  
  apply PLT.compose_hom_rel in H. apply PLT.compose_hom_rel.
  destruct H as [[a b] [??]].
  rewrite (PLT.pair_hom_rel _ _ _ _ f (real_mult ∘ 《g,h》%plt)) in H. destruct H.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [[c d] [??]].
  rewrite (PLT.pair_hom_rel _ _ _ _ g h) in H1. destruct H1.
  exists (rint_mult a c,d).
  split.
  apply PLT.pair_hom_rel.
  split; auto.
  apply PLT.compose_hom_rel.
  exists (a,c). split.
  apply PLT.pair_hom_rel. split; auto.
  simpl. apply real_mult_rel_elem. auto.
  simpl. apply real_mult_rel_elem. 
  apply real_mult_rel_elem in H0. rewrite H0.
  apply real_mult_rel_elem in H2. 
  hnf; intros.
  apply rint_mult_correct in H4.
  destruct H4 as [q1 [q2 [?[??]]]].
  apply rint_mult_correct in H4.
  destruct H4 as [q3 [q4 [?[??]]]].
  apply rint_mult_correct.
  exists q3. exists (q4*q2).
  intuition.
  apply H2.
  apply rint_mult_correct.
  exists q4. exists q2.
  intuition.
  rewrite H6.
  rewrite H8.
  symmetry. apply Qmult_assoc.

  apply PLT.compose_hom_rel in H.  
  destruct H as [[a b][??]].
  apply (PLT.pair_hom_rel _ _ _ _ (real_mult ∘ 《f, g》%plt) h) in H.
  destruct H.
  apply PLT.compose_hom_rel in H.  
  destruct H as [[c d][??]].
  apply PLT.compose_hom_rel.
  apply (PLT.pair_hom_rel _ _ _ _ f g) in H. destruct H.
  exists (c, rint_mult d b).
  split.
  apply PLT.pair_hom_rel. split; auto.
  apply PLT.compose_hom_rel.
  exists (d,b). split.
  apply PLT.pair_hom_rel. split; auto.
  simpl. apply real_mult_rel_elem. auto.
  apply real_mult_rel_elem.
  apply real_mult_rel_elem in H0.
  apply real_mult_rel_elem in H2.
  hnf; intros.
  apply rint_mult_correct in H4.
  destruct H4 as [q1 [q2 [?[??]]]].
  apply rint_mult_correct in H5.
  destruct H5 as [q3 [q4 [?[??]]]].
  apply H0.
  apply rint_mult_correct.
  exists (q1*q3). exists q4.
  intuition.
  apply H2.
  apply rint_mult_correct.
  exists q1. exists q3. intuition.
  rewrite H6.
  rewrite H8.
  apply Qmult_assoc.
Qed.


Lemma real_plus_assoc A (f g h:A → PreRealDom) :
  (real_plus ∘ 《 f, real_plus ∘ 《 g, h 》 》 ≈
   real_plus ∘ 《 real_plus ∘ 《 f, g 》, h 》)%plt.
Proof.
  split; intros [x y] H.  
  apply PLT.compose_hom_rel in H. apply PLT.compose_hom_rel.
  destruct H as [[a b] [??]].
  rewrite (PLT.pair_hom_rel _ _ _ _ f (real_plus ∘ 《g,h》%plt)) in H. destruct H.
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
  apply (PLT.pair_hom_rel _ _ _ _ (real_plus ∘ 《f, g》%plt) h) in H.
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

Lemma real_plus_0_le A (h: A → PreRealDom) :
  real_plus ∘ 《 h, injq 0 ∘ PLT.terminate true A 》%plt ≤ h.
Proof.
  hnf; simpl; intros.
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
Qed.

Lemma real_plus_0_eq A (h: A → PreRealDom) :
  canonical A h ->
  real_plus ∘ 《 h, injq 0 ∘ PLT.terminate true A 》%plt ≈ h.
Proof.
  intros. split. apply real_plus_0_le.
  hnf; intros. destruct a as [a x].
  apply PLT.compose_hom_rel.
  destruct (H a x) as [x' [??]]; auto.
  set (q1 := rint_start x - rint_start x').
  set (q2 := rint_end x - rint_end x').
  destruct H2.
  assert ( q1 < 0 ).
  unfold q1.
  rewrite <- (Qplus_lt_l _ _ (rint_start x')).
  ring_simplify. auto.
  assert( 0 < q2 ).
  unfold q2.
  rewrite <- (Qplus_lt_l _ _ (rint_end x')).
  ring_simplify. auto.
  assert (q1 <= q2).
  apply Qlt_le_weak.
  apply Qlt_trans with 0%Q; auto.
  exists (x', RatInt q1 q2 H6).
  simpl; split.
  apply PLT.pair_hom_rel. split; auto.
  apply PLT.compose_hom_rel.
  exists tt. split; auto.
  simpl. apply eprod_elem.
  split. apply eff_complete. apply single_axiom. auto.
  simpl. apply injq_rel_elem.
  split; simpl; auto.
  apply real_plus_rel_elem.
  apply rint_ord_test; split; simpl; auto.
  unfold q1. ring_simplify. apply Qle_refl.
  unfold q2. ring_simplify. apply Qle_refl.
Qed.

Lemma real_opp_0_le A (h : A → PreRealDom) 
  (Hh : canonical A h) :
  real_plus ∘ 《 h, real_opp ∘ h 》%plt ≤ injq 0 ∘ PLT.terminate true A.
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
  
  red.
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
  apply rint_ord_test in H0. simpl in H0.
  destruct H0.
  destruct (Hh c z) as [z' [??]]; auto.
  destruct H12.
  split.
  eapply Qle_lt_trans. apply H0.
  rewrite <- (Qplus_lt_l _ _ (- rint_start b)).
  ring_simplify.
  apply Qle_lt_trans with (rint_start z); auto.
  apply Qlt_le_trans with (rint_start z'); auto.
  rewrite <- (Qplus_le_l _ _ (rint_start b)).
  ring_simplify.
  eapply Qle_trans.
  apply (Qplus_le_r). apply H2.
  rewrite <- (Qplus_le_l _ _ (rint_end q)).
  ring_simplify.
  apply Qle_trans with (rint_end z').
  apply rint_proper.
  apply Qle_trans with (rint_end z); auto.
  apply Qlt_le_weak; auto.
  
  eapply Qlt_le_trans. 2: apply H10.
  rewrite <- (Qplus_lt_l _ _ (- rint_end a)).
  ring_simplify.
  apply Qlt_le_trans with (- rint_start q); auto.
  cut (- rint_end a < -rint_start q).
  intros.
  ring_simplify.
  ring_simplify in H14. auto.
  rewrite <- (Qplus_lt_l _ _ (rint_end a)).
  rewrite <- (Qplus_lt_l _ _ (rint_start q)).
  ring_simplify.
  apply Qle_lt_trans with (rint_start z); auto.
  apply Qlt_le_trans with (rint_start z'); auto.
  apply Qle_trans with (rint_end z'); auto.
  apply rint_proper.
  apply Qle_trans with (rint_end z); auto.
  apply Qlt_le_weak; auto.
Qed.

Lemma real_opp_0_le2 A (h : A → PreRealDom) 
  (Hh : realdom_converges A h) :
  real_plus ∘ 《 h, real_opp ∘ h 》%plt ≥ injq 0 ∘ PLT.terminate true A.
Proof.
  hnf; intros [a x] ?.
  apply PLT.compose_hom_rel in H.
  destruct H as [[] [??]].
  set (ε := Qmin (- rint_start x) (rint_end x)).
  assert (Hε : 0 < ε).
    unfold ε.
    simpl in H0. apply injq_rel_elem in H0. destruct H0.
    apply Q.min_case_strong; intros.
    rewrite <- H2; auto.
    rewrite <- (Qplus_lt_l _ _ (rint_start x)). ring_simplify. auto.
    auto.
  destruct (Hh a ε) as [z [??]]; auto.
  apply PLT.compose_hom_rel.
  exists (z, rint_opp z).
  split.
  apply PLT.pair_hom_rel.
  split; auto.
  apply PLT.compose_hom_rel.
  exists z. split; auto.
  simpl. apply real_opp_rel_elem.
  auto.
  simpl. apply real_plus_rel_elem.
  apply rint_ord_test.
  simpl.
  split.
  rewrite <- (Qplus_le_l _ _ (rint_end z - rint_start z)).
  rewrite <- (Qplus_le_l _ _ (- rint_start x)).
  ring_simplify.
  ring_simplify in H2.
  eapply Qle_trans. apply H2.
  unfold ε.
  apply Q.le_min_l.
  eapply Qle_trans. apply H2.
  unfold ε.
  apply Q.le_min_r.
Qed.

Lemma real_opp_0_eq A (h : A → PreRealDom) :
  canonical A h ->
  realdom_converges A h ->
  real_plus ∘ 《 h, real_opp ∘ h 》%plt ≈ injq 0 ∘ PLT.terminate true A.
Proof.
  intros; split.
  apply real_opp_0_le; auto.
  apply real_opp_0_le2; auto.
Qed.


Lemma real_plus_reflects A (f g h:A → PreRealDom) :
  realdom_lt A (real_plus ∘ 《 f, h 》)%plt (real_plus ∘ 《 g, h 》)%plt ->
  realdom_lt A f g.
Proof.
  repeat intro.  
  destruct (H a) as [x [y [?[??]]]].
  apply PLT.compose_hom_rel in H0.
  apply PLT.compose_hom_rel in H1.
  destruct H0 as [[r m] [??]].
  destruct H1 as [[s n] [??]].
  rewrite (PLT.pair_hom_rel _ _ _ _ f h) in H0.
  rewrite (PLT.pair_hom_rel _ _ _ _ g h) in H1.
  destruct H0. destruct H1.
  simpl in *.
  apply real_plus_rel_elem in H3.
  apply real_plus_rel_elem in H4.
  apply rint_ord_test in H3.
  apply rint_ord_test in H4.
  simpl in *.
  destruct H3. destruct H4.
  exists r. exists s. intuition.
  rewrite <- (Qplus_lt_l _ _ (rint_end m)).
  apply Qle_lt_trans with (rint_end x); auto.
  apply Qlt_le_trans with (rint_start y); auto.
  apply Qle_trans with (rint_start s + rint_start n)%Q; auto.
  apply Qplus_le_compat. apply Qle_refl.
  destruct (PLT.hom_directed _ _ _ h a (m::n::nil)%list) as [z [??]].
  exists m. apply cons_elem; auto.
  red; intros ? HIN.
  apply erel_image_elem.
  apply cons_elem in HIN. destruct HIN as [HIN|HIN].
  apply PLT.hom_order with a m; auto.
  apply cons_elem in HIN. destruct HIN as [HIN|HIN].
  apply PLT.hom_order with a n; auto.
  apply nil_elem in HIN; elim HIN.
  apply erel_image_elem in H10.
  assert (m ≤ z).
    apply H9. apply cons_elem. auto.
  assert (n ≤ z).
    apply H9. apply cons_elem. right. apply cons_elem. auto.
  apply rint_ord_test in H11.
  apply rint_ord_test in H12.
  intuition.
  apply Qle_trans with (rint_start z); auto.
  apply Qle_trans with (rint_end z); auto.
  apply rint_proper.
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
  apply rint_ord_test in H0.
  destruct H; destruct H0.
  simpl in *.
  split.
  eapply Qle_lt_trans; eauto.
  rewrite <- (Qplus_lt_l _ _ q).
  rewrite <- (Qplus_lt_l _ _ (rint_end r)).
  ring_simplify. auto.
  eapply Qlt_le_trans. 2: apply H2.
  rewrite <- (Qplus_lt_l _ _ q).
  rewrite <- (Qplus_lt_l _ _ (rint_start r)).
  ring_simplify. auto.

  intros [??] ?. apply PLT.compose_hom_rel.
  exists (rint_opp c0).
  split. simpl. apply injq_rel_elem.
  red. simpl.
  simpl in H. apply injq_rel_elem in H.
  destruct H. split; simpl.
  rewrite <- (Qplus_lt_l _ _ (-q)).
  rewrite <- (Qplus_lt_l _ _ (rint_end c0)).
  ring_simplify. apply H0.
  rewrite <- (Qplus_lt_l _ _ (-q)).
  rewrite <- (Qplus_lt_l _ _ (rint_start c0)).
  ring_simplify. apply H.
  
  simpl. apply real_opp_rel_elem.
  apply rint_ord_test. simpl.
  rewrite Qopp_involutive.
  rewrite Qopp_involutive.
  split; apply Qle_refl.
Qed.

Lemma Q_real_lt_compat (q1 q2:Q) :
  realdom_lt 1%plt (injq q1) (injq q2) <-> q1 < q2.
Proof.
  split; intros.
  destruct (H tt) as [x [y [?[??]]]].

  simpl in H0. simpl in H1.
  apply injq_rel_elem in H0.
  apply injq_rel_elem in H1.
  destruct H0. destruct H1.
  apply Qlt_trans with (rint_end x); auto.
  apply Qlt_trans with (rint_start y); auto.

  red; intros.
  destruct (Q_dense q1 q2) as [q [??]]; auto.
  destruct (Q_dense q1 q) as [q1' [??]]; auto.
  destruct (Q_dense q q2) as [q2' [??]]; auto.
  assert (q1 - 1 < q1).
    rewrite <- (Qplus_lt_l _ _ 1).
    ring_simplify.
    rewrite Qplus_comm.
    apply Qle_lt_trans with (0 + q1)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_lt_le_compat.
    compute. auto. apply Qle_refl.
  assert (q1 - 1 <= q1')%Q.
    apply Qle_trans with q1; auto.
    apply Qlt_le_weak; auto.
    apply Qlt_le_weak; auto.
  assert (q2 < q2 + 1).
    rewrite Qplus_comm.
    apply Qle_lt_trans with (0 + q2)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_lt_le_compat.
    compute. auto. apply Qle_refl.
  assert (q2' <= q2+1).
    apply Qle_trans with q2; auto.
    apply Qlt_le_weak; auto.
    apply Qlt_le_weak; auto.

  exists (RatInt (q1-1) q1' H7), (RatInt q2' (q2+1) H9).
  repeat split; simpl.
  apply injq_rel_elem. split; simpl; auto.
  apply injq_rel_elem. split; simpl; auto.
  apply Qlt_trans with q; auto.
Qed.

Lemma Q_real_le_compat (q1 q2:Q) :
  realdom_le 1%plt (injq q1) (injq q2) <-> q1 <= q2.
Proof.
  split; intros.  
  red in H.
  destruct (Qlt_le_dec q2 q1); auto.
  exfalso.
    destruct (H tt (q1 - q2)) as [x [y [?[??]]]].
    rewrite <- (Qplus_lt_l _ _ q2).
    ring_simplify. auto.
    simpl in *.
    apply injq_rel_elem in H0.
    apply injq_rel_elem in H1.
    destruct H0; destruct H1.
    assert (rint_end x < rint_end x).
    eapply Qlt_trans. apply H2.
    rewrite <- (Qplus_lt_l _ _ q2).
    ring_simplify.
    apply Qplus_lt_le_compat; auto.
    apply Qlt_le_weak; auto.
    red in H5. omega.
  
  red; intros.
  set (ε' := ε / (3#1)).
  assert (0 < ε').
    unfold ε'.
    apply Qlt_shift_div_l.
    compute. auto.
    ring_simplify. auto.
  assert (q1 < ε' + q1).
    apply Qle_lt_trans with (0 + q1)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_lt_le_compat; auto. apply Qle_refl.
  assert (q1 - ε' < q1).
    rewrite <- (Qplus_lt_l _ _ ε').
    ring_simplify.
    rewrite Qplus_comm. auto.
  assert (q2 < ε' + q2).
    apply Qle_lt_trans with (0 + q2)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_lt_le_compat; auto. apply Qle_refl.
  assert (q2 - ε' < q2).
    rewrite <- (Qplus_lt_l _ _ ε').
    ring_simplify.
    rewrite Qplus_comm. auto.
  assert (q1 - ε' <= ε' + q1).  
    apply Qle_trans with q1; apply Qlt_le_weak; auto.
  assert (q2 - ε' <= ε' + q2).
    apply Qle_trans with q2; apply Qlt_le_weak; auto.
  exists (RatInt (q1 - ε') (ε' + q1) H6).
  exists (RatInt (q2 - ε') (ε' + q2) H7).
  simpl. repeat split.
  apply injq_rel_elem. split; simpl; auto.
  apply injq_rel_elem. split; simpl; auto.
  rewrite <- (Qplus_lt_l _ _ ε').
  ring_simplify.
  rewrite (Qplus_comm q2).
  apply Qplus_lt_le_compat; auto.
  unfold ε'.
  apply Qle_lt_trans with (((2#1)/(3#1)) * ε).
  field_simplify. apply Qle_refl.
  apply Qlt_le_trans with (1 * ε).
  rewrite Qmult_lt_r; auto.
  compute. auto.
  ring_simplify. apply Qle_refl.
Qed.


Lemma Q_real_eq_compat (q1 q2:Q) :
  injq q1 ≈ injq q2 <-> q1 == q2.
Proof.
  split; intros.
  destruct (Qcompare_spec q1 q2); auto.
  exfalso.
    apply Q_real_lt_compat in H0.
    apply (realdom_le_napart 1%plt (injq q1) (injq q2)); auto.
    apply realdom_lt_apart. auto.
  exfalso.
    apply Q_real_lt_compat in H0.
    apply (realdom_le_napart 1%plt (injq q2) (injq q1)); auto.
    apply realdom_lt_apart. auto.

  split; hnf; intros [a x] ?; simpl in *.
  apply injq_rel_elem in H0; apply injq_rel_elem.
  destruct H0. red. rewrite <- H. split; auto.
  apply injq_rel_elem in H0; apply injq_rel_elem.
  destruct H0. red. rewrite H. split; auto.
Qed.


Lemma realdom_lt_asym A (f g:A → PreRealDom) (a:A) :
  realdom_lt A f g -> realdom_lt A g f -> False.
Proof.
  unfold realdom_lt; intros.
  destruct (H a) as [x [y [?[??]]]].
  destruct (H0 a) as [p [q [?[??]]]].
  destruct (PLT.hom_directed _ _ _ f a (x::q::nil)%list) as [x' [??]]; auto.
  exists x. apply cons_elem; auto.
  red; intros ? HIN.
  apply erel_image_elem.
  apply cons_elem in HIN. destruct HIN as [HIN|HIN].
  apply PLT.hom_order with a x; auto.
  apply cons_elem in HIN. destruct HIN as [HIN|HIN].
  apply PLT.hom_order with a q; auto.
  apply nil_elem in HIN; elim HIN.
  apply erel_image_elem in H8.
  assert (x ≤ x').
    apply H7. apply cons_elem. auto.
  assert (q ≤ x').
    apply H7. apply cons_elem. right. apply cons_elem. auto.
  apply rint_ord_test in H9.
  apply rint_ord_test in H10.
  destruct (PLT.hom_directed _ _ _ g a (y::p::nil)%list) as [y' [??]]; auto.
  exists y. apply cons_elem; auto.
  red; intros ? HIN.
  apply erel_image_elem.
  apply cons_elem in HIN. destruct HIN as [HIN|HIN].
  apply PLT.hom_order with a y; auto.
  apply cons_elem in HIN. destruct HIN as [HIN|HIN].
  apply PLT.hom_order with a p; auto.
  apply nil_elem in HIN; elim HIN.
  apply erel_image_elem in H12.
  assert (y ≤ y').
    apply H11. apply cons_elem. auto.
  assert (p ≤ y').
    apply H11. apply cons_elem. right. apply cons_elem. auto.
  apply rint_ord_test in H13.
  apply rint_ord_test in H14.
  intuition.
  assert (rint_end x < rint_end x).
  apply Qlt_le_trans with (rint_start y); auto.
  apply Qle_trans with (rint_start y'); auto.
  apply Qle_trans with (rint_end y').
  apply rint_proper.
  apply Qle_trans with (rint_end p); auto.
  apply Qlt_le_weak.
  apply Qlt_le_trans with (rint_start q); auto.
  apply Qle_trans with (rint_start x'); auto.
  apply Qle_trans with (rint_end x'); auto.
  apply rint_proper.
  red in H14. omega.
Qed.



Lemma real_archimediean (f: 1%plt → PreRealDom) :
  realdom_converges 1%plt f ->
  exists q1 q2,
    realdom_lt 1%plt (injq q1) f /\ realdom_lt 1%plt f (injq q2).
Proof.
  intros.
  destruct (H tt 1%Q) as [x [??]].
  compute. auto.
  exists (rint_start x - 1).
  exists (rint_end x + 1)%Q.
  split.
  red; intros. destruct a. simpl.
  assert (rint_start x - (2#1) < rint_start x - 1).
    rewrite <- (Qplus_lt_l _ _ (2#1)%Q).
    ring_simplify.    
    rewrite Qplus_comm.
    apply Qle_lt_trans with (0 + rint_start x)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_lt_le_compat.
    compute. auto. apply Qle_refl.
  assert (rint_start x - 1 < rint_start x - (1#2)).
    rewrite <- (Qplus_lt_l _ _ 1).
    ring_simplify.
    rewrite Qplus_comm.
    apply Qle_lt_trans with (0 + rint_start x)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_lt_le_compat.
    compute. auto. apply Qle_refl.
  assert (rint_start x - (2#1) <= rint_start x - (1#2)).
    apply Qlt_le_weak. eapply Qlt_trans; eauto.
  exists (RatInt _ _ H4), x.
  repeat split; simpl; auto.
  apply injq_rel_elem.
  split; simpl; auto.
    ring_simplify.
    rewrite Qplus_comm.
    apply Qlt_le_trans with (0 + rint_start x)%Q.
    apply Qplus_lt_le_compat.
    compute. auto. apply Qle_refl.
    ring_simplify. apply Qle_refl.

  red; intros.
  assert (rint_end x + (1#2) < rint_end x + 1).
    rewrite Qplus_comm.
    rewrite (Qplus_comm _ 1).
    apply Qplus_lt_le_compat.
    compute. auto. apply Qle_refl.
  assert (rint_end x + 1 < rint_end x + (2#1)%Q).
    rewrite Qplus_comm.
    rewrite (Qplus_comm _ (2#1)).
    apply Qplus_lt_le_compat.
    compute. auto. apply Qle_refl.
  assert (rint_end x + (1#2) <= rint_end x + (2#1)).
    apply Qlt_le_weak. eapply Qlt_trans; eauto.
  exists x, (RatInt _ _ H4).
  repeat split; simpl; auto.
  apply injq_rel_elem.
  split; simpl; auto.
    rewrite Qplus_comm.
    apply Qle_lt_trans with (0 + rint_end x)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_lt_le_compat.
    compute. auto. apply Qle_refl.
Qed.


Lemma Q_real_plus_compat (q q1 q2:Q) :
  (real_plus ∘ 《 injq q1, injq q2 》 ≈ injq q)%plt <-> q1 + q2 == q.
Proof.
  split; intros.
  destruct (Qlt_le_dec q (q1+q2)).
    exfalso.
    set (ε := (q1+q2 - q) / (2#1)).
    assert (0 < ε).
      unfold ε.
      apply Qlt_shift_div_l.
      reflexivity.
      rewrite <- (Qplus_lt_l _ _ q).
      ring_simplify. auto.
    assert (q - ε <= q + ε).
    apply Qplus_le_compat.
    apply Qle_refl.
    apply Qle_trans with 0%Q.
    rewrite <- (Qplus_le_l _ _ ε).
    ring_simplify. apply Qlt_le_weak; auto. apply Qlt_le_weak; auto.

    assert (q + ε < q1 + q2).
      rewrite <- (Qmult_lt_r _ _ (2#1)). 2: compute; auto.
      unfold ε. field_simplify.
      apply Qle_lt_trans with (q + (q1+q2))%Q.
      rewrite (Qplus_assoc).
      field_simplify.
      field_simplify. apply Qle_refl.
      apply Qlt_le_trans with ((q1+q2)+(q1+q2))%Q.
      apply Qplus_lt_le_compat; auto. apply Qle_refl.
      field_simplify. apply Qle_refl.

    destruct H.
    assert ((tt,(RatInt  _ _ H1)) ∈ PLT.hom_rel (injq q)).
    simpl. apply injq_rel_elem.
    split; simpl.
    rewrite <- (Qplus_lt_l _ _ ε).
    ring_simplify.
    rewrite Qplus_comm.
    apply Qle_lt_trans with (0 + q)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_lt_le_compat; auto. apply Qle_refl.
    rewrite Qplus_comm.
    apply Qle_lt_trans with (0 + q)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_lt_le_compat; auto. apply Qle_refl.
    apply H3 in H4.
    apply PLT.compose_hom_rel in H4.
    destruct H4 as [[z w] [??]].
    simpl in H5. apply real_plus_rel_elem in H5.
    apply rint_ord_test in H5. simpl in H5. destruct H5.
    apply (PLT.pair_hom_rel true _ _ _ _ _ _ z w) in H4.
    destruct H4. simpl in H4, H7.
    apply injq_rel_elem in H4.
    apply injq_rel_elem in H7.
    destruct H4. destruct H7.
    assert (rint_end z + rint_end w < rint_end z + rint_end w).
    eapply Qle_lt_trans. apply H6.
    eapply Qlt_le_trans. apply H2.
    apply Qplus_le_compat; apply Qlt_le_weak; auto.
    red in H10. omega.
  destruct (Qlt_le_dec (q1+q2) q).
    exfalso.
    set (ε := (q - (q1+q2)) / (2#1)).
    assert (0 < ε).
      unfold ε.
      apply Qlt_shift_div_l.
      reflexivity.
      rewrite <- (Qplus_lt_l _ _ (q1+q2)).
      ring_simplify. auto.
    assert (q - ε <= q + ε).
    apply Qplus_le_compat.
    apply Qle_refl.
    apply Qle_trans with 0%Q.
    rewrite <- (Qplus_le_l _ _ ε).
    ring_simplify. apply Qlt_le_weak; auto. apply Qlt_le_weak; auto.

    assert (q1+q2+ ε < q).
      rewrite <- (Qmult_lt_r _ _ (2#1)). 2: compute; auto.
      unfold ε. field_simplify.
      apply Qle_lt_trans with ((q1+q2)+q)%Q.
      field_simplify. field_simplify. apply Qle_refl.
      apply Qlt_le_trans with (q+q)%Q.
      apply Qplus_lt_le_compat; auto. apply Qle_refl.
      field_simplify. apply Qle_refl.

    destruct H.
    assert ((tt,(RatInt  _ _ H1)) ∈ PLT.hom_rel (injq q)).
    simpl. apply injq_rel_elem.
    split; simpl.
    rewrite <- (Qplus_lt_l _ _ ε).
    ring_simplify.
    rewrite Qplus_comm.
    apply Qle_lt_trans with (0 + q)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_lt_le_compat; auto. apply Qle_refl.
    rewrite Qplus_comm.
    apply Qle_lt_trans with (0 + q)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_lt_le_compat; auto. apply Qle_refl.
    apply H3 in H4.
    apply PLT.compose_hom_rel in H4.
    destruct H4 as [[z w] [??]].
    simpl in H5. apply real_plus_rel_elem in H5.
    apply rint_ord_test in H5. simpl in H5. destruct H5.
    apply (PLT.pair_hom_rel true _ _ _ _ _ _ z w) in H4.
    destruct H4. simpl in H4, H7.
    apply injq_rel_elem in H4.
    apply injq_rel_elem in H7.
    destruct H4. destruct H7.
    assert (q - ε < q - ε).
    eapply Qle_lt_trans. apply H5.
    rewrite <- (Qplus_lt_l _ _ ε).
    ring_simplify.
    apply Qle_lt_trans with (q1+q2+ε)%Q.
    apply Qplus_le_compat.
    apply Qplus_le_compat; apply Qlt_le_weak; auto.
    apply Qle_refl.
    auto.
    red in H10. omega.

  apply Qle_antisym; auto.

  
  split; intros [u a] H0.
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [[b c][??]].
  apply (PLT.pair_hom_rel _ _ _ _ (injq q1) (injq q2)) in H0.
  destruct H0.
  simpl in H0. apply injq_rel_elem in H0.
  simpl in H2. apply injq_rel_elem in H2.
  simpl in H1. apply real_plus_rel_elem in H1.
  simpl. apply injq_rel_elem.
  apply rint_ord_test in H1.
  hnf. rewrite <- H.
  destruct H0; destruct H2; destruct H1.
  simpl in *.
  split.
  eapply Qle_lt_trans. apply H1.
  eapply Qlt_trans.
  apply Qplus_lt_l. apply H0.
  apply Qplus_lt_r. apply H2.
  eapply Qlt_le_trans. 2: apply H5.
  eapply Qlt_trans.
  apply Qplus_lt_l. apply H3.
  apply Qplus_lt_r. apply H4.
  
  simpl in H0.
  apply injq_rel_elem in H0.
  apply PLT.compose_hom_rel.
  destruct H0.
  set (ε := (Qmin (q-rint_start a) (rint_end a-q)) / (2#1)).
  assert (0 < ε).
    unfold ε.
    apply Qlt_shift_div_l.
    compute. auto.
    ring_simplify.
    apply Q.min_case.
    intros. rewrite <- H2; auto.
    rewrite <- (Qplus_lt_l _ _ (rint_start a)).
    ring_simplify. auto.
    rewrite <- (Qplus_lt_l _ _ q).
    ring_simplify. auto.
  assert (q1 - ε <= q1 + ε).
    apply Qle_trans with q1.
    rewrite <- (Qplus_le_l _ _ ε).
    ring_simplify.
    apply Qle_trans with (q1 + 0)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_le_compat.
    apply Qle_refl. apply Qlt_le_weak; auto.
    apply Qle_trans with (q1 + 0)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_le_compat.
    apply Qle_refl. apply Qlt_le_weak; auto.
  assert (q2 - ε <= q2 + ε).
    apply Qle_trans with q2.
    rewrite <- (Qplus_le_l _ _ ε).
    ring_simplify.
    apply Qle_trans with (q2 + 0)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_le_compat.
    apply Qle_refl. apply Qlt_le_weak; auto.
    apply Qle_trans with (q2 + 0)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_le_compat.
    apply Qle_refl. apply Qlt_le_weak; auto.
  exists (RatInt _ _ H3, RatInt _ _ H4).    
  split; simpl.
  apply PLT.pair_hom_rel; split; simpl.
  apply injq_rel_elem.
  split; simpl; auto.
  rewrite <- (Qplus_lt_l _ _ ε).
  ring_simplify.
  rewrite Qplus_comm.
  apply Qle_lt_trans with (0 + q1)%Q.
  ring_simplify. apply Qle_refl.
  apply Qplus_lt_le_compat; auto.
  apply Qle_refl.
  rewrite Qplus_comm.
  apply Qle_lt_trans with (0 + q1)%Q.
  ring_simplify. apply Qle_refl.
  apply Qplus_lt_le_compat; auto.
  apply Qle_refl.
  apply injq_rel_elem.
  split; simpl; auto.
  rewrite <- (Qplus_lt_l _ _ ε).
  ring_simplify.
  rewrite Qplus_comm.
  apply Qle_lt_trans with (0 + q2)%Q.
  ring_simplify. apply Qle_refl.
  apply Qplus_lt_le_compat; auto.
  apply Qle_refl.
  rewrite Qplus_comm.
  apply Qle_lt_trans with (0 + q2)%Q.
  ring_simplify. apply Qle_refl.
  apply Qplus_lt_le_compat; auto.
  apply Qle_refl.
  simpl. apply real_plus_rel_elem.
  apply rint_ord_test. simpl.

  split.
  rewrite <- (Qplus_le_l _ _ ((2#1)*ε)%Q).
  ring_simplify.
  unfold ε.
  apply Q.min_case_strong.
  intros. rewrite <- H5. auto.
  intros.
  rewrite Qmult_div_r.
  2: compute; discriminate.
  ring_simplify. rewrite H. apply Qle_refl.
  rewrite Qmult_div_r.
  2: compute; discriminate.
  rewrite H.
  intros.
  apply Qle_trans with (rint_start a + (q - rint_start a))%Q.
  apply Qplus_le_compat. apply Qle_refl. auto.
  ring_simplify. apply Qle_refl.
  
  apply Qle_trans with (q + (2#1)*ε)%Q.
  rewrite <- H. ring_simplify. apply Qle_refl.
  unfold ε.
  apply Q.min_case_strong.
  intros. rewrite <- H5. auto.
  intros.
  rewrite Qmult_div_r.
  2: compute; discriminate.
  apply Qle_trans with (q + (rint_end a - q))%Q.
  apply Qplus_le_compat. apply Qle_refl. auto.
  ring_simplify. apply Qle_refl.
  intros.
  rewrite Qmult_div_r.
  2: compute; discriminate.
  ring_simplify. apply Qle_refl.
Qed.
