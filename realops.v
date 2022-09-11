Require Import QArith.
Require Import Setoid.
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
Require Import realdom.

Require Import Qabs.
Require Import Qminmax.


(**  The rational numbers inject into RealDom.
  *)

Definition injq_rel (q:Q) : erel unitpo PreRealDom :=
  esubset_dec (prod_preord unitpo PreRealDom)
     (fun x => in_interior q (snd x))
     (fun x => in_interior_dec q (snd x))
     (eprod (single tt) rint_enum).

Lemma injq_rel_elem (q:Q) (u:unit) (r:rational_interval) :
  (u, r) ∈ injq_rel q <-> in_interior q r.
Proof.
  destruct u.
  unfold injq_rel.
  rewrite esubset_dec_elem.
  - simpl. intuition.
    apply eprod_elem.
    split.
    + apply single_axiom; auto.
    + destruct (rint_enum_complete r) as [n [r' [??]]]; auto.
      exists n. rewrite H0. auto.
  - intros. destruct H. 
    destruct H. destruct H1.
    destruct x. destruct y. simpl in *.
    apply rint_ord_test in H3. destruct H3.
    destruct H0. split.
    + eapply Qle_lt_trans; eauto.
    + eapply Qlt_le_trans; eauto.
Qed.


Program Definition injq (q:Q) : PLT.unit true → PreRealDom :=
  PLT.Hom true _ PreRealDom (injq_rel q) _ _.
Next Obligation.
  intros. apply injq_rel_elem in H1. apply injq_rel_elem.
  apply rint_ord_test in H0. destruct H0.
  destruct H1. split.
  - eapply Qle_lt_trans; eauto.
  - eapply Qlt_le_trans; eauto.
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
  { apply Q.max_case; intros.
    - rewrite <- H3; auto.
    - apply Q.min_case; intros.
      + rewrite <- H3; auto.
      + apply rint_proper.
      + apply Qlt_le_weak.
        apply Qlt_trans with q; auto.
    - apply Q.min_case; intros.
      + rewrite <- H3; auto.
      + apply Qlt_le_weak.
        apply Qlt_trans with q; auto.
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
      apply injq_rel_elem.
      split; simpl.
      * apply Q.max_case; intros; auto.
        rewrite <- H4; auto.
      * apply Q.min_case; intros; auto.
        rewrite <- H4; auto.
Qed.

Lemma injq_canon A q :
  canonical A (injq q ∘ PLT.terminate _ A).
Proof.
  red; intros.
  apply PLT.compose_hom_rel in H.
  destruct H as [[] [??]].
  simpl in H0.
  apply injq_rel_elem in H0.
  destruct H0.
  destruct (Q_dense (rint_start x) q) as [y1 [??]]; auto.
  destruct (Q_dense q (rint_end x)) as [y2 [??]]; auto.
  assert (y1 <= y2).
  { apply Qle_trans with q; intuition. }
  exists (RatInt y1 y2 H6).
  split.
  - apply PLT.compose_hom_rel.
    exists tt. split; simpl; auto.
    apply injq_rel_elem.
    split; simpl; auto.
  - split; simpl; auto.
Qed.

Lemma injq_converges A q :
  realdom_converges A (injq q ∘ PLT.terminate _ A). 
Proof.
  red; intros.
  set (x1 := q - ε/(2#1)).
  set (x2 := (q + ε/(2#1))%Q).
  assert (x1 <= x2).
  { unfold x1, x2.
    rewrite <- (Qplus_le_l _ _ (ε/(2#1))). ring_simplify.
    field_simplify.
    field_simplify.
    apply Qle_trans with (q + 0)%Q.
    - field_simplify. apply Qle_refl.
    - apply Qle_trans with (q + ε)%Q.
      + apply Qplus_le_compat; intuition.
      + field_simplify. 
        field_simplify. intuition.
  } 
  exists (RatInt x1 x2 H0).
  simpl. split.
  - apply PLT.compose_hom_rel.
    exists tt. split.
    + simpl. apply eprod_elem.
      split.
      * apply eff_complete.
      * apply single_axiom; auto.
    + simpl. apply injq_rel_elem.
      split; simpl.
      * unfold x1.
        rewrite <- (Qplus_lt_l _ _ (ε/(2#1))). ring_simplify.
        apply Qle_lt_trans with (q + 0)%Q.
        ** ring_simplify. apply Qle_refl.
        ** rewrite (Qplus_comm q).
           rewrite (Qplus_comm q).
           apply Qplus_lt_le_compat.
           *** apply Qlt_shift_div_l.
               **** compute. auto.
               **** ring_simplify. auto.
           *** intuition.
      * unfold x2.
        apply Qle_lt_trans with (q + 0)%Q.
        ** ring_simplify. apply Qle_refl.
        ** rewrite (Qplus_comm q).
           rewrite (Qplus_comm q).
           apply Qplus_lt_le_compat.
           *** apply Qlt_shift_div_l.
               **** compute. auto.
               **** ring_simplify. auto.
           *** intuition.
  - unfold x2, x1.
    ring_simplify.
    field_simplify.
    field_simplify.
    apply Qle_refl.
Qed.


(**  The negation operator *)

Definition real_opp_rel : erel rint_preord rint_preord :=
  esubset_dec (prod_preord rint_preord rint_preord)
     (fun xy => snd xy ≤ rint_opp (fst xy))
     (fun xy => rint_dec _ _)
     (eprod rint_enum rint_enum).

Lemma real_opp_rel_elem x y :
  (x,y) ∈ real_opp_rel <-> y ≤ rint_opp x.
Proof.
  unfold real_opp_rel. rewrite esubset_dec_elem.
  - simpl; intuition.
    apply eprod_elem; split; apply rint_enum_complete'.
  - simpl; intros.
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
  - red; intros.
    apply H in H0. apply erel_image_elem in H0.
    apply real_opp_rel_elem in H0. auto.
  - apply erel_image_elem.
    apply real_opp_rel_elem. auto.
Qed.


Lemma real_opp_canonical A f :
  canonical A f ->
  canonical A (real_opp ∘ f).
Proof.
  repeat intro.
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [y [??]].
  simpl in H1. apply real_opp_rel_elem in H1.
  destruct (H a y) as [y' [??]]; auto.
  exists (rint_opp y'). split.
  - apply PLT.compose_hom_rel.
    exists y'. split; auto.
    simpl. apply real_opp_rel_elem. auto.
  - destruct H3.
    apply rint_ord_test in H1.
    simpl in H1. destruct H1.
    split; simpl.
    + apply Qle_lt_trans with (-rint_end y); auto.
      rewrite <- (Qplus_lt_l _ _ (rint_end y')).
      rewrite <- (Qplus_lt_l _ _ (rint_end y)).
      ring_simplify. auto.
    + apply Qlt_le_trans with (-rint_start y); auto.
      rewrite <- (Qplus_lt_l _ _ (rint_start y')).
      rewrite <- (Qplus_lt_l _ _ (rint_start y)).
      ring_simplify. auto.
Qed.

Lemma real_opp_converges A f :
  realdom_converges A f ->
  realdom_converges A (real_opp ∘ f).
Proof.
  repeat intro.
  destruct (H a ε) as [r [??]]; auto.
  exists (rint_opp r).
  split.
  - apply PLT.compose_hom_rel.
    exists r. split; auto.
    simpl. apply real_opp_rel_elem. auto.
  - simpl.
    ring_simplify.
    ring_simplify in H2.
    rewrite Qplus_comm.
    auto.
Qed.


Lemma real_opp_inv : real_opp ∘ real_opp ≈ id.
Proof.
  split; hnf; simpl; intros [a r] H.
  - apply ident_elem.
    apply PLT.compose_hom_rel in H.
    destruct H as [y [??]].
    simpl in *.
    apply real_opp_rel_elem in H.
    apply real_opp_rel_elem in H0.
    hnf; simpl; intros.
    apply H0.
    cut (in_interval (-q) y).
    { intros.
      apply rint_opp_correct in H2.
      red in H2. rewrite Qopp_involutive in H2. auto.
    } 
    apply H.
    apply rint_opp_correct. auto.
  
  - simpl in H. apply ident_elem in H.
    apply PLT.compose_hom_rel.
    exists (rint_opp r).
    split.
    + simpl. apply real_opp_rel_elem.
      hnf; simpl; intros.
      cut (in_interval (-q) r).
      { intros.
        apply rint_opp_correct in H1.
        red in H1. rewrite Qopp_involutive in H1. auto.
      } 
      apply H.
      apply rint_opp_correct.
      red. rewrite Qopp_involutive. auto.
    + simpl. apply real_opp_rel_elem.
      apply rint_ord_test; simpl.
      do 2 rewrite Qopp_involutive.
      split; apply Qle_refl.
Qed.

Lemma realdom_lt0_opp A (f:A → PreRealDom) :
  realdom_lt A f (injq 0 ∘ PLT.terminate _ A) ->
  realdom_lt A (injq 0 ∘ PLT.terminate _ A) (real_opp ∘ f).
Proof.
  repeat intro.
  destruct (H a) as [x [y [?[??]]]].
  exists (rint_opp y).
  exists (rint_opp x).
  repeat split.
  - apply PLT.compose_hom_rel in H1.
    destruct H1 as [[][??]].
    apply PLT.compose_hom_rel. exists tt. split; auto.
    simpl in *.
    apply injq_rel_elem in H3.
    apply injq_rel_elem.
    destruct H3; split; simpl.
    + rewrite <- (Qplus_lt_l _ _ (rint_end y)). ring_simplify; auto.
    + rewrite <- (Qplus_lt_l _ _ (rint_start y)). ring_simplify; auto.
  - apply PLT.compose_hom_rel.
    exists x. split; auto.
    simpl. apply real_opp_rel_elem. auto.
  - simpl.
    apply Qopp_lt_compat. auto.
Qed.



(** The addition operator *)

Definition real_plus_rel : erel (prod_preord rint_preord rint_preord) rint_preord :=
  esubset_dec (prod_preord (prod_preord rint_preord rint_preord) rint_preord)
     (fun xyz => (snd xyz) ≤ rint_plus (fst (fst xyz)) (snd (fst xyz)))
     (fun xyz => rint_dec _ _)
     (eprod (eprod rint_enum rint_enum) rint_enum).

Lemma real_plus_rel_elem x y z :
  (x,y,z) ∈ real_plus_rel <-> z ≤ rint_plus x y.
Proof.
  unfold real_plus_rel.
  rewrite esubset_dec_elem.
  - simpl.
    intuition. apply eprod_elem. split.
    + apply eprod_elem; split; apply rint_enum_complete'.
    + apply rint_enum_complete'.
  - simpl. intros.
    destruct x0 as [[??]?]. simpl in *.
    destruct y0 as [[??]?]. simpl in *.
    destruct H as [[[??]?][[??]?]] . simpl in *.
    rewrite H5. rewrite H0.
    unfold rint_plus.
    apply rint_ord_test. simpl.
    apply rint_ord_test in H; destruct H.
    split; apply Qplus_le_compat; auto.
    + apply rint_ord_test in H1; destruct H1. auto.
    + apply rint_ord_test in H1; destruct H1. auto.
Qed.

Local Obligation Tactic := idtac.
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

Lemma real_plus_canon : forall A (f g:A → PreRealDom),
  canonical A f ->
  canonical A g ->
  canonical A (real_plus ∘ 《 f, g 》)%plt.
Proof.
  repeat intro.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [[p q] [??]].
  apply (PLT.pair_hom_rel _ _ _ _ f g) in H1. destruct H1.
  destruct (H a p) as [p' [??]]; auto.
  destruct (H0 a q) as [q' [??]]; auto.
  simpl in H2.
  apply real_plus_rel_elem in H2.
  exists (rint_plus p' q'). split.
  - apply PLT.compose_hom_rel.
    exists (p',q').
    split.
    + apply PLT.pair_hom_rel. split; auto.
    + simpl. apply real_plus_rel_elem. auto.
  - apply rint_ord_test in H2. simpl in H2.
    destruct H2.
    destruct H5. destruct H7.
    red; simpl; split.
    + eapply Qle_lt_trans; [ apply H2 |].
      apply Qplus_lt_le_compat; intuition.
    + eapply Qlt_le_trans; [| apply H8 ].
      apply Qplus_lt_le_compat; intuition.
Qed.

Lemma real_plus_converges : forall A (f g:A → PreRealDom),
  realdom_converges A f ->
  realdom_converges A g ->
  realdom_converges A (real_plus ∘ 《 f, g 》)%plt.
Proof.
  repeat intro.
  destruct (H a (ε/(2#1))) as [p [??]].
  - apply Qlt_shift_div_l.
    + compute. auto.
    + ring_simplify. auto.
  - destruct (H0 a (ε/(2#1))) as [q [??]].
    + apply Qlt_shift_div_l.
      * compute. auto.
      * ring_simplify. auto.
    + exists (rint_plus p q).
      split.
      * apply PLT.compose_hom_rel.
        exists (p,q).
        split.
        ** apply PLT.pair_hom_rel; split; auto.
        ** simpl. apply real_plus_rel_elem; auto.
      * simpl.
        apply Qle_trans with
          ((rint_end p - rint_start p) + (rint_end q - rint_start q))%Q.
        ** ring_simplify. apply Qle_refl.
        ** apply Qle_trans with ((ε/(2#1)) + (ε/(2#1)))%Q.
           *** apply Qplus_le_compat; auto.
           *** field_simplify.
               field_simplify.
               apply Qle_refl.
Qed.


(** The multiplication operator *)

Definition real_mult_rel : erel (prod_preord rint_preord rint_preord) rint_preord :=
  esubset_dec (prod_preord (prod_preord rint_preord rint_preord) rint_preord)
     (fun xyz => (snd xyz) ≤ rint_mult (fst (fst xyz)) (snd (fst xyz)))
     (fun xyz => rint_dec _ _)
     (eprod (eprod rint_enum rint_enum) rint_enum).

Lemma real_mult_rel_elem x y z :
  (x,y,z) ∈ real_mult_rel <-> z ≤ rint_mult x y.
Proof.
  unfold real_mult_rel. rewrite esubset_dec_elem.
  - simpl.
    intuition. apply eprod_elem. split.
    + apply eprod_elem; split; apply rint_enum_complete'.
    + apply rint_enum_complete'.
  - simpl. intros.
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
  destruct H. simpl in *.
  exists q1. exists q2. intuition.
Qed.
Next Obligation.
  intro. destruct x as [x y]. apply prove_directed; simpl; auto.
  - intros. apply erel_image_elem in H. apply erel_image_elem in H0.
    apply real_mult_rel_elem in H.
    apply real_mult_rel_elem in H0.
    exists (rint_mult x y). split; auto. split; auto.
    apply erel_image_elem.
    apply real_mult_rel_elem. auto.
Qed.


Lemma real_mult_canon : forall A (f g:A → PreRealDom),
  canonical A f ->
  canonical A g ->
  canonical A (real_mult ∘ 《 f, g 》)%plt.
Proof.
  repeat intro.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [[p q] [??]].
  apply (PLT.pair_hom_rel _ _ _ _ f g) in H1. destruct H1.
  destruct (H a p) as [p' [??]]; auto.
  destruct (H0 a q) as [q' [??]]; auto.
  simpl in H2.
  apply real_mult_rel_elem in H2.
  exists (rint_mult p' q'). split.
  - apply PLT.compose_hom_rel.
    exists (p',q').
    split.
    + apply PLT.pair_hom_rel. split; auto.
    + simpl. apply real_mult_rel_elem. auto.

  - apply way_inside_alt. intros.
    cut (in_interior x0 (rint_mult p q)).
    { intros.
      apply rint_ord_test in H2.
      destruct H2. destruct H9.
      split.
      - eapply Qle_lt_trans; [ apply H2 | auto ].
      - eapply Qlt_le_trans; [ apply H11 | auto ].
    } 
    apply rint_mult_correct in H8.
    destruct H8 as [q1 [q2 [?[??]]]].
    apply rint_mult_correct_interior with q1 q2.
    + rewrite <- way_inside_alt in H5.
      apply H5; auto.
    + rewrite <- way_inside_alt in H7.
      apply H7; auto.
    + auto.
Qed.


Lemma real_mult_converges : forall A (f g:A → PreRealDom),
  realdom_converges A f ->
  realdom_converges A g ->
  realdom_converges A (real_mult ∘ 《 f, g 》)%plt.
Proof.
  repeat intro.
  destruct (H a 1%Q) as [m [??]]; [ compute; auto |].
  destruct (H0 a 1%Q) as [n [??]]; [ compute; auto |].
  set (q := Qmax 1 (Qmax (Qabs (rint_start m))
                   (Qmax (Qabs (rint_end m))
                   (Qmax (Qabs (rint_start n))
                         (Qabs (rint_end n)))))).
  destruct (Qsolve_mult_quadratic q ε) as [γ [??]];
    [ unfold q; apply Q.le_max_l | auto |].
  destruct (H a γ) as [r [??]]; auto.
  destruct (H0 a γ) as [s [??]]; auto.
  
  destruct (plt_hom_directed2 _ _ _ f a m r) as [r' [?[??]]]; auto.
  destruct (plt_hom_directed2 _ _ _ g a n s) as [s' [?[??]]]; auto.
  
  assert (Hr' : rint_end r' - rint_start r' <= γ). 
  { eapply Qle_trans; [ | apply H9 ].
    ring_simplify.
    apply rint_ord_test in H14. destruct H14.
    apply Qplus_le_compat; auto.
    rewrite <- (Qplus_le_l _ _ (rint_start r')).
    rewrite <- (Qplus_le_l _ _ (rint_start r)).
    ring_simplify. auto.
  } 
  assert (Hs' : rint_end s' - rint_start s' <= γ). 
  { eapply Qle_trans; [ | apply H11 ].
    ring_simplify.
    apply rint_ord_test in H17. destruct H17.
    apply Qplus_le_compat; auto.
    rewrite <- (Qplus_le_l _ _ (rint_start s')).
    rewrite <- (Qplus_le_l _ _ (rint_start s)).
    ring_simplify. auto.
  } 

  exists (rint_mult r' s').
  split.
  - apply PLT.compose_hom_rel.
    exists (r',s').
    split.
    + apply PLT.pair_hom_rel; split; auto.
    + simpl. apply real_mult_rel_elem. auto.

  - apply rint_ord_test in H13.
    apply rint_ord_test in H16.
    revert Hr' Hs' H13 H16.
  
    cut (forall m1 m2 n1 n2,
         let q := Qmax 1
          (Qmax (Qabs m1)
             (Qmax (Qabs m2)
                (Qmax (Qabs n1) (Qabs n2))))
         in 
      rint_end r' - rint_start r' <= γ ->
      rint_end s' - rint_start s' <= γ ->
      m1 <= rint_start r' /\ rint_end r' <= m2 ->
      n1 <= rint_start s' /\ rint_end s' <= n2 ->
      rint_end (rint_mult r' s') - rint_start (rint_mult r' s') <=
      (((rint_end r'- rint_start r')*(rint_end s'-rint_start s')) + (2#1)*q*γ)).
    { intros.
      eapply Qle_trans; [ apply H13; auto; [ apply H16 | apply H18 ] | ].
      apply Qle_trans with (γ^2 + (2#1)*q*γ)%Q.
      - apply Qplus_le_compat.
        + simpl.
          apply Qmult_le_compat.
          * split; auto.
            apply (Qplus_le_l _ _ (rint_start r')). ring_simplify. apply rint_proper.
          * split; auto.
            apply (Qplus_le_l _ _ (rint_start s')). ring_simplify. apply rint_proper.
        + apply Qmult_le_compat; [ split |].
          * apply (Qmult_le_compat 0 0). 
            ** split.
               *** apply Qle_refl.
               *** compute. discriminate.
            ** split; [ apply Qle_refl |].
               apply Qle_trans with 1%Q; [ compute; discriminate |].
               apply Q.le_max_l.
          * apply Qmult_le_compat.
            ** split; [ compute; discriminate | apply Qle_refl ].
            ** split.
               *** apply Qle_trans with 1%Q; [ compute; discriminate |].
                   apply Q.le_max_l.
               *** apply Qle_refl.
          * intuition.
      - intuition.
    }

    clear -H6.
    apply rint_mult_ind.

    + intros.
      rewrite rint_mult_swap_end.
      rewrite rint_mult_swap_start.
      rewrite Qmult_comm.
      set (q' := Qmax 1 (Qmax (Qabs n1) (Qmax (Qabs n2) (Qmax (Qabs m1) (Qabs m2))))).
      assert (q == q').
      { unfold q'.
        rewrite (Q.max_assoc (Qabs n1)).
        rewrite (Q.max_comm (Qmax (Qabs n1) (Qabs n2))).
        rewrite <- Q.max_assoc.
        reflexivity.
      } 
      rewrite H4.
      apply H; auto.

    + intros.
      rewrite rint_mult_opp_end.
      rewrite rint_mult_opp_start.
      eapply Qle_trans.
      * apply (H (-m2) (-m1) (-n2) (-n1)); auto.
        ** simpl.
           ring_simplify.
           ring_simplify in H0.
           rewrite Qplus_comm. auto.
        ** simpl.
           ring_simplify.
           ring_simplify in H1.
           rewrite Qplus_comm. auto.
        ** simpl. split.
           *** apply Qopp_le_compat; intuition.
           *** apply Qopp_le_compat; intuition.
        ** simpl. split.
           *** apply Qopp_le_compat; intuition.
           *** apply Qopp_le_compat; intuition.
      * apply Qplus_le_compat.
        ** simpl.
           ring_simplify. apply Qle_refl.
        ** repeat rewrite Qabs_opp.
           rewrite (Q.max_assoc (Qabs m2)).
           rewrite (Q.max_comm (Qabs m2)).
           rewrite (Q.max_comm (Qabs n2)).
           rewrite <- (Q.max_assoc (Qabs m1)).
           apply Qle_refl.

    + simpl; intros.  
      set (q := Qmax 1
                 (Qmax (Qabs m1)
                   (Qmax (Qabs m2)
                     (Qmax (Qabs n1) (Qabs n2))))).
      rewrite H1. rewrite H2.
      ring_simplify.
      rewrite <- (Qplus_le_l _ _ (-(x2*y2))). ring_simplify.
      rewrite <- (Qplus_le_l _ _ (-(x1*y1))). ring_simplify.
      rewrite <- (Qplus_le_l _ _ ((x1*y2))). ring_simplify.
      rewrite <- (Qplus_le_l _ _ ((y1*x2))). ring_simplify.
      apply Qle_trans with
        ((x1*(y2-y1)) + (y1*(x2-x1)))%Q;
          [ ring_simplify; apply Qle_refl |].
      apply Qle_trans with (q*γ + q*γ)%Q; 
          [ | ring_simplify; apply Qle_refl ].
      apply Qplus_le_compat.  
      * apply Qmult_le_compat; intuition.
        ** apply Qle_trans with x2; auto.
           apply Qle_trans with m2; auto.
           apply Qle_trans with (Qabs m2); auto.
           *** rewrite Qabs_pos; intuition.
               apply Qle_trans with x2; auto.
               apply Qle_trans with x1; intuition.
           *** unfold q.
               eapply Qle_trans; [| apply Q.le_max_r ].
               eapply Qle_trans; [| apply Q.le_max_r ].
               apply Q.le_max_l.
        ** rewrite <- (Qplus_le_l _ _ y1). ring_simplify. auto.
      * apply Qmult_le_compat; intuition.
        ** apply Qle_trans with y2; auto.
           apply Qle_trans with n2; auto.
           apply Qle_trans with (Qabs n2); auto.
           *** rewrite Qabs_pos; intuition.
               apply Qle_trans with y2; auto.
               apply Qle_trans with y1; intuition.
           *** unfold q.
               eapply Qle_trans; [| apply Q.le_max_r ].
               eapply Qle_trans; [| apply Q.le_max_r ].
               eapply Qle_trans; [| apply Q.le_max_r ].
               apply Q.le_max_r.
        ** rewrite <- (Qplus_le_l _ _ x1). ring_simplify. auto.

    + simpl; intros.
      set (q := Qmax 1
            (Qmax (Qabs m1)
               (Qmax (Qabs m2)
                  (Qmax (Qabs n1) (Qabs n2))))).
      rewrite H1. rewrite H2.
      ring_simplify.
      rewrite <- (Qplus_le_l _ _ (-(x2*y2))). ring_simplify.
      rewrite <- (Qplus_le_l _ _ ((x2*y1))). ring_simplify.
      rewrite <- (Qplus_le_l _ _ (-(x1*y1))). ring_simplify.
      rewrite <- (Qplus_le_l _ _ ((x1*y2))). ring_simplify.
      apply Qle_trans with ((x1*(y2-y1)))%Q;
        [ ring_simplify; apply Qle_refl |].
      apply Qle_trans with (q*γ + q*γ)%Q;
        [| ring_simplify; apply Qle_refl ].
      apply Qle_trans with (0 + (x1*(y2-y1)))%Q.
      * ring_simplify. ring_simplify. 
        apply Qle_refl.
      * apply Qplus_le_compat.  
        ** apply (Qmult_le_compat 0 0); intuition.
           apply Qle_trans with 1%Q; [ compute; discriminate |].
           unfold q. apply Q.le_max_l.
        ** apply Qmult_le_compat.
           *** split; intuition.
               apply Qle_trans with (Qabs m2).
               **** apply Qle_trans with x2; auto.
                    rewrite Qabs_pos; auto.
                    apply Qle_trans with x2; auto.
                    apply Qle_trans with x1; intuition.
               **** unfold q.
                    eapply Qle_trans; [| apply Q.le_max_r ].
                    eapply Qle_trans; [| apply Q.le_max_r ].
                    apply Q.le_max_l.
           *** split; auto.
               rewrite <- (Qplus_le_l _ _ y1). ring_simplify. auto.

    + simpl; intros.
      set (q := Qmax 1
            (Qmax (Qabs m1)
               (Qmax (Qabs m2)
                  (Qmax (Qabs n1) (Qabs n2))))).
      rewrite H1. rewrite H2.
      ring_simplify.
      rewrite <- (Qplus_le_l _ _ ((x1*y2))). ring_simplify.
      rewrite <- (Qplus_le_l _ _ ((x2*y1))). ring_simplify.
      rewrite <- (Qplus_le_l _ _ (-(x2*y2))). ring_simplify.
      rewrite <- (Qplus_le_l _ _ (-(x1*y1))). ring_simplify.
      apply Qle_trans with
        ((x1*(y2-y1)) + ((-y2)*(x2-x1)))%Q;
        [ ring_simplify; apply Qle_refl |].
      apply Qle_trans with (q*γ + q*γ)%Q;
        [ | ring_simplify; apply Qle_refl ].
      apply Qplus_le_compat.  
      * apply Qmult_le_compat; intuition.
        ** apply Qle_trans with (Qabs m2).
           *** apply Qle_trans with x2; auto.
               rewrite Qabs_pos; auto.
               apply Qle_trans with x2; auto.
               apply Qle_trans with x1; intuition.
           *** unfold q.
               eapply Qle_trans; [| apply Q.le_max_r ].
               eapply Qle_trans; [| apply Q.le_max_r ].
               apply Q.le_max_l.
        ** rewrite <- (Qplus_le_l _ _ y1). ring_simplify. auto.
      * apply Qmult_le_compat; intuition.
        ** rewrite <- (Qplus_le_l _ _ y2). ring_simplify. intuition.
        ** apply Qle_trans with (Qabs n1).
           *** rewrite Qabs_neg.
               **** rewrite <- (Qplus_le_l _ _ y2).
                    rewrite <- (Qplus_le_l _ _ n1).
                    ring_simplify.
                    apply Qle_trans with y1; auto.
               **** apply Qle_trans with y1; auto.
                    apply Qle_trans with y2; intuition.
           *** unfold q.
               eapply Qle_trans; [| apply Q.le_max_r ].
               eapply Qle_trans; [| apply Q.le_max_r ].
               eapply Qle_trans; [| apply Q.le_max_r ].
               apply Q.le_max_l.
        ** rewrite <- (Qplus_le_l _ _ x1). ring_simplify. auto.

    + simpl; intros.
      set (q := Qmax 1
            (Qmax (Qabs m1)
               (Qmax (Qabs m2)
                  (Qmax (Qabs n1) (Qabs n2))))).
      rewrite H. rewrite H0.
      apply Q.max_case_strong; intros.
      * rewrite <- H8; auto.
      * apply Q.min_case_strong; intros.
        ** rewrite <- H9; auto.
        ** rewrite <- (Qplus_le_l _ _ (-(x1*y1))).
           rewrite <- (Qplus_le_l _ _ ((x1*y2))). ring_simplify.
           apply Qle_trans with (0+0+0)%Q;
             [ compute; discriminate |].
           apply Qplus_le_compat.
           *** apply Qplus_le_compat.
               **** apply (Qmult_le_compat 0 0).
                    ***** split; intuition.
                    rewrite <- (Qplus_le_l _ _ y1). ring_simplify. auto.
                    ***** split; [ apply Qle_refl |].
                          intuition.
               **** apply (Qmult_le_compat 0 0); intuition.
           *** apply (Qmult_le_compat 0 0).
               **** split; [ apply Qle_refl |].
                    apply (Qmult_le_compat 0 0).
                    ***** split; compute; discriminate.
                    ***** split; auto.
                          ****** compute; discriminate.
                          ****** apply Qle_trans with 1%Q.
                                 ******* compute. discriminate.
                                 ******* unfold q. apply Q.le_max_l.
               **** split; [ apply Qle_refl |].
                    intuition.
  
        ** rewrite <- (Qplus_le_l _ _ (-(x1*y1))).
           rewrite <- (Qplus_le_l _ _ ((x2*y1))). ring_simplify.
           apply Qle_trans with (0+0+0)%Q; [ compute; discriminate |].
           apply Qplus_le_compat.
           *** apply Qplus_le_compat.
               **** apply (Qmult_le_compat 0 0).
                    ***** split; intuition.
                          rewrite <- (Qplus_le_l _ _ x1). ring_simplify. auto.
                    ***** split; [ apply Qle_refl |].
                          intuition.
               **** apply (Qmult_le_compat 0 0); intuition.
           *** apply (Qmult_le_compat 0 0).
               **** split; [ apply Qle_refl |].
                    apply (Qmult_le_compat 0 0).
                    ***** split; compute; discriminate.
                    ***** split; [ compute; discriminate |].
                    apply Qle_trans with 1%Q; [ compute; discriminate |].
                    unfold q. apply Q.le_max_l.
               **** split; [ apply Qle_refl |].
                    intuition.

      * apply Q.min_case_strong; intros.
        ** rewrite <- H9; auto.
        ** rewrite <- (Qplus_le_l _ _ (-(x2*y2))).
           rewrite <- (Qplus_le_l _ _ ((x1*y2))). ring_simplify.
           apply Qle_trans with (0+0+0)%Q; [ compute; discriminate |].
           apply Qplus_le_compat.
           *** apply Qplus_le_compat.
               **** apply (Qmult_le_compat'' 0 0).
                    ***** split; intuition.
                          rewrite <- (Qplus_le_l _ _ x2). ring_simplify. auto.
                    ***** intuition.
               **** apply (Qmult_le_compat'' 0 0); intuition.
           *** apply (Qmult_le_compat 0 0).
               **** split; [ apply Qle_refl |].
                    apply (Qmult_le_compat 0 0).
                    ***** split; compute; discriminate.
                    ***** split; [ compute; discriminate |].
                          apply Qle_trans with 1%Q; [ compute; discriminate |].
                          unfold q. apply Q.le_max_l.
               **** split; [ apply Qle_refl |].
                    intuition.
  
        ** rewrite <- (Qplus_le_l _ _ (-(x2*y2))).
           rewrite <- (Qplus_le_l _ _ ((x2*y1))). ring_simplify.
           apply Qle_trans with (0+0+0)%Q; [ compute; discriminate |].
           apply Qplus_le_compat; [ apply Qplus_le_compat; [ apply (Qmult_le_compat'' 0 0) |] |].
           *** split; intuition.
               rewrite <- (Qplus_le_l _ _ y2). ring_simplify. auto.
           *** intuition.
           *** apply (Qmult_le_compat'' 0 0); intuition.
           *** apply (Qmult_le_compat 0 0).
               **** split; [ apply Qle_refl |].
                    apply (Qmult_le_compat 0 0).
                    ***** split; compute; discriminate.
                    ***** split; [ compute; discriminate |].
                          apply Qle_trans with 1%Q; [ compute; discriminate |].
                          unfold q. apply Q.le_max_l.
               **** split; [ apply Qle_refl |].
                    intuition.
Qed.

(** Recripricol operation *)

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
  - simpl. intuition.
    apply eprod_elem.
    split.
    + destruct (rint_enum_complete x) as [n [x' [??]]].
      exists n. rewrite H0. auto.
    + destruct (rint_enum_complete y) as [n [y' [??]]].
      exists n. rewrite H0. auto.
  - unfold rint_recip. simpl; intuition.
    destruct (H0 a0) as [q [??]]; auto.
    + destruct H as [[??][??]]. simpl in *.
      apply H. auto.
    + exists q. split; auto.
      destruct H as [[??][??]]. simpl in *.
      apply rint_ord_test in H6.
      destruct H6.
      destruct H2; split.
      apply Qle_trans with (rint_start b); auto.
      apply Qle_trans with (rint_end b); auto.
Qed.

Program Definition real_recip : PreRealDom → PreRealDom :=
  PLT.Hom _ PreRealDom PreRealDom real_recip_rel _ _ .
Next Obligation.
  intros.
  rewrite real_recip_rel_elem in H1.
  rewrite real_recip_rel_elem.
  red; intros.
  destruct (H1 a) as [q [??]].
  - apply H. auto.
  - exists q; split; auto.
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
  - split; auto.
    + apply Qle_refl.
    + apply rint_proper.
  - destruct (H0 (rint_start x)) as [q2 [??]].
    + split; auto.
      * apply Qle_refl.
      * apply rint_proper.
    + assert (q1 == q2).
      { assert (~ rint_start x == 0).
        { intro.
          rewrite H5 in H2.
          ring_simplify in H2.
          compute in H2. discriminate.
        } 
        apply Qeq_trans with (1 / rint_start x).
        - apply Qmult_inj_r with (rint_start x); auto.
          field_simplify; auto.
          rewrite Qmult_comm in H2.
          field_simplify in H2.
          field_simplify in H2.
          auto.
        - apply Qmult_inj_r with (rint_start x); auto.
          field_simplify; auto.
          field_simplify in H4.
          field_simplify in H4.
          apply Qeq_sym. auto.
      } 
      assert (Qmax (rint_start x0) (rint_start y) <=
              Qmin (rint_end x0) (rint_end y)).
      { apply Qle_trans with q1.
        apply Q.max_case.
        - intros. rewrite <- H6; auto.
        - destruct H1; intuition.
        - rewrite H5.
          destruct H3; intuition.
        - apply Q.min_case.
          + intros. rewrite <- H6; auto.
          + destruct H1; intuition.
          + rewrite H5.
            destruct H3; intuition.
      } 
      exists (RatInt _ _ H6).
      split.
      * apply rint_ord_test.
        split; simpl.
        ** apply Q.le_max_l.
        ** apply Q.le_min_l.
      * split.
        ** apply rint_ord_test.
           split; simpl.
           *** apply Q.le_max_r.
           *** apply Q.le_min_r.
        ** rewrite erel_image_elem.
           apply real_recip_rel_elem.
           red. simpl; intros.
           clear q1 H1 H2 q2 H3 H4 H5.
  
           destruct (H a) as [q1 [??]]; auto.
           destruct (H0 a) as [q2 [??]]; auto.
           assert (q1 == q2).
           { assert (~ a == 0).
             { intro.
               rewrite H5 in H2.
               ring_simplify in H2.
               compute in H2. discriminate.
             } 
             apply Qeq_trans with (1 / a).
             - apply Qmult_inj_r with a; auto.
               field_simplify; auto.
               rewrite Qmult_comm in H2.
               field_simplify in H2.
               field_simplify in H2.
               auto.
             - apply Qmult_inj_r with a; auto.
               field_simplify; auto.
               field_simplify in H4.
               field_simplify in H4.
               apply Qeq_sym. auto.
           } 
           exists q1.
           split; auto.
           split; simpl; auto.
           *** apply Q.max_case.
               **** intros. rewrite <- H8; auto.
               **** destruct H1; auto.
               **** rewrite H5. destruct H3; auto.
           *** apply Q.min_case.
               **** intros. rewrite <- H8; auto.
               **** destruct H1; auto.
               **** rewrite H5.
                    destruct H3; auto.
Qed.

Lemma real_recip_opp :
  real_recip ∘ real_opp ≈ real_opp ∘ real_recip.
Proof.
  split; hnf; intros [a r] H.
  - apply PLT.compose_hom_rel in H. destruct H as [y [??]].
    simpl in *.
    apply real_opp_rel_elem in H.
    apply real_recip_rel_elem in H0.
    apply PLT.compose_hom_rel.
    exists (rint_opp r). split; simpl.
    + apply real_recip_rel_elem.
      red; intros.
      destruct (H0 (-a0)) as [q [??]].
      * apply H.
        apply rint_opp_correct. auto.
      * exists (-q). split.
        ** apply rint_opp_correct. auto.
        ** rewrite <- H3. ring.
    + apply real_opp_rel_elem.
      apply rint_ord_test. simpl.
      do 2 rewrite Qopp_involutive. split; apply Qle_refl.
  
  - apply PLT.compose_hom_rel in H. destruct H as [y [??]].
    simpl in *.
    apply real_opp_rel_elem in H0.
    apply real_recip_rel_elem in H.
    apply PLT.compose_hom_rel.
    exists (rint_opp a). split; simpl.
    + apply real_opp_rel_elem. auto.
    + apply real_recip_rel_elem.
      red; intros.
      destruct (H (-a0)) as [q [??]].
      * apply rint_opp_correct. 
        red. rewrite Qopp_involutive. auto.
      * hnf in H0.
        exists (-q). split.
        ** apply H0.
           apply rint_opp_correct. auto.
        ** rewrite <- H3. ring.
Qed.  


Lemma real_recip_canonical A (f: A → PreRealDom) :
  canonical A f ->
  canonical A (real_recip ∘ f).
Proof.
  repeat intro.
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [r [??]].
  simpl in H1. apply real_recip_rel_elem in H1.
  destruct (H a r) as [r' [??]]; auto.
  hnf in H1.
  destruct (H1 (rint_start r)) as [q0 [??]].
  - split.
    + apply Qle_refl.
    + apply rint_proper.
  - destruct (H1 (rint_start r')) as [q1 [??]].
    + destruct H3.
      red; intuition.
      apply Qle_trans with (rint_end r'); intuition.
      apply rint_proper.
    + destruct (H1 (rint_end r')) as [q2 [??]].
      * destruct H3.
        red; intuition.
        apply Qle_trans with (rint_start r'); intuition.
        apply rint_proper.
      * destruct (H1 (rint_end r)) as [q3 [??]].
        ** split; [ apply rint_proper | apply Qle_refl ].

        ** assert (Hr0 : ~in_interval 0 r).
           { intro. destruct (H1 0%Q) as [?[??]]; auto.
             ring_simplify in H14. compute in H14. discriminate.
           } 
           destruct (Qlt_le_dec 0 (rint_start r)).
  
           *** assert (0 < q2 /\ q2 <= q1).
               { destruct H3.
                 destruct (recip_find_interior (rint_start r') (rint_end r') (rint_start r') q1 q2); 
                   intuition.
                 - apply Qlt_le_trans with (rint_start r); intuition.
                 - apply rint_proper.
                 - apply Qle_trans with x0; auto.
               }
               destruct H12.
               exists (RatInt q2 q1 H13).
               split. 
               **** apply PLT.compose_hom_rel.
                    exists r'. split; auto.
                    simpl. apply real_recip_rel_elem.
                    hnf. simpl; intros.
                    destruct H14.
                    destruct (recip_find_interior (rint_start r') (rint_end r') a0 q1 q2)
                      as [y [?[?[??]]]]; auto.
                    destruct H3. apply Qlt_le_trans with (rint_start r); intuition.
                    exists y; split; auto.
                    split; simpl; auto.

               **** split; simpl.
                    ***** destruct H10.
                          apply Qle_lt_trans with q3; auto.
                          apply (Qmult_lt_l _ _ (rint_end r)).
                          ****** apply Qlt_le_trans with (rint_start r); auto.
                                 apply rint_proper.
                          ****** rewrite H11. rewrite <- H9.
                                 destruct H3.
                                 apply (Qmult_lt_r _ _ q2); auto.
                    ***** destruct H4.
                          apply Qlt_le_trans with q0; auto.
                          apply (Qmult_lt_l _ _ (rint_start r')).
                          ****** destruct H3.
                                 apply Qlt_le_trans with (rint_start r); intuition.
                          ****** rewrite H7. rewrite <- H5.
                                 destruct H3.
                                 apply (Qmult_lt_r _ _ q0); auto.
                                 apply (Qmult_lt_l _ _ (rint_start r)); auto.
                                 ring_simplify. rewrite H5. compute. auto.

           *** assert (Hr : rint_end r < 0).
               { destruct (Qlt_le_dec (rint_end r) 0); auto.
                 elim Hr0. split; auto.
               } 

               assert (q2 <= q1 /\ q1 < 0).
               { destruct H3.
                 destruct (recip_find_interior' (rint_start r') (rint_end r') (rint_start r') q1 q2); 
      intuition.
                 - apply rint_proper.
                 - apply Qlt_le_trans with (rint_end r); intuition.
                 - apply Qle_trans with x0; auto.
               } 

               destruct H12.
               exists (RatInt q2 q1 H12).
               split. 
               **** apply PLT.compose_hom_rel.
                    exists r'. split; auto.
                    simpl. apply real_recip_rel_elem.
                    hnf. simpl; intros.
                    destruct H14.
                    destruct (recip_find_interior' (rint_start r') (rint_end r') a0 q1 q2)
                      as [y [?[?[??]]]]; auto.
                    ***** destruct H3. apply Qlt_le_trans with (rint_end r); intuition.
                    ***** exists y; split; auto.
                          split; simpl; auto.

               **** split; simpl.
                    ***** destruct H10.
                          apply Qle_lt_trans with q3; auto.
                          apply (Qmult_lt_l _ _ (-rint_end r)).
                          ******* rewrite <- (Qplus_lt_l _ _ (rint_end r)). ring_simplify. auto.
                          ******* ring_simplify.
                                  rewrite <- (Qmult_assoc).
                                  rewrite H11.
                                  rewrite <- H9.
                                  cut (rint_end r' * (-q2) < rint_end r * (-q2)).
                                  { intro. ring_simplify in H15. ring_simplify. auto. }
                                  apply (Qmult_lt_r _ _ (-q2)).
                                  rewrite <- (Qplus_lt_l _ _ q2). ring_simplify.
                                  apply Qle_lt_trans with q1; auto.
                                  destruct H3; auto.
  
                    ***** destruct H4.
                          apply Qlt_le_trans with q0; auto.
                          apply (Qmult_lt_l _ _ (-rint_start r')).
                          rewrite <- (Qplus_lt_l _ _ (rint_start r')). ring_simplify.
                          apply Qle_lt_trans with (rint_end r); auto.
                          destruct H3.
                          apply Qle_trans with (rint_end r'); intuition.
                          apply rint_proper.
                          ring_simplify.
                          rewrite <- (Qmult_assoc).
                          rewrite H7.
                          rewrite <- H5.
                          cut (rint_start r * (-q0) < rint_start r' * (-q0)).
                          { intro. ring_simplify in H15. ring_simplify. auto. }
                          apply (Qmult_lt_r _ _ (-q0)).
                          ****** apply (Qmult_lt_l _ _ (-rint_start r)).
                                 rewrite <- (Qplus_lt_l _ _ (rint_start r)). ring_simplify.
                                 apply Qle_lt_trans with (rint_end r); auto.
                                 ******* apply rint_proper.
                                 ******* ring_simplify. rewrite H5. compute; auto.
                          ****** destruct H3; auto.
Qed.


Lemma real_recip_pos_converges A (f: A → PreRealDom) :
  realdom_lt A (injq 0 ∘ PLT.terminate _ A) f ->
  realdom_converges A f ->
  realdom_converges A (real_recip ∘ f).
Proof.
  repeat intro.
  destruct (H a) as [q0 [q [?[??]]]].
  apply PLT.compose_hom_rel in H2.
  destruct H2 as [[] [??]].
  simpl in H5. apply injq_rel_elem in H5.
  destruct H5.
  assert (0 < rint_start q).
  { apply Qlt_trans with (rint_end q0); auto. }
  clear q0 H2 H5 H6 H4 H.
  set (γ := ((rint_start q)^2 * ε)).
  assert (0 < γ).
  { unfold γ.
    apply Qmult_lt0; auto.
    simpl. apply Qmult_lt0; auto.
  } 
  destruct (H0 a γ) as [r [??]]; auto.
  destruct (plt_hom_directed2 _ _ _ f a q r) as [r' [?[??]]]; auto.
  assert (0 < rint_start r').
  { apply rint_ord_test in H6.
    destruct H6.
    apply Qlt_le_trans with (rint_start q); auto.
  } 
  assert (0 < rint_end r').
  { apply Qlt_le_trans with (rint_start r'); auto. apply rint_proper. }
  assert (1 / rint_end r' <= 1 / rint_start r').  
  { apply (Qmult_le_l _ _ (rint_start r')); auto.
    apply (Qmult_le_l _ _ (rint_end r')); auto.
    field_simplify.
    - generalize (rint_proper r'). intro.
      field_simplify in H11. auto.
    - intro. rewrite H11 in H9.
      apply (Qlt_irrefl 0); auto.
    - intro. rewrite H11 in H10.
      apply (Qlt_irrefl 0); auto.
  } 
  exists (RatInt (1/rint_end r') (1/rint_start r') H11).
  split.
  - apply PLT.compose_hom_rel. exists r'. split; auto.
    simpl. apply real_recip_rel_elem.
    red; simpl; intros.
    destruct (recip_find_interior (rint_start r') (rint_end r') a0
              (1/rint_start r') (1/rint_end r')) as [y [?[?[??]]]]; auto.  
    + field_simplify.
      * field_simplify. reflexivity.
      * intro. rewrite H13 in H9. apply (Qlt_irrefl 0); auto.
    + field_simplify.
      * field_simplify. reflexivity.
      * intro. rewrite H13 in H10. apply (Qlt_irrefl 0); auto.
    + destruct H12; auto.
    + destruct H12; auto.
    + exists y; split; auto.
      split; simpl; auto.
  - simpl.
    apply (Qmult_le_l _ _ (rint_start r')); auto.
    apply (Qmult_le_l _ _ (rint_end r')); auto.
    field_simplify.
    + apply Qle_trans with (rint_end r' - rint_start r'); auto.
      field_simplify. apply Qle_refl.
      apply Qle_trans with (rint_end r - rint_start r); auto.
      * apply (Qplus_le_l _ _ (rint_start r)).
        apply (Qplus_le_l _ _ (rint_start r')).
        ring_simplify.
        rewrite (Qplus_comm _ (rint_start r)).
        apply rint_ord_test in H8. destruct H8.
        apply Qplus_le_compat; auto.
      * apply Qle_trans with γ; auto.
        apply Qle_trans with ((rint_end r' * rint_start r') * ε); auto.
        ** unfold γ.
           apply Qmult_le_compat; split; intuition.
           *** simpl.
               apply (Qmult_le_compat 0 0); intuition.
           *** simpl.
               apply rint_ord_test in H6. destruct H6.
               apply Qmult_le_compat; split; intuition.
               apply Qle_trans with (rint_start r'); auto.
               apply rint_proper.
        ** field_simplify.
           field_simplify. apply Qle_refl.
    + split.
      * intro.
        rewrite H12 in H10. apply (Qlt_irrefl 0). auto.
      * intro.
        rewrite H12 in H9. apply (Qlt_irrefl 0). auto.
Qed.


Lemma real_recip_neg_converges A (f: A → PreRealDom) :
  realdom_lt A f (injq 0 ∘ PLT.terminate _ A) ->
  realdom_converges A f ->
  realdom_converges A (real_recip ∘ f).
Proof.
  intros.
  assert (realdom_converges A (real_opp ∘ (real_recip ∘ (real_opp ∘ f)))).
  { apply real_opp_converges.
    apply real_recip_pos_converges.
    - apply realdom_lt0_opp. auto.
    - apply real_opp_converges; auto.
  } 
  revert H1. apply realdom_converges_le.
  rewrite (cat_assoc ∂PLT).
  rewrite <- real_recip_opp.
  rewrite <- (cat_assoc ∂PLT).
  rewrite (cat_assoc ∂PLT _ _ _ _ real_opp).
  rewrite real_opp_inv.
  rewrite (cat_ident2 ∂PLT). auto.
Qed.



(** Addition is a commutative group *)
Lemma real_plus_comm_le A (g h:A → PreRealDom) :
  real_plus ∘ 《 g, h 》%plt ≤ real_plus ∘ 《 h, g 》%plt.
Proof.
  red; intros [x y] H.
  apply PLT.compose_hom_rel in H. apply PLT.compose_hom_rel.
  destruct H as [[a b] [??]].
  rewrite (PLT.pair_hom_rel _ _ _ _ g h) in H. destruct H.
  exists (b,a). split.
  - apply PLT.pair_hom_rel. split; auto.
  - simpl in *. apply real_plus_rel_elem in H0. apply real_plus_rel_elem.
    rewrite H0.
    apply rint_ord_test. simpl; split.
    + rewrite Qplus_comm; apply Qle_refl.
    + rewrite Qplus_comm; apply Qle_refl.
Qed.

Lemma real_plus_comm A (g h:A → PreRealDom) :
  real_plus ∘ 《 g, h 》%plt ≈ real_plus ∘ 《 h, g 》%plt.
Proof.
  split; apply real_plus_comm_le; auto.
Qed.

Lemma real_plus_assoc A (f g h:A → PreRealDom) :
  (real_plus ∘ 《 f, real_plus ∘ 《 g, h 》 》 ≈
   real_plus ∘ 《 real_plus ∘ 《 f, g 》, h 》)%plt.
Proof.
  split; intros [x y] H.  
  - apply PLT.compose_hom_rel in H. apply PLT.compose_hom_rel.
    destruct H as [[a b] [??]].
    rewrite (PLT.pair_hom_rel _ _ _ _ f (real_plus ∘ 《g,h》%plt)) in H. destruct H.
    apply PLT.compose_hom_rel in H1.
    destruct H1 as [[c d] [??]].
    rewrite (PLT.pair_hom_rel _ _ _ _ g h) in H1. destruct H1.
    exists (rint_plus a c,d).
    split.
    + apply PLT.pair_hom_rel.
      split; auto.
      apply PLT.compose_hom_rel.
      exists (a,c). split.
      * apply PLT.pair_hom_rel. split; auto.
      * simpl. apply real_plus_rel_elem. auto.
    + simpl. apply real_plus_rel_elem. 
      apply real_plus_rel_elem in H0. rewrite H0.
      apply real_plus_rel_elem in H2. 
      apply rint_ord_test in H2.
      simpl in H2. destruct H2.
      apply rint_ord_test.
      split; simpl.
      * rewrite <- Qplus_assoc.
        apply Qplus_le_compat.
        ** apply Qle_refl.
        ** auto.
      * rewrite <- Qplus_assoc.
        apply Qplus_le_compat.
        ** apply Qle_refl.
        ** auto.
  
  - apply PLT.compose_hom_rel in H.  
    destruct H as [[a b][??]].
    apply (PLT.pair_hom_rel _ _ _ _ (real_plus ∘ 《f, g》%plt) h) in H.
    destruct H.
    apply PLT.compose_hom_rel in H.  
    destruct H as [[c d][??]].
    apply PLT.compose_hom_rel.
    apply (PLT.pair_hom_rel _ _ _ _ f g) in H. destruct H.
    exists (c, rint_plus d b).
    split.
    + apply PLT.pair_hom_rel. split; auto.
      apply PLT.compose_hom_rel.
      exists (d,b). split.
      * apply PLT.pair_hom_rel. split; auto.
      * simpl. apply real_plus_rel_elem. auto.
    + apply real_plus_rel_elem.
      apply real_plus_rel_elem in H0.
      apply real_plus_rel_elem in H2.
      apply rint_ord_test in H2.
      rewrite H0.
      apply rint_ord_test. unfold rint_plus; simpl.
      do 2 rewrite Qplus_assoc.
      split.
      * apply Qplus_le_compat.
        ** simpl in H2; destruct H2; auto.
        ** apply Qle_refl.
      * apply Qplus_le_compat.
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
  - destruct H2; split.
    + apply Qlt_le_weak; auto.
    + apply Qlt_le_weak; auto.
  - ring.
Qed.

Lemma real_plus_0_eq A (h: A → PreRealDom) :
  canonical A h ->
  real_plus ∘ 《 h, injq 0 ∘ PLT.terminate true A 》%plt ≈ h.
Proof.
  intros. split; [ apply real_plus_0_le |].
  hnf; intros. destruct a as [a x].
  apply PLT.compose_hom_rel.
  destruct (H a x) as [x' [??]]; auto.
  set (q1 := rint_start x - rint_start x').
  set (q2 := rint_end x - rint_end x').
  destruct H2.
  assert ( q1 < 0 ).
  { unfold q1.
    rewrite <- (Qplus_lt_l _ _ (rint_start x')).
    ring_simplify. auto.
  } 
  assert( 0 < q2 ).
  { unfold q2.
    rewrite <- (Qplus_lt_l _ _ (rint_end x')).
    ring_simplify. auto.
  } 
  assert (q1 <= q2).
  { apply Qlt_le_weak.
    apply Qlt_trans with 0%Q; auto.
  } 
  exists (x', RatInt q1 q2 H6).
  simpl; split.
  - apply PLT.pair_hom_rel. split; auto.
    apply PLT.compose_hom_rel.
    exists tt. split; auto.
    + simpl. apply eprod_elem.
      split.
      * apply eff_complete.
      * apply single_axiom. auto.
    + simpl. apply injq_rel_elem.
      split; simpl; auto.
  - apply real_plus_rel_elem.
    apply rint_ord_test; split; simpl; auto.
    + unfold q1. ring_simplify. apply Qle_refl.
    + unfold q2. ring_simplify. apply Qle_refl.
Qed.

Lemma real_opp_0_le A (h : A → PreRealDom) 
  (Hh : canonical A h) :
  real_plus ∘ 《 h, real_opp ∘ h 》%plt ≤ injq 0 ∘ PLT.terminate true A.
Proof.
  intros [??] ?.
  apply PLT.compose_hom_rel in H.
  apply PLT.compose_hom_rel.
  exists tt. split; simpl.
  - apply eprod_elem. split.
    + apply eff_complete.
    + apply single_axiom. auto.
  - destruct H as [[a b][??]].
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
    + exists a. apply cons_elem; auto.
    + red; intros. apply erel_image_elem.
      apply cons_elem in H4. destruct H4.
      * apply PLT.hom_order with c a; auto.
      * apply cons_elem in H4. destruct H4.
        ** apply PLT.hom_order with c q; auto.
        ** apply nil_elem in H4. elim H4.
    + apply erel_image_elem in H5.
      assert (a ≤ z).
      { apply H4. apply cons_elem; auto. }
      assert (q ≤ z).
      { apply H4. apply cons_elem. right. apply cons_elem; auto. }
      apply rint_ord_test in H6.
      apply rint_ord_test in H7.
      destruct H6. destruct H7.
      apply rint_ord_test in H0. simpl in H0.
      destruct H0.
      destruct (Hh c z) as [z' [??]]; auto.
      destruct H12.
      split.
      * eapply Qle_lt_trans; [ apply H0 |].
        rewrite <- (Qplus_lt_l _ _ (- rint_start b)).
        ring_simplify.
        apply Qle_lt_trans with (rint_start z); auto.
        apply Qlt_le_trans with (rint_start z'); auto.
        rewrite <- (Qplus_le_l _ _ (rint_start b)).
        ring_simplify.
        eapply Qle_trans.
        ** apply (Qplus_le_r). apply H2.
        ** rewrite <- (Qplus_le_l _ _ (rint_end q)).
           ring_simplify.
           apply Qle_trans with (rint_end z').
           *** apply rint_proper.
           *** apply Qle_trans with (rint_end z); auto.
               apply Qlt_le_weak; auto.
  
      * eapply Qlt_le_trans; [ | apply H10 ].
        rewrite <- (Qplus_lt_l _ _ (- rint_end a)).
        ring_simplify.
        apply Qlt_le_trans with (- rint_start q); auto.
        cut (- rint_end a < -rint_start q).
        { intros.
          ring_simplify.
          ring_simplify in H14. auto.
        }
        rewrite <- (Qplus_lt_l _ _ (rint_end a)).
        rewrite <- (Qplus_lt_l _ _ (rint_start q)).
        ring_simplify.
        apply Qle_lt_trans with (rint_start z); auto.
        apply Qlt_le_trans with (rint_start z'); auto.
        apply Qle_trans with (rint_end z'); auto.
        ** apply rint_proper.
        ** apply Qle_trans with (rint_end z); auto.
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
  { unfold ε.
    simpl in H0. apply injq_rel_elem in H0. destruct H0.
    apply Q.min_case_strong; intros.
    - rewrite <- H2; auto.
    - rewrite <- (Qplus_lt_l _ _ (rint_start x)). ring_simplify. auto.
    - auto.
  } 
  destruct (Hh a ε) as [z [??]]; auto.
  apply PLT.compose_hom_rel.
  exists (z, rint_opp z).
  split.
  - apply PLT.pair_hom_rel.
    split; auto.
    apply PLT.compose_hom_rel.
    exists z. split; auto.
    simpl. apply real_opp_rel_elem.
    auto.
  - simpl. apply real_plus_rel_elem.
    apply rint_ord_test.
    simpl.
    split.
    + rewrite <- (Qplus_le_l _ _ (rint_end z - rint_start z)).
      rewrite <- (Qplus_le_l _ _ (- rint_start x)).
      ring_simplify.
      ring_simplify in H2.
      eapply Qle_trans; [ apply H2 |].
      unfold ε.
      apply Q.le_min_l.
    + eapply Qle_trans; [ apply H2 |].
      unfold ε.
      apply Q.le_min_r.
Qed.

Lemma real_opp_0_eq A (h : A → PreRealDom) :
  canonical A h ->
  realdom_converges A h ->
  real_plus ∘ 《 h, real_opp ∘ h 》%plt ≈ injq 0 ∘ PLT.terminate true A.
Proof.
  intros; split.
  - apply real_opp_0_le; auto.
  - apply real_opp_0_le2; auto.
Qed.

(** Addition reflects the strict order *)
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
  apply Qplus_le_compat; [ apply Qle_refl |].
  destruct (PLT.hom_directed _ _ _ h a (m::n::nil)%list) as [z [??]].
  - exists m. apply cons_elem; auto.
  - red; intros ? HIN.
    apply erel_image_elem.
    apply cons_elem in HIN. destruct HIN as [HIN|HIN].
    + apply PLT.hom_order with a m; auto.
    + apply cons_elem in HIN. destruct HIN as [HIN|HIN].
      * apply PLT.hom_order with a n; auto.
      * apply nil_elem in HIN; elim HIN.
  - apply erel_image_elem in H10.
    assert (m ≤ z).
    { apply H9. apply cons_elem. auto. }
    assert (n ≤ z).
    { apply H9. apply cons_elem. right. apply cons_elem. auto. }
    apply rint_ord_test in H11.
    apply rint_ord_test in H12.
    intuition.
    apply Qle_trans with (rint_start z); auto.
    apply Qle_trans with (rint_end z); auto.
    apply rint_proper.
Qed.


(** Multiplication is a commutative monoid with unit 1 *)

Lemma real_mult_comm_le A (g h:A → PreRealDom) :
  real_mult ∘ 《 g, h 》%plt ≤ real_mult ∘ 《 h, g 》%plt.
Proof.
  red; intros [x y] H.
  apply PLT.compose_hom_rel in H. apply PLT.compose_hom_rel.
  destruct H as [[a b] [??]].
  rewrite (PLT.pair_hom_rel _ _ _ _ g h) in H. destruct H.
  exists (b,a). split.
  - apply PLT.pair_hom_rel. split; auto.
  - simpl in *. apply real_mult_rel_elem in H0. apply real_mult_rel_elem.
    rewrite H0.
    hnf; intros.
    apply rint_mult_swap. auto.
Qed.

Lemma real_mult_comm A (g h:A → PreRealDom) :
  real_mult ∘ 《 g, h 》%plt ≈ real_mult  ∘ 《 h, g 》%plt.
Proof.
  split; apply real_mult_comm_le; auto.
Qed.


Lemma real_mult_assoc A (f g h:A → PreRealDom) :
  (real_mult ∘ 《 f, real_mult ∘ 《 g, h 》 》 ≈
   real_mult ∘ 《 real_mult ∘ 《 f, g 》, h 》)%plt.
Proof.
  split; intros [x y] H.  
  - apply PLT.compose_hom_rel in H. apply PLT.compose_hom_rel.
    destruct H as [[a b] [??]].
    rewrite (PLT.pair_hom_rel _ _ _ _ f (real_mult ∘ 《g,h》%plt)) in H. destruct H.
    apply PLT.compose_hom_rel in H1.
    destruct H1 as [[c d] [??]].
    rewrite (PLT.pair_hom_rel _ _ _ _ g h) in H1. destruct H1.
    exists (rint_mult a c,d).
    split.
    + apply PLT.pair_hom_rel.
      split; auto.
      apply PLT.compose_hom_rel.
      exists (a,c). split.
      * apply PLT.pair_hom_rel. split; auto.
      * simpl. apply real_mult_rel_elem. auto.
    + simpl. apply real_mult_rel_elem. 
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
      * apply H2.
        apply rint_mult_correct.
        exists q4. exists q2.
        intuition.
      * rewrite H6.
        rewrite H8.
        symmetry. apply Qmult_assoc.

  - apply PLT.compose_hom_rel in H.  
    destruct H as [[a b][??]].
    apply (PLT.pair_hom_rel _ _ _ _ (real_mult ∘ 《f, g》%plt) h) in H.
    destruct H.
    apply PLT.compose_hom_rel in H.  
    destruct H as [[c d][??]].
    apply PLT.compose_hom_rel.
    apply (PLT.pair_hom_rel _ _ _ _ f g) in H. destruct H.
    exists (c, rint_mult d b).
    split.
    + apply PLT.pair_hom_rel. split; auto.
      apply PLT.compose_hom_rel.
      exists (d,b). split.
      * apply PLT.pair_hom_rel. split; auto.
      * simpl. apply real_mult_rel_elem. auto.
    + apply real_mult_rel_elem.
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
      * apply H2.
        apply rint_mult_correct.
        exists q1. exists q3. intuition.
      * rewrite H6.
        rewrite H8.
        apply Qmult_assoc.
Qed.


Lemma real_mult_1_le A (f:A → PreRealDom) :
  (real_mult ∘ 《 f, injq 1 ∘ PLT.terminate true A 》 ≤ f)%plt.
Proof.
  intros [a r] H.
  apply PLT.compose_hom_rel in H.
  destruct H as [[s t] [H H0]].
  apply (PLT.pair_hom_rel _ _ _ _ f (injq 1 ∘ PLT.terminate true A))in H.
  destruct H as [H H1].
  simpl in H0. apply real_mult_rel_elem in H0.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [[] [H1 H2]].
  simpl in H2. apply injq_rel_elem in H2.
  red in H2.
  apply PLT.hom_order with a s; auto.
  hnf; intros.
  apply H0.
  apply rint_mult_correct.
  exists q. exists 1%Q.
  split; auto.
  split.
  - red. intuition.
  - ring.
Qed.


(* Wow, why is this proof so damn hard? *)
Lemma real_mult_1_le2 A (f:A → PreRealDom) :
  canonical A f ->
  (real_mult ∘ 《 f, injq 1 ∘ PLT.terminate true A 》 ≥ f)%plt.
Proof.
  intro Hf.
  hnf; simpl; intros [a r] H.
  destruct (Hf a r) as [r' [?[??]]]; auto.

  destruct (Qlt_le_dec 0 (rint_start r')).
  
  - set (q1 := Qmax 0 (rint_start r / rint_start r')).
    set (q2 := rint_end r / rint_end r').
    assert (q1 < 1).
    { unfold q1.
      apply Q.max_case. intros. rewrite <- H3. auto.
      compute. auto.
      apply Qlt_shift_div_r. auto.
      ring_simplify. intuition.
    } 
    assert (1 < q2).
    { unfold q2.
      apply Qlt_shift_div_l.
      apply Qlt_le_trans with (rint_start r'); auto. apply rint_proper.
      ring_simplify. intuition.
    }
    assert (q1 <= q2).
    { apply Qle_trans with 1%Q; intuition. }
    apply PLT.compose_hom_rel.
    exists (r', RatInt q1 q2 H5).
    split.
    + apply PLT.pair_hom_rel. split; auto.
      apply PLT.compose_hom_rel.
      exists tt. split.
      * simpl. apply eprod_elem.
        split.
        ** apply eff_complete.
        ** apply single_axiom. auto.
      * simpl. apply injq_rel_elem.
        split; auto.
    + simpl.
      apply real_mult_rel_elem.
      hnf; intros.
      apply rint_mult_correct in H6.
      destruct H6 as [p1 [p2 [?[??]]]].
      red. rewrite H8.
      destruct H6; destruct H7. simpl in *.
      split.
      * apply Qle_trans with (rint_start r' * q1).
        ** unfold q1.
           apply Q.max_case_strong.
           *** intros.
               rewrite <- H11; auto.
           *** intros.
               rewrite <- (Qmult_le_l _ _ (rint_start r')) in H11; auto.
               rewrite Qmult_div_r in H11; auto.
               intro. rewrite H12 in q. apply (Qlt_irrefl 0); auto.
           *** intros.
               field_simplify.
               **** field_simplify.
                    apply Qle_refl.
               **** intro. rewrite H12 in q. apply (Qlt_irrefl 0); auto.
        ** apply Qmult_le_compat; intuition.
           unfold q1.
           apply Q.le_max_l.
      * apply Qle_trans with (rint_end r' * q2).
        ** apply Qmult_le_compat; intuition.
           *** apply Qle_trans with (rint_start r'); intuition.
           *** apply Qle_trans with q1; intuition.
               unfold q1.
               apply Q.le_max_l.
        ** unfold q2.
           field_simplify.
           *** field_simplify. apply Qle_refl.
           *** intro.
               apply (Qlt_irrefl 0).
               apply Qlt_le_trans with (rint_start r'); auto.
               apply Qle_trans with (rint_end r').
               **** apply rint_proper.
               **** rewrite H11. apply Qle_refl.
  
  - destruct (Qlt_le_dec (rint_end r') 0).
    + set (q1 := Qmax 0 (rint_end r / rint_end r')).
      set (q2 := rint_start r / rint_start r').

      assert (~rint_end r' == 0).
      { intro. apply (Qlt_irrefl 0).
        rewrite H3 in q0. auto.
      } 

      assert (~rint_start r' == 0).
      { intro. apply (Qlt_irrefl 0).
        apply Qle_lt_trans with (rint_end r'); auto.
        apply Qle_trans with (rint_start r'); auto.
        rewrite H4; apply Qle_refl.
        apply rint_proper.
      } 

      assert (q1 < 1).
      { unfold q1.
        apply Q.max_case.
        - intros. rewrite <- H5; auto.
        - compute. auto.
        - apply Qle_lt_trans with ((-rint_end r) / (-rint_end r')). 
          + field_simplify; auto. field_simplify; auto. apply Qle_refl.
          + apply Qlt_shift_div_r. 
            * rewrite <- (Qplus_lt_l _ _ (rint_end r')). ring_simplify. auto.
            * ring_simplify.
              rewrite <- (Qplus_lt_l _ _ (rint_end r')). 
              rewrite <- (Qplus_lt_l _ _ (rint_end r)). 
              ring_simplify. auto.
      }
      assert (1 < q2).
      { unfold q2.
        apply Qlt_le_trans with ((-rint_start r) / (-rint_start r')). 
        - apply Qlt_shift_div_l; auto.
          + rewrite <- (Qplus_lt_l _ _ (rint_start r')). ring_simplify.
            apply Qle_lt_trans with (rint_end r'); auto.
            apply rint_proper.
          + rewrite <- (Qplus_lt_l _ _ (rint_start r')). 
            rewrite <- (Qplus_lt_l _ _ (rint_start r)). 
            ring_simplify. auto.
        - field_simplify; auto. field_simplify; auto. apply Qle_refl.
      } 
      assert (q1 <= q2).
      { apply Qle_trans with 1%Q; intuition. }
      apply PLT.compose_hom_rel.
      exists (r', RatInt q1 q2 H7).
      split.
      * apply PLT.pair_hom_rel. split; auto.
        apply PLT.compose_hom_rel.
        exists tt. split.
        ** simpl. apply eprod_elem. split.
           *** apply eff_complete.
           *** apply single_axiom. auto.
        ** simpl. apply injq_rel_elem.
           split; auto.
      * simpl.
        apply real_mult_rel_elem.
        hnf; intros.
        apply rint_mult_correct in H8.
        destruct H8 as [p1 [p2 [?[??]]]].
        red. rewrite H10.
        destruct H8; destruct H9. simpl in *.
        split.
        ** apply Qle_trans with (rint_start r' * q2).
           *** unfold q2.
               rewrite Qmult_div_r; auto. apply Qle_refl.
           *** rewrite (Qmult_comm (rint_start r')).
               rewrite (Qmult_comm p1).
               apply Qmult_le_compat'; intuition.
               **** apply Qle_trans with q1; auto.
                    unfold q1. apply Q.le_max_l.
               **** apply Qle_trans with (rint_end r'); intuition.
        ** apply Qle_trans with (rint_end r' * q1).
           *** rewrite (Qmult_comm p1).
               rewrite (Qmult_comm (rint_end r')).
               apply Qmult_le_compat'; intuition.
               unfold q1. apply Q.le_max_l.
           *** unfold q1.
               apply Q.max_case_strong; intros.
               **** rewrite <- H13; auto.
               **** ring_simplify.
                    assert ( (- rint_end r) / (- rint_end r') <= 0 ).
                    { field_simplify; auto.
                      field_simplify; auto.
                    } 
                    rewrite <- (Qmult_le_l _ _ (-rint_end r')) in H14.
                    ***** rewrite Qmult_div_r in H14.
                          ****** ring_simplify in H14.
                                 rewrite <- (Qplus_le_l _ _ (-rint_end r)). ring_simplify. auto.
                          ****** intro. apply H3.
                                  rewrite <- (Qopp_involutive (rint_end r')).
                                  rewrite H15. compute. auto.
                    ***** rewrite <- (Qplus_lt_l _ _ (rint_end r')). ring_simplify. auto.
               **** rewrite (Qmult_div_r); auto. apply Qle_refl.
  
    + apply Qle_lteq in q.
      destruct q.
      * assert (~rint_start r' == 0).
        { intro. apply (Qlt_irrefl 0). rewrite H4 in H3. auto. }
        apply Qle_lteq in q0.
        destruct q0.
        ** assert (~rint_end r' == 0).
           { intro. apply (Qlt_irrefl 0). rewrite H6 in H5. auto. }
           set (q1 := 0%Q).
           set (q2 := Qmin (rint_start r / rint_start r') (rint_end r / rint_end r')).

           assert (q1 < 1).
           { unfold q1. compute. auto. }
           assert (1 < q2).
           { unfold q2.
             apply Q.min_case; intros.
             - rewrite <- H8; auto.
             - apply Qlt_le_trans with (-rint_start r / -rint_start r').
               + apply Qlt_shift_div_l.
                 * rewrite <- (Qplus_lt_l _ _ (rint_start r')). ring_simplify. auto.
                 * rewrite <- (Qplus_lt_l _ _ (rint_start r')).
                   rewrite <- (Qplus_lt_l _ _ (rint_start r)).
                   ring_simplify. auto.
               + field_simplify; auto.
                 field_simplify; auto.
                 apply Qle_refl.
             - apply Qlt_shift_div_l; auto.
               ring_simplify. auto.
           } 
           assert (q1 <= q2).
           { apply Qle_trans with 1%Q; intuition. }

           apply PLT.compose_hom_rel.
           exists (r', RatInt q1 q2 H9).
           split.
           *** apply PLT.pair_hom_rel. split; auto.
               apply PLT.compose_hom_rel.
               exists tt. split.
               **** simpl.
                    apply eprod_elem. split.
                    ***** apply eff_complete.
                    ***** apply single_axiom. auto.
               **** simpl. apply injq_rel_elem.
                    split; auto.
           *** simpl.
               apply real_mult_rel_elem.
               hnf; intros.
               apply rint_mult_correct in H10.
               destruct H10 as [p1 [p2 [?[??]]]].
               red. rewrite H12.
               destruct H10; destruct H11. simpl in *.

               destruct (Qlt_le_dec 0 p1).
               **** split.
                    ***** apply Qle_trans with 0%Q.
                          ****** apply Qle_trans with (rint_start r'); intuition.
                          ****** apply (Qmult_le_compat 0 0); intuition.
                    ***** apply Qle_trans with (rint_end r' * q2).
                          ****** apply Qmult_le_compat; intuition.
                          ****** apply Qle_trans with (rint_end r' * (rint_end r / rint_end r')).
                                 ******* apply Qmult_le_compat; intuition.
                                         unfold q2. apply Q.le_min_r.
                                 ******* field_simplify; auto.
                                         field_simplify; auto.
                                         apply Qle_refl.
               **** split.
                    ***** apply Qle_trans with (rint_start r' * q2).
                          ****** apply Qle_trans with (rint_start r' * (rint_start r / rint_start r')).
                                 ******* field_simplify; auto.
                                         field_simplify; auto. apply Qle_refl.
                                 ******* rewrite (Qmult_comm (rint_start r')).
                                         rewrite (Qmult_comm (rint_start r')).
                                         apply Qmult_le_compat'; intuition.
                                         unfold q2. apply Q.le_min_l.
                           ****** rewrite (Qmult_comm (rint_start r')).
                                  rewrite (Qmult_comm p1).
                                  apply Qmult_le_compat'; intuition.
                    ***** apply Qle_trans with 0%Q.
                          rewrite (Qmult_comm p1).
                          apply (Qmult_le_compat' 0 0); intuition.
                          apply Qle_trans with (rint_end r'); intuition.

        ** set (q1 := 0%Q).
           set (q2 := rint_start r / rint_start r').

           assert (q1 < 1).
           { unfold q1. compute. auto. }
           assert (1 < q2).
           { unfold q2.
             apply Qlt_le_trans with (-rint_start r / -rint_start r').
             - apply Qlt_shift_div_l.
               + rewrite <- (Qplus_lt_l _ _ (rint_start r')). ring_simplify. auto.
               + rewrite <- (Qplus_lt_l _ _ (rint_start r')).
                 rewrite <- (Qplus_lt_l _ _ (rint_start r)).
                 ring_simplify. auto.
             - field_simplify; auto.
               field_simplify; auto.
               apply Qle_refl.
           } 
           assert (q1 <= q2).
           { apply Qle_trans with 1%Q; intuition. }

           apply PLT.compose_hom_rel.
           exists (r', RatInt q1 q2 H8).
           split.
          *** apply PLT.pair_hom_rel. split; auto.
              apply PLT.compose_hom_rel.
              exists tt. split.
              **** simpl. apply eprod_elem. split.
                   ***** apply eff_complete.
                   ***** apply single_axiom. auto.
              **** simpl. apply injq_rel_elem.
                   split; auto.
          *** simpl.
              apply real_mult_rel_elem.
              hnf; intros.
              apply rint_mult_correct in H9.
              destruct H9 as [p1 [p2 [?[??]]]].
              red. rewrite H11.
              destruct H9; destruct H10. simpl in *.
              split.
              **** apply Qle_trans with (rint_start r' * q2).
                   ***** unfold q2.
                         field_simplify; auto.
                         field_simplify; auto. apply Qle_refl.
                   ***** rewrite (Qmult_comm (rint_start r')).
                         rewrite (Qmult_comm p1).
                         apply Qmult_le_compat'; intuition.
                         rewrite H5. auto.
              **** apply Qle_trans with (rint_end r' * q1).
                   ***** rewrite (Qmult_comm p1).
                         rewrite (Qmult_comm (rint_end r')).
                         apply Qmult_le_compat'; intuition.
                         rewrite <- H5. apply Qle_refl.
                   ***** rewrite <- H5.
                         ring_simplify.
                         apply Qle_trans with (rint_end r'); intuition.
  
      * apply Qle_lteq in q0.
        destruct q0.
        ** assert (~rint_end r' == 0).
           { intro. apply (Qlt_irrefl 0). rewrite H5 in H4. auto. }
        
           set (q1 := 0%Q).
           set (q2 := rint_end r / rint_end r').

           assert (q1 < 1).
           { unfold q1. compute. auto. }
           assert (1 < q2).
           { unfold q2.
             apply Qlt_shift_div_l; auto.
             ring_simplify. auto.
           } 
           assert (q1 <= q2).
           { apply Qle_trans with 1%Q; intuition. }

           apply PLT.compose_hom_rel.
           exists (r', RatInt q1 q2 H8).
           split.
           *** apply PLT.pair_hom_rel. split; auto.
               apply PLT.compose_hom_rel.
               exists tt. split.
               **** simpl. apply eprod_elem. split.
                    ***** apply eff_complete.
                    ***** apply single_axiom. auto.
               **** simpl. apply injq_rel_elem.
                    split; auto.
           *** simpl.
               apply real_mult_rel_elem.
               hnf; intros.
               apply rint_mult_correct in H9.
               destruct H9 as [p1 [p2 [?[??]]]].
               red. rewrite H11.
               destruct H9; destruct H10. simpl in *.
               split.
               **** apply Qle_trans with (rint_start r' * q2).
                    ***** rewrite H3. ring_simplify.
                          apply Qle_trans with (rint_start r'); intuition.
                    ***** rewrite H3. ring_simplify.
                    apply (Qmult_le_compat 0 0); intuition.
                    rewrite <- H3. auto.
               **** apply Qle_trans with (rint_end r' * q2).
                    ***** apply Qmult_le_compat; intuition.
                          apply Qle_trans with (rint_start r'); intuition.
                          rewrite H3. apply Qle_refl.
                    ***** unfold q2.
                          field_simplify; auto.
                          field_simplify; auto.
                          apply Qle_refl.
  
        ** destruct (Hf a r') as [r'' [??]]; auto.
           destruct H6.
           exfalso. apply (Qlt_irrefl 0).
           apply Qlt_trans with (rint_start r'').
           *** rewrite <- H3; auto.
           *** apply Qle_lt_trans with (rint_end r'').
               **** apply rint_proper.
               **** rewrite H4. auto.
Qed.

Lemma real_mult_1 A (f:A → PreRealDom) :
  canonical A f ->
  (real_mult ∘ 《 f, injq 1 ∘ PLT.terminate true A 》 ≈ f)%plt.
Proof.
  intros. split.
  - apply real_mult_1_le.
  - apply real_mult_1_le2. auto.
Qed.


(** Multiplication reflects the strict order *)
Lemma real_mult_reflects_pos (A:∂PLT) (a:A) (x y z:A → PreRealDom) :
  realdom_lt A (injq 0 ∘ PLT.terminate _ A) z ->
  realdom_lt A
    (real_mult ∘ 《 x, z 》)%plt
    (real_mult ∘ 《 y, z 》)%plt ->
  realdom_lt A x y.
Proof.
  repeat intro.
  destruct (H0 a0) as [p [q [?[??]]]].
  apply PLT.compose_hom_rel in H1.
  apply PLT.compose_hom_rel in H2.
  destruct H1 as [[p1 p2] [??]].
  destruct H2 as [[q1 q2] [??]].
  apply (PLT.pair_hom_rel _ _ _ _ x z) in H1.
  apply (PLT.pair_hom_rel _ _ _ _ y z) in H2.
  destruct H1; destruct H2.
  simpl in H4.
  apply real_mult_rel_elem in H4.
  apply real_mult_rel_elem in H5.
  destruct (H a0) as [r1 [r2 [?[??]]]].
  exists p1. exists q1. intuition.
  assert (exists z', in_interval z' p2 /\ in_interval z' q2 /\ 0 < z').
  { destruct (plt_hom_directed2 _ _ _ z a0 p2 q2) as [z1 [?[??]]]; auto.
    destruct (plt_hom_directed2 _ _ _ z a0 z1 r2) as [z2 [?[??]]]; auto.
    exists (rint_start z2).
    split.
    - apply H12. apply H15.
      split.
      + apply Qle_refl.
      + apply rint_proper.
    - split.
      + apply H13. apply H15.
        split.
        * apply Qle_refl.
        * apply rint_proper.
      + destruct (H16 (rint_start z2)).
        * split.
          ** apply Qle_refl.
          ** apply rint_proper.
        * apply Qlt_le_trans with (rint_start r2); auto.
          apply Qle_lt_trans with (rint_end r1); auto.
          apply PLT.compose_hom_rel in H8.
          destruct H8 as [?[??]].
          simpl in H19.
          apply injq_rel_elem in H19.
          destruct H19. intuition.
  } 
  destruct H11 as [z' [?[??]]].
  assert (rint_end p1 * z' < rint_start q1 * z').
  { destruct (H4 (rint_end p1 * z')).
    - apply rint_mult_correct.
      exists (rint_end p1). exists z'.
      split.
      + split.
        * apply rint_proper.
        * apply Qle_refl.
      + split; auto.
        reflexivity.
    - destruct (H5 (rint_start q1 * z')).
      + apply rint_mult_correct.
        exists (rint_start q1). exists z'.
        split.
        * split.
          ** apply Qle_refl.
          ** apply rint_proper. 
        * split; auto.
          reflexivity.
      + apply Qle_lt_trans with (rint_end p); auto.
        apply Qlt_le_trans with (rint_start q); auto.
  }
  apply Qmult_lt_r in H14; auto.
Qed.


(** Addition distributes through multiplication.
    Hence, the reals are a ring.
  *)

Lemma real_distrib_le A (x y z: A → PreRealDom) :
  (real_plus ∘ 《 real_mult ∘ 《 x, y 》 
              , real_mult ∘ 《 x, z 》 
              》
   ≤ 
  real_mult ∘ 《 x, real_plus ∘ 《 y, z 》 》)%plt.
Proof.
  hnf; simpl; intros [a r] H.
  apply PLT.compose_hom_rel in H.
  destruct H as [[r1 r2] [H H0]].
  apply (PLT.pair_hom_rel _ _ _ _ _ _ a r1 r2) in H. destruct H.
  apply PLT.compose_hom_rel in H. destruct H as [[??][??]].
  apply PLT.compose_hom_rel in H1. destruct H1 as [[??][??]].
  apply (PLT.pair_hom_rel _ _ _ _ x y) in H. destruct H.
  apply (PLT.pair_hom_rel _ _ _ _ x z) in H1. destruct H1.
  simpl in *.
  apply real_plus_rel_elem in H0.
  apply real_mult_rel_elem in H2.
  apply real_mult_rel_elem in H3.
  apply PLT.compose_hom_rel.
  destruct (plt_hom_directed2 _ _ _ x a c c1) as [c' [?[??]]]; auto.
  exists (c', rint_plus c0 c2).
  split.
  - apply PLT.pair_hom_rel.
    split; auto.
    apply PLT.compose_hom_rel.
    exists (c0,c2). split.
    + apply PLT.pair_hom_rel; auto.
    + simpl. apply real_plus_rel_elem. auto.
  - simpl. apply real_mult_rel_elem.
    hnf; intros.
    apply rint_mult_correct in H9.
    destruct H9 as [q1 [q2 [?[??]]]].
    apply rint_plus_correct in H10.
    destruct H10 as [q3 [q4 [?[??]]]].
    rewrite H13 in H11.
    ring_simplify in H11.
    apply H0.
    apply rint_plus_correct.
    exists (q1*q3), (q1*q4).
    intuition.
    + apply H2.
      apply rint_mult_correct.
      exists q1, q3; intuition.
    + apply H3.
      apply rint_mult_correct.
      exists q1, q4; intuition.
Qed.

(** Probably this lemma can be improved to require only that
    x converges...
  *)
Lemma real_distrib_eq A (x y z: A → PreRealDom) 
  (Hx0 : canonical A x) 
  (Hy0 : canonical A y) 
  (Hz0 : canonical A z)
  (Hx : realdom_converges A x) 
  (Hy : realdom_converges A y) 
  (Hz : realdom_converges A z) :

  (real_plus ∘ 《 real_mult ∘ 《 x, y 》 
              , real_mult ∘ 《 x, z 》 
              》
  ≈
  real_mult ∘ 《 x, real_plus ∘ 《 y, z 》 》)%plt.
Proof.
  apply converges_maximal.
  - apply real_mult_canon; auto.
    apply real_plus_canon; auto.
  - apply real_plus_converges; auto.
    + apply real_mult_converges; auto.
    + apply real_mult_converges; auto.
  - apply real_distrib_le.
Qed.

(*
Lemma real_distrib_le2 A (x y z: A → PreRealDom) 
  (Hx : realdom_converges A x) :
  (real_plus ∘ 《 real_mult ∘ 《 x, y 》 
              , real_mult ∘ 《 x, z 》 
              》
   ≥
  real_mult ∘ 《 x, real_plus ∘ 《 y, z 》 》)%plt.
Proof.
  hnf; simpl; intros [a r] H.
  apply PLT.compose_hom_rel in H.
  destruct H as [[r1 r2] [H H0]].
  apply (PLT.pair_hom_rel _ _ _ _ x (real_plus ∘ 《 y, z 》)%plt) in H. destruct H.
  apply PLT.compose_hom_rel in H1. destruct H1 as [[??][??]].
  apply (PLT.pair_hom_rel _ _ _ _ y z) in H1. destruct H1.
  simpl in *.
  apply real_plus_rel_elem in H2.
  apply real_mult_rel_elem in H0.
Admitted.
     (* ?? how to choose a small enough ε so we can use the fact that x
             converges to complete this proof?  Perhaps we also need that
             y and z are  canonical?
        *) 
*)
(*
  apply PLT.compose_hom_rel.
  exists (rint_mult r1 c, rint_mult r1 c0).
  split.
  apply PLT.pair_hom_rel. split.
  apply PLT.compose_hom_rel.
  exists (r1,c). split.
  apply PLT.pair_hom_rel. split; auto.
  simpl. apply real_mult_rel_elem. auto.
  apply PLT.compose_hom_rel.
  exists (r1,c0). split.
  apply PLT.pair_hom_rel. split; auto.
  simpl. apply real_mult_rel_elem. auto.
  simpl. apply real_plus_rel_elem.
  hnf; intros.
  apply rint_plus_correct in H4.
  destruct H4 as [m [n [?[??]]]].
  apply rint_mult_correct in H4.
  destruct H4 as [s [t [?[??]]]].
  apply rint_mult_correct in H5.
  destruct H5 as [w [u [?[??]]]].
  apply H0.
  apply rint_mult_correct.
  


Qed.
*)

(** Recip is the inverse for multiplication for all reals apart from 0.
    Hence the reals form a field.
  *)

Lemma real_recip_mult_le (A:∂PLT) (x: A → PreRealDom) :
  canonical A x ->
  (real_mult ∘ 《 x, real_recip ∘ x 》 ≤ injq 1 ∘ PLT.terminate _ A)%plt.
Proof.
  intro Hx.
  hnf; intros.
  destruct a as [a r].
  destruct (real_mult_canon A x (real_recip ∘ x)) with a r  as [r' [??]]; auto.
  - apply real_recip_canonical; auto.

  - apply PLT.compose_hom_rel in H0.
    destruct H0 as [[x1 x2] [??]].
    rewrite (PLT.pair_hom_rel _ _ _ _ _ _ a x1 x2) in H0. destruct H0.
    apply PLT.compose_hom_rel in H3.
    destruct H3 as [x' [??]].
    simpl in H2.
    apply real_mult_rel_elem in H2.
    simpl in H4.
    apply real_recip_rel_elem in H4.
    hnf in H4.
    apply PLT.compose_hom_rel. exists tt.
    split.
    + simpl.
      apply eprod_elem. split; auto.
      * apply eff_complete.
      * apply single_axiom. auto.
    + simpl.
      apply injq_rel_elem.
      cut (in_interval 1 r').
      { intros. destruct H1. destruct H5. split.
        - apply Qlt_le_trans with (rint_start r'); auto.
        - apply Qle_lt_trans with (rint_end r'); auto.
      } 
      apply H2.

      destruct (plt_hom_directed2 _ _ _ x a x1 x') as [q [?[??]]]; auto.
      destruct (H4 (rint_start q)) as [m [??]].
      * apply H7.
        split.
        ** apply Qle_refl.
        ** apply rint_proper.
      * apply rint_mult_correct.
        exists (rint_start q), m. intuition.
        apply H6.
        split; intuition.
        apply rint_proper.
Qed.

Lemma real_recip_pos_eq (A:∂PLT) (x: A → PreRealDom) :
  canonical A x ->
  realdom_converges A x ->
  realdom_lt A (injq 0 ∘ PLT.terminate _ A) x ->
  (real_mult ∘ 《 x, real_recip ∘ x 》 ≈ injq 1 ∘ PLT.terminate _ A)%plt.
Proof.
  intros. apply converges_maximal; auto.
  - apply injq_canon.
  - apply real_mult_converges; auto.
    apply real_recip_pos_converges; auto.
  - apply real_recip_mult_le; auto.
Qed.

Lemma real_recip_neg_eq (A:∂PLT) (x: A → PreRealDom) :
  canonical A x ->
  realdom_converges A x ->
  realdom_lt A x (injq 0 ∘ PLT.terminate _ A) ->
  (real_mult ∘ 《 x, real_recip ∘ x 》 ≈ injq 1 ∘ PLT.terminate _ A)%plt.
Proof.
  intros. apply converges_maximal; auto.
  - apply injq_canon.
  - apply real_mult_converges; auto.
    apply real_recip_neg_converges; auto.
  - apply real_recip_mult_le; auto.
Qed.

(** The reals are an archimedian field *)

Lemma real_archimediean (f: 1%plt → PreRealDom) :
  realdom_converges 1%plt f ->
  exists q1 q2,
    realdom_lt 1%plt (injq q1) f /\ realdom_lt 1%plt f (injq q2).
Proof.
  intros.
  destruct (H tt 1%Q) as [x [??]]; [ compute; auto |].
  exists (rint_start x - 1).
  exists (rint_end x + 1)%Q.
  split.
  - red; intros. destruct a. simpl.
    assert (rint_start x - (2#1) < rint_start x - 1).
    { rewrite <- (Qplus_lt_l _ _ (2#1)%Q).
      ring_simplify.    
      rewrite Qplus_comm.
      apply Qle_lt_trans with (0 + rint_start x)%Q.
      - ring_simplify. apply Qle_refl.
      - apply Qplus_lt_le_compat.
        * compute. auto.
        * apply Qle_refl.
    } 
    assert (rint_start x - 1 < rint_start x - (1#2)).
    { rewrite <- (Qplus_lt_l _ _ 1).
      ring_simplify.
      rewrite Qplus_comm.
      apply Qle_lt_trans with (0 + rint_start x)%Q.
      - ring_simplify. apply Qle_refl.
      - apply Qplus_lt_le_compat.
        + compute. auto.
        + apply Qle_refl.
    } 
    assert (rint_start x - (2#1) <= rint_start x - (1#2)).
    { apply Qlt_le_weak. eapply Qlt_trans; eauto. }
    exists (RatInt _ _ H4), x.
    repeat split; simpl; auto.
    + apply injq_rel_elem.
      split; simpl; auto.
    + ring_simplify.
      rewrite Qplus_comm.
      apply Qlt_le_trans with (0 + rint_start x)%Q.
      * apply Qplus_lt_le_compat.
        ** compute. auto.
        ** apply Qle_refl.
      * ring_simplify. apply Qle_refl.

  - red; intros.
    assert (rint_end x + (1#2) < rint_end x + 1).
    { rewrite Qplus_comm.
      rewrite (Qplus_comm _ 1).
      apply Qplus_lt_le_compat.
      + compute. auto.
      + apply Qle_refl.
    } 
    assert (rint_end x + 1 < rint_end x + (2#1)%Q).
    { rewrite Qplus_comm.
      rewrite (Qplus_comm _ (2#1)).
      apply Qplus_lt_le_compat.
      + compute. auto.
      + apply Qle_refl.
    }
    assert (rint_end x + (1#2) <= rint_end x + (2#1)).
    { apply Qlt_le_weak. eapply Qlt_trans; eauto. }
    exists x, (RatInt _ _ H4).
    repeat split; simpl; auto.
    + apply injq_rel_elem.
      split; simpl; auto.
    + rewrite Qplus_comm.
      apply Qle_lt_trans with (0 + rint_end x)%Q.
      * ring_simplify. apply Qle_refl.
      * apply Qplus_lt_le_compat.
        compute. auto.
        apply Qle_refl.
Qed.


(** injq commutes with the ordered field operations on Q *)

Lemma Q_real_opp_compat q :
  real_opp ∘ injq q ≈ injq (Qopp q).
Proof.
  split; intros.
  - intros [??] ?. apply PLT.compose_hom_rel in H.
    destruct H as [r [??]].
    simpl in *.
    apply injq_rel_elem in H.
    apply real_opp_rel_elem in H0.
    apply injq_rel_elem.
    apply rint_ord_test in H0.
    destruct H; destruct H0.
    simpl in *.
    split.
    + eapply Qle_lt_trans; eauto.
      rewrite <- (Qplus_lt_l _ _ q).
      rewrite <- (Qplus_lt_l _ _ (rint_end r)).
      ring_simplify. auto.
    + eapply Qlt_le_trans; [ | apply H2 ].
      rewrite <- (Qplus_lt_l _ _ q).
      rewrite <- (Qplus_lt_l _ _ (rint_start r)).
      ring_simplify. auto.

  - intros [??] ?. apply PLT.compose_hom_rel.
    exists (rint_opp c0).
    split.
    + simpl. apply injq_rel_elem.
      red. simpl.
      simpl in H. apply injq_rel_elem in H.
      destruct H. split; simpl.
      * rewrite <- (Qplus_lt_l _ _ (-q)).
        rewrite <- (Qplus_lt_l _ _ (rint_end c0)).
        ring_simplify. apply H0.
      * rewrite <- (Qplus_lt_l _ _ (-q)).
        rewrite <- (Qplus_lt_l _ _ (rint_start c0)).
        ring_simplify. apply H.
  
    + simpl. apply real_opp_rel_elem.
      apply rint_ord_test. simpl.
      rewrite Qopp_involutive.
      rewrite Qopp_involutive.
      split; apply Qle_refl.
Qed.


Lemma Q_real_lt_compat (q1 q2:Q) :
  realdom_lt 1%plt (injq q1) (injq q2) <-> q1 < q2.
Proof.
  split; intros.

  - destruct (H tt) as [x [y [?[??]]]].

    simpl in H0. simpl in H1.
    apply injq_rel_elem in H0.
    apply injq_rel_elem in H1.
    destruct H0. destruct H1.
    apply Qlt_trans with (rint_end x); auto.
    apply Qlt_trans with (rint_start y); auto.

  - red; intros.
    destruct (Q_dense q1 q2) as [q [??]]; auto.
    destruct (Q_dense q1 q) as [q1' [??]]; auto.
    destruct (Q_dense q q2) as [q2' [??]]; auto.
    assert (q1 - 1 < q1).
    { rewrite <- (Qplus_lt_l _ _ 1).
      ring_simplify.
      rewrite Qplus_comm.
      apply Qle_lt_trans with (0 + q1)%Q.
      - ring_simplify. apply Qle_refl.
      - apply Qplus_lt_le_compat.
        + compute. auto.
        + apply Qle_refl.
    }
    assert (q1 - 1 <= q1')%Q.
    { apply Qle_trans with q1; auto.
      - apply Qlt_le_weak; auto.
      - apply Qlt_le_weak; auto.
    } 
    assert (q2 < q2 + 1).
    { rewrite Qplus_comm.
      apply Qle_lt_trans with (0 + q2)%Q.
      - ring_simplify. apply Qle_refl.
      - apply Qplus_lt_le_compat.
        + compute. auto.
        + apply Qle_refl.
    } 
    assert (q2' <= q2+1).
    { apply Qle_trans with q2; auto.
      - apply Qlt_le_weak; auto.
      - apply Qlt_le_weak; auto.
    } 
    exists (RatInt (q1-1) q1' H7), (RatInt q2' (q2+1) H9).
    repeat split; simpl.
    + apply injq_rel_elem. split; simpl; auto.
    + apply injq_rel_elem. split; simpl; auto.
    + apply Qlt_trans with q; auto.
Qed.

Lemma Q_real_le_compat (q1 q2:Q) :
  realdom_le 1%plt (injq q1) (injq q2) <-> q1 <= q2.
Proof.
  split; intros.  
  - red in H.
  destruct (Qlt_le_dec q2 q1); auto.
  exfalso.
  destruct (H tt (q1 - q2)) as [x [y [?[??]]]].
    + rewrite <- (Qplus_lt_l _ _ q2).
      ring_simplify. auto.
    + simpl in *.
      apply injq_rel_elem in H0.
      apply injq_rel_elem in H1.
      destruct H0; destruct H1.
      assert (rint_end x < rint_end x).
      { eapply Qlt_trans. apply H2.
        rewrite <- (Qplus_lt_l _ _ q2).
        ring_simplify.
        apply Qplus_lt_le_compat; auto.
        apply Qlt_le_weak; auto.
      }
      red in H5. lia.
  
  - red; intros.
    set (ε' := ε / (3#1)).
    assert (0 < ε').
    { unfold ε'.
      apply Qlt_shift_div_l.
      - compute. auto.
      - ring_simplify. auto.
    } 
    assert (q1 < ε' + q1).
    { apply Qle_lt_trans with (0 + q1)%Q.
      - ring_simplify. apply Qle_refl.
      - apply Qplus_lt_le_compat; auto. apply Qle_refl.
    }
    assert (q1 - ε' < q1).
    { rewrite <- (Qplus_lt_l _ _ ε').
      ring_simplify.
      rewrite Qplus_comm. auto.
    } 
    assert (q2 < ε' + q2).
    { apply Qle_lt_trans with (0 + q2)%Q.
      - ring_simplify. apply Qle_refl.
      - apply Qplus_lt_le_compat; auto. apply Qle_refl.
    } 
    assert (q2 - ε' < q2).
    { rewrite <- (Qplus_lt_l _ _ ε').
      ring_simplify.
      rewrite Qplus_comm. auto.
    } 
    assert (q1 - ε' <= ε' + q1).  
    { apply Qle_trans with q1; apply Qlt_le_weak; auto. }
    assert (q2 - ε' <= ε' + q2).
    { apply Qle_trans with q2; apply Qlt_le_weak; auto. }
    exists (RatInt (q1 - ε') (ε' + q1) H6).
    exists (RatInt (q2 - ε') (ε' + q2) H7).
    simpl. repeat split.
    + apply injq_rel_elem. split; simpl; auto.
    + apply injq_rel_elem. split; simpl; auto.
    + rewrite <- (Qplus_lt_l _ _ ε').
      ring_simplify.
      rewrite (Qplus_comm q2).
      apply Qplus_lt_le_compat; auto.
      unfold ε'.
      apply Qle_lt_trans with (((2#1)/(3#1)) * ε).
      * field_simplify. apply Qle_refl.
      * apply Qlt_le_trans with (1 * ε).
        ** rewrite Qmult_lt_r; auto.
           compute. auto.
        ** ring_simplify. apply Qle_refl.
Qed.


Lemma Q_real_eq_compat (q1 q2:Q) :
  injq q1 ≈ injq q2 <-> q1 == q2.
Proof.
  split; intros.
  - destruct (Qcompare_spec q1 q2); auto.
    + exfalso.
      apply Q_real_lt_compat in H0.
      apply (realdom_le_napart 1%plt (injq q1) (injq q2)); auto.
      apply realdom_lt_apart. auto.
    + exfalso.
      apply Q_real_lt_compat in H0.
      apply (realdom_le_napart 1%plt (injq q2) (injq q1)); auto.
      apply realdom_lt_apart. auto.

  - split; hnf; intros [a x] ?; simpl in *.
    + apply injq_rel_elem in H0; apply injq_rel_elem.
      destruct H0. red. rewrite <- H. split; auto.
    + apply injq_rel_elem in H0; apply injq_rel_elem.
      destruct H0. red. rewrite H. split; auto.
Qed.


Lemma Q_real_plus_compat (q q1 q2:Q) :
  (real_plus ∘ 《 injq q1, injq q2 》 ≈ injq q)%plt <-> q1 + q2 == q.
Proof.
  split; intros.
  - destruct (Qlt_le_dec q (q1+q2)).
    + exfalso.
      set (ε := (q1+q2 - q) / (2#1)).
      assert (0 < ε).
      { unfold ε.
        apply Qlt_shift_div_l.
        + reflexivity.
        + rewrite <- (Qplus_lt_l _ _ q).
          ring_simplify. auto.
      }
      assert (q - ε <= q + ε).
      { apply Qplus_le_compat.
        - apply Qle_refl.
        - apply Qle_trans with 0%Q.
          + rewrite <- (Qplus_le_l _ _ ε).
            ring_simplify. apply Qlt_le_weak; auto.
          + apply Qlt_le_weak; auto.
      } 
      assert (q + ε < q1 + q2).
      { rewrite <- (Qmult_lt_r _ _ (2#1)); [ | compute; auto ].
        unfold ε. field_simplify.
        apply Qle_lt_trans with (q + (q1+q2))%Q.
        - rewrite (Qplus_assoc).
          field_simplify.
          field_simplify. apply Qle_refl.
        - apply Qlt_le_trans with ((q1+q2)+(q1+q2))%Q.
          + apply Qplus_lt_le_compat; auto. apply Qle_refl.
          + field_simplify. apply Qle_refl.
      }
      destruct H.
      assert ((tt,(RatInt  _ _ H1)) ∈ PLT.hom_rel (injq q)).
      { simpl. apply injq_rel_elem.
        split; simpl.
        - rewrite <- (Qplus_lt_l _ _ ε).
          ring_simplify.
          rewrite Qplus_comm.
          apply Qle_lt_trans with (0 + q)%Q.
          + ring_simplify. apply Qle_refl.
          + apply Qplus_lt_le_compat; auto. apply Qle_refl.
        - rewrite Qplus_comm.
          apply Qle_lt_trans with (0 + q)%Q.
          + ring_simplify. apply Qle_refl.
          + apply Qplus_lt_le_compat; auto. apply Qle_refl.
      } 
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
      { eapply Qle_lt_trans. apply H6.
        eapply Qlt_le_trans. apply H2.
        apply Qplus_le_compat; apply Qlt_le_weak; auto.
      } 
      red in H10. lia.

    + destruct (Qlt_le_dec (q1+q2) q).
      * exfalso.
        set (ε := (q - (q1+q2)) / (2#1)).
        assert (0 < ε).
        { unfold ε.
          apply Qlt_shift_div_l.
          - reflexivity.
          - rewrite <- (Qplus_lt_l _ _ (q1+q2)).
            ring_simplify. auto.
        } 
        assert (q - ε <= q + ε).
        { apply Qplus_le_compat.
          apply Qle_refl.
          apply Qle_trans with 0%Q.
          - rewrite <- (Qplus_le_l _ _ ε).
            ring_simplify. apply Qlt_le_weak; auto.
          - apply Qlt_le_weak; auto.
        }

        assert (q1+q2+ ε < q).
        { rewrite <- (Qmult_lt_r _ _ (2#1)); [ | compute; auto ].
          unfold ε. field_simplify.
          apply Qle_lt_trans with ((q1+q2)+q)%Q.
          - field_simplify. field_simplify. apply Qle_refl.
          - apply Qlt_le_trans with (q+q)%Q.
            + apply Qplus_lt_le_compat; auto. apply Qle_refl.
            + field_simplify. apply Qle_refl.
        } 
        destruct H.
        assert ((tt,(RatInt  _ _ H1)) ∈ PLT.hom_rel (injq q)).
        { simpl. apply injq_rel_elem.
          split; simpl.
          - rewrite <- (Qplus_lt_l _ _ ε).
            ring_simplify.
            rewrite Qplus_comm.
            apply Qle_lt_trans with (0 + q)%Q.
            + ring_simplify. apply Qle_refl.
            + apply Qplus_lt_le_compat; auto. apply Qle_refl.
          - rewrite Qplus_comm.
            apply Qle_lt_trans with (0 + q)%Q.
            + ring_simplify. apply Qle_refl.
            + apply Qplus_lt_le_compat; auto. apply Qle_refl.
        } 
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
        { eapply Qle_lt_trans. apply H5.
          rewrite <- (Qplus_lt_l _ _ ε).
          ring_simplify.
          apply Qle_lt_trans with (q1+q2+ε)%Q.
          - apply Qplus_le_compat.
            + apply Qplus_le_compat; apply Qlt_le_weak; auto.
            + apply Qle_refl.
          - auto.
        } 
        red in H10. lia.

      * apply Qle_antisym; auto.

  
  - split; intros [u a] H0.
    + apply PLT.compose_hom_rel in H0.
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
      * eapply Qle_lt_trans. apply H1.
        eapply Qlt_trans.
        apply Qplus_lt_l. apply H0.
        apply Qplus_lt_r. apply H2.
      * eapply Qlt_le_trans. 2: apply H5.
        eapply Qlt_trans.
        apply Qplus_lt_l. apply H3.
        apply Qplus_lt_r. apply H4.
  
    + simpl in H0.
      apply injq_rel_elem in H0.
      apply PLT.compose_hom_rel.
      destruct H0.
      set (ε := (Qmin (q-rint_start a) (rint_end a-q)) / (2#1)).
      assert (0 < ε).
      { unfold ε.
        apply Qlt_shift_div_l.
        - compute. auto.
        - ring_simplify.
          apply Q.min_case.
          + intros. rewrite <- H2; auto.
          + rewrite <- (Qplus_lt_l _ _ (rint_start a)).
            ring_simplify. auto.
          + rewrite <- (Qplus_lt_l _ _ q).
            ring_simplify. auto.
      } 
      assert (q1 - ε <= q1 + ε).
      { apply Qle_trans with q1.
        - rewrite <- (Qplus_le_l _ _ ε).
          ring_simplify.
          apply Qle_trans with (q1 + 0)%Q.
          + ring_simplify. apply Qle_refl.
          + apply Qplus_le_compat.
            * apply Qle_refl.
            * apply Qlt_le_weak; auto.
        - apply Qle_trans with (q1 + 0)%Q.
          + ring_simplify. apply Qle_refl.
          + apply Qplus_le_compat.
            * apply Qle_refl.
            * apply Qlt_le_weak; auto.
      } 
      assert (q2 - ε <= q2 + ε).
      { apply Qle_trans with q2.
        - rewrite <- (Qplus_le_l _ _ ε).
          ring_simplify.
          apply Qle_trans with (q2 + 0)%Q.
          + ring_simplify. apply Qle_refl.
          + apply Qplus_le_compat.
            * apply Qle_refl.
            * apply Qlt_le_weak; auto.
        - apply Qle_trans with (q2 + 0)%Q.
          + ring_simplify. apply Qle_refl.
          + apply Qplus_le_compat.
            * apply Qle_refl.
            * apply Qlt_le_weak; auto.
      } 
      exists (RatInt _ _ H3, RatInt _ _ H4).    
      split; simpl.
      * apply PLT.pair_hom_rel; split; simpl.
        ** apply injq_rel_elem.
           split; simpl; auto.
           *** rewrite <- (Qplus_lt_l _ _ ε).
               ring_simplify.
               rewrite Qplus_comm.
               apply Qle_lt_trans with (0 + q1)%Q.
               **** ring_simplify. apply Qle_refl.
               **** apply Qplus_lt_le_compat; auto.
                    apply Qle_refl.
           *** rewrite Qplus_comm.
               apply Qle_lt_trans with (0 + q1)%Q.
               **** ring_simplify. apply Qle_refl.
               **** apply Qplus_lt_le_compat; auto.
                    apply Qle_refl.
        ** apply injq_rel_elem.
           split; simpl; auto.
           *** rewrite <- (Qplus_lt_l _ _ ε).
               ring_simplify.
               rewrite Qplus_comm.
               apply Qle_lt_trans with (0 + q2)%Q.
               **** ring_simplify. apply Qle_refl.
               **** apply Qplus_lt_le_compat; auto.
                    apply Qle_refl.
           *** rewrite Qplus_comm.
               apply Qle_lt_trans with (0 + q2)%Q.
               **** ring_simplify. apply Qle_refl.
               **** apply Qplus_lt_le_compat; auto.
                    apply Qle_refl.
      * simpl. apply real_plus_rel_elem.
        apply rint_ord_test. simpl.
        split.
        ** rewrite <- (Qplus_le_l _ _ ((2#1)*ε)%Q).
           ring_simplify.
           unfold ε.
           apply Q.min_case_strong.
           *** intros. rewrite <- H5. auto.
           *** intros.
               rewrite Qmult_div_r.
               2: compute; discriminate.
               ring_simplify. rewrite H. apply Qle_refl.
           *** rewrite Qmult_div_r.
               2: compute; discriminate.
               rewrite H.
               intros.
               apply Qle_trans with (rint_start a + (q - rint_start a))%Q.
               **** apply Qplus_le_compat. apply Qle_refl. auto.
               **** ring_simplify. apply Qle_refl.
  
        ** apply Qle_trans with (q + (2#1)*ε)%Q.
           *** rewrite <- H. ring_simplify. apply Qle_refl.
           *** unfold ε.
               apply Q.min_case_strong.
               **** intros. rewrite <- H5. auto.
               **** intros.
                    rewrite Qmult_div_r.
                    2: compute; discriminate.
                    apply Qle_trans with (q + (rint_end a - q))%Q.
                    ***** apply Qplus_le_compat. apply Qle_refl. auto.
                    ***** ring_simplify. apply Qle_refl.
               **** intros.
                    rewrite Qmult_div_r.
                    2: compute; discriminate.
                    ring_simplify. apply Qle_refl.
Qed.


Lemma terminate_1_univ :
  id(1%plt) ≈ PLT.terminate true 1%plt.
Proof.
  split; hnf; simpl; intros.
  - destruct a.
    apply eprod_elem.
    destruct u. destruct u0.
    split; apply single_axiom; auto.
  - destruct a.
    destruct u. destruct u0.
    apply ident_elem. hnf. auto.
Qed.

Lemma Q_real_mult_compat (q q1 q2:Q) :
  (real_mult ∘ 《 injq q1, injq q2 》 ≈ injq q)%plt <-> q1 * q2 == q.
Proof.
  split; intros.
  - destruct H.
    destruct (Qcompare_spec (q1*q2) q); auto. 
    + exfalso.
      destruct (Q_dense (q1*q2) q) as [q' [??]]; auto.
      assert (q' <= q + 1).
      { apply Qle_trans with q; intuition.
        apply Qle_trans with (q + 0)%Q.
        - ring_simplify. apply Qle_refl.
        - apply Qplus_le_compat. apply Qle_refl. compute. discriminate.
      } 
      assert ((tt,RatInt q' (q+1) H4) ∈ PLT.hom_rel (injq q)).
      { simpl. apply injq_rel_elem.
        split; simpl; auto.
        apply Qle_lt_trans with (0 + q)%Q.
        - ring_simplify. apply Qle_refl.
        - rewrite (Qplus_comm q 1).
          apply Qplus_lt_le_compat. 
          + compute. auto.
          + apply Qle_refl. 
      } 
      apply H0 in H5.
      apply PLT.compose_hom_rel in H5.
      destruct H5 as [[a b] [??]].
      rewrite (PLT.pair_hom_rel _ _ _ _ (injq q1) (injq q2)) in H5.
      destruct H5.
      simpl in H6.
      apply real_mult_rel_elem in H6.
      assert (in_interval (q1*q2) (RatInt q' (q+1) H4)).
      { apply H6.
        apply rint_mult_correct.
        simpl in *.
        apply injq_rel_elem in H5.
        apply injq_rel_elem in H7.
        exists q1. exists q2. intuition.
        - destruct H5; split; intuition.
        - destruct H7; split; intuition.
      } 
      destruct H8; simpl in *.
      apply (Qlt_irrefl (q1*q2)).
      apply Qlt_le_trans with q'; auto.

    + exfalso.
      destruct (Q_dense q (q1*q2)) as [q' [??]]; auto.
      assert (q-1 <= q').
      { apply Qle_trans with q; intuition.
        rewrite <- (Qplus_le_l _ _ 1). ring_simplify.
        apply Qle_trans with (q + 0)%Q.
        - ring_simplify. apply Qle_refl.
        - apply Qplus_le_compat. apply Qle_refl. compute. discriminate.
      } 
      assert ((tt,RatInt (q-1) q' H4) ∈ PLT.hom_rel (injq q)).
      { simpl. apply injq_rel_elem.
        split; simpl; auto.
        rewrite <- (Qplus_lt_l _ _ 1). ring_simplify.
        apply Qle_lt_trans with (0 + q)%Q.
        - ring_simplify. apply Qle_refl.
        - rewrite (Qplus_comm q 1).
          apply Qplus_lt_le_compat. 
          + compute. auto.
          + apply Qle_refl. 
      } 
      apply H0 in H5.
      apply PLT.compose_hom_rel in H5.
      destruct H5 as [[a b] [??]].
      rewrite (PLT.pair_hom_rel _ _ _ _ (injq q1) (injq q2)) in H5.
      destruct H5.
      simpl in H6.
      apply real_mult_rel_elem in H6.
      assert (in_interval (q1*q2) (RatInt (q-1) q' H4)).
      { apply H6.
        apply rint_mult_correct.
        simpl in *.
        apply injq_rel_elem in H5.
        apply injq_rel_elem in H7.
        exists q1. exists q2. intuition.
        - destruct H5; split; intuition.
        - destruct H7; split; intuition.
      } 
      destruct H8; simpl in *.
      apply (Qlt_irrefl (q1*q2)).
      apply Qle_lt_trans with q'; auto.

  - apply converges_maximal.
    + apply canon_canonical_iff.
      generalize (injq_canon 1%plt q).
      intros.
      apply canon_canonical_iff in H0.
      transitivity (injq q ∘ PLT.terminate true 1%plt).
      * transitivity (injq q ∘ id).
        ** symmetry. apply cat_ident1.
        ** apply cat_respects; auto.
           apply terminate_1_univ.
      * rewrite H0.
        apply cat_respects; auto.
        transitivity (injq q ∘ id).
        ** apply cat_respects; auto.
           symmetry. apply terminate_1_univ.
        ** apply cat_ident1.
    + apply real_mult_converges.
      * apply realdom_converges_le with (injq q1 ∘ PLT.terminate true 1%plt).
        ** transitivity (injq q1 ∘ id).
           *** apply eq_ord.
               apply cat_respects; auto.
               symmetry. apply terminate_1_univ.
           *** rewrite (cat_ident1 ∂PLT). auto.
        ** apply injq_converges.
      * apply realdom_converges_le with (injq q2 ∘ PLT.terminate true 1%plt).
        ** transitivity (injq q2 ∘ id).
           *** apply eq_ord.
               apply cat_respects; auto.
               symmetry. apply terminate_1_univ.
           *** rewrite (cat_ident1 ∂PLT). auto.
        ** apply injq_converges.

    + hnf; simpl; intros.
      destruct a.
      apply PLT.compose_hom_rel in H0.
      destruct H0 as [[a b] [??]].
      simpl in H1. apply real_mult_rel_elem in H1.
      rewrite (PLT.pair_hom_rel _ _ _ _ (injq q1) (injq q2)) in H0. destruct H0.
      simpl in *.
      apply injq_rel_elem in H0.
      apply injq_rel_elem in H2.
      apply injq_rel_elem.
      cut (in_interior q (rint_mult a b)).
      { apply rint_ord_test in H1.
        destruct H1.
        intros [??]; split.
        - eapply Qle_lt_trans; eauto.
        - eapply Qlt_le_trans; eauto.
      } 
      apply rint_mult_correct_interior with q1 q2; auto.
      symmetry; auto.
Qed.


Lemma Q_real_recip_compat (q:Q) : (q == 0%Q -> False) ->
  real_recip ∘ injq q ≈ injq (Qinv q).
Proof.
  intros.
  apply converges_maximal.

  - apply canon_canonical_iff.
    generalize (injq_canon 1%plt (/ q)).
    intros.
    apply canon_canonical_iff in H0.
    transitivity (injq (/ q) ∘ PLT.terminate true 1%plt).
    + transitivity (injq (/ q) ∘ id).
      * symmetry. apply cat_ident1.
      * apply cat_respects; auto.
        apply terminate_1_univ.
    + rewrite H0.
      apply cat_respects; auto.
      transitivity (injq (/ q) ∘ id).
      * apply cat_respects; auto.
        symmetry. apply terminate_1_univ.
      * apply cat_ident1.

  - destruct (Qcompare_spec q 0).
    * elim H; auto.
    * apply real_recip_neg_converges.
      ** assert (injq 0 ≈ injq 0 ∘ PLT.terminate true 1%plt).
         { transitivity (injq 0 ∘ id).
           - rewrite (cat_ident1 ∂PLT). auto.
           - apply cat_respects; auto.
             apply terminate_1_univ.
         } 
         rewrite <- H1.
         apply Q_real_lt_compat. auto.

      ** apply realdom_converges_le with (injq q ∘ PLT.terminate true 1%plt).
         *** transitivity (injq q ∘ id).
             **** apply eq_ord.
                  apply cat_respects; auto.
                  symmetry. apply terminate_1_univ.
             **** rewrite (cat_ident1 ∂PLT). auto.
         *** apply injq_converges.
    * apply real_recip_pos_converges.
      ** assert (injq 0 ≈ injq 0 ∘ PLT.terminate true 1%plt).
         { transitivity (injq 0 ∘ id).
           - rewrite (cat_ident1 ∂PLT). auto.
           - apply cat_respects; auto.
             apply terminate_1_univ.
         }
         rewrite <- H1.
         apply Q_real_lt_compat. auto.

      ** apply realdom_converges_le with (injq q ∘ PLT.terminate true 1%plt).
         *** transitivity (injq q ∘ id).
             **** apply eq_ord.
                  apply cat_respects; auto.
                  symmetry. apply terminate_1_univ.
             **** rewrite (cat_ident1 ∂PLT). auto.
         *** apply injq_converges.

  - hnf; simpl; intros.
    assert (canonical 1%plt (real_recip ∘ injq q)).
    { apply real_recip_canonical.
      apply canon_canonical_iff.
      generalize (injq_canon 1%plt q).
      intros.
      apply canon_canonical_iff in H1.
      transitivity (injq q ∘ PLT.terminate true 1%plt).
      - transitivity (injq q ∘ id).
        + symmetry. apply cat_ident1.
        + apply cat_respects; auto.
          apply terminate_1_univ.
      - rewrite H1.
        apply cat_respects; auto.
        transitivity (injq q ∘ id).
        + apply cat_respects; auto.
          symmetry. apply terminate_1_univ.
        + apply cat_ident1.
    } 
    destruct a.
    destruct (H1 u r) as [r' [??]]; auto.
    apply PLT.compose_hom_rel in H2.
    destruct H2 as [y [??]].
    simpl in H2.
    apply injq_rel_elem in H2.
    simpl in H4.
    apply real_recip_rel_elem in H4.
    red in H4.
    destruct (H4 q) as [a' [??]].
    + destruct H2; split; intuition.
    + apply injq_rel_elem.
      rewrite <- way_inside_alt in H3.
      apply H3.

      assert (a' == /q).
      { apply (Qmult_inj_l a' (/q) q); auto.
        rewrite H6.
        rewrite Qmult_inv_r; auto.
        reflexivity.
      } 
      red.
      rewrite <- H7. auto.
Qed.
