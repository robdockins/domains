Require Import QArith.
Require Import Qminmax.
Require Import Setoid.

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

Lemma Qmin_Qmax_le : forall x1 x2 y1 y2,
   x1 <= x2 -> y1 <= y2 ->
   Qmin x1 y1 <= Qmax x2 y2.
Proof.
  intros. apply Q.min_case.
  intros. rewrite <- H1. auto.
  apply Qle_trans with x2; auto.
  apply Q.le_max_l.
  apply Qle_trans with y2; auto.
  apply Q.le_max_r.
Qed.                 

Program Definition rint_mult (r1 r2:rational_interval) : rational_interval
  := RatInt (Qmin (rint_start r1 * rint_start r2)
            (Qmin (rint_start r1 * rint_end   r2)
            (Qmin (rint_end   r1 * rint_start r2)
                  (rint_end   r1 * rint_end   r2))))
            (Qmax (rint_start r1 * rint_start r2)
            (Qmax (rint_start r1 * rint_end   r2)
            (Qmax (rint_end   r1 * rint_start r2)
                  (rint_end   r1 * rint_end   r2))))
            _.
Next Obligation.
  intros. 
  apply Qmin_Qmax_le. apply Qle_refl.
  apply Qmin_Qmax_le. apply Qle_refl.
  apply Qmin_Qmax_le; apply Qle_refl.
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


Lemma Qmult_le_compat a b x y :
  0 <= a <= x ->
  0 <= b <= y ->
  a * b <= x * y.
Proof.
  intuition.
  apply Qle_trans with (a * y).
  do 2 rewrite (Qmult_comm a).
  apply Qmult_le_compat_r; auto.
  apply Qmult_le_compat_r; auto.
  apply Qle_trans with b; auto.
Qed.

Lemma Qmult_le_compat' a b x y :
  0 <= a <= x ->
  y <= b <= 0 ->
  x * y <= a * b.
Proof.
  intuition.
  rewrite <- (Qopp_involutive (x*y)).
  rewrite <- (Qopp_involutive (a*b)).
  apply Qopp_le_compat.
  apply Qle_trans with (a * (-b)).
  ring_simplify. apply Qle_refl.
  apply Qle_trans with (x * (-y)).
  apply Qmult_le_compat.
  split; auto.
  split.
  apply Qle_trans with (-0).
  compute. discriminate.
  apply Qopp_le_compat; auto.
  apply Qopp_le_compat; auto.
  ring_simplify. apply Qle_refl.
Qed.

Lemma Qmult_le_compat'' a b x y :
  x <= a <= 0 ->
  y <= b <= 0 ->
  a * b <= x * y.
Proof.
  intuition.
  rewrite <- (Qopp_involutive (x*y)).
  rewrite <- (Qopp_involutive (a*b)).
  apply Qopp_le_compat.
  apply Qle_trans with ((-x) * y).
  ring_simplify. apply Qle_refl.
  apply Qle_trans with ((-a) * b).
  apply Qmult_le_compat'; auto.
  split.
  apply Qle_trans with (-0).
  compute. discriminate.
  apply Qopp_le_compat; auto.
  apply Qopp_le_compat; auto.
  ring_simplify. apply Qle_refl.
Qed.

Lemma Qle_trans' (x y z:Q) : y <= z -> x <= y -> x <= z.
Proof. 
  intros. apply (Qle_trans _ _ _ H0 H).
Qed.

Section mult_correct.
  Variables x1 x2 y1 y2:Q.
  Variable q:Q.

  Hypothesis HX : x1 <= x2.
  Hypothesis HY : y1 <= y2.
  Hypothesis HQ : 
            (Qmin (x1 * y1)
            (Qmin (x1 * y2)
            (Qmin (x2 * y1)
                  (x2 * y2))))
            <=
            q
            <=
            (Qmax (x1 * y1)
            (Qmax (x1 * y2)
            (Qmax (x2 * y1)
                  (x2 * y2)))).

  Section case1.
    Hypothesis Hx : 0 < x1.
    Hypothesis Hy : 0 < y1.

    Lemma case1_q : x1 * y1 <= q <= x2 * y2.
    Proof.
      destruct HQ. split.
      revert H.
      apply Q.min_case; auto.
      intros. apply H1. rewrite H. auto.
      apply Q.min_case; auto.
      intros. apply H1. rewrite H. auto.
      apply Qle_trans.
      apply Qmult_le_compat; intuition.
      apply Q.min_case; auto.
      intros. apply H1. rewrite H. auto.
      apply Qle_trans.
      apply Qmult_le_compat; intuition.
      apply Qle_trans.
      apply Qmult_le_compat; intuition.
      
      revert H0.
      apply Q.max_case.
      intros. apply H1. rewrite H0; auto.
      apply Qle_trans'. apply Qmult_le_compat; intuition.
      apply Q.max_case.
      intros. apply H1. rewrite H0; auto.
      apply Qle_trans'. apply Qmult_le_compat; intuition.
      apply Qle_trans with y1; intuition.
      apply Q.max_case.
      intros. apply H1. rewrite H0; auto.
      apply Qle_trans'. apply Qmult_le_compat; intuition.
      apply Qle_trans with x1; intuition.
      auto.
    Qed.

    Lemma case1 : exists q1 q2, x1 <= q1 <= x2 /\ y1 <= q2 <= y2 /\ q == q1 * q2.
    Proof.
      clear HQ. destruct (case1_q).

      destruct (Qlt_le_dec (q/x1) y2).
      exists x1. exists (q/x1).
      intuition.
      apply Qle_shift_div_l; auto.
      rewrite Qmult_comm. auto.
      rewrite Qmult_div_r; intuition.
      assert (0 < 0). 
      rewrite <- H1 at 2. auto.
      red in H2. omega.

      destruct (Qlt_le_dec x1 (q/y2)).
      exists (q/y2). exists y2.
      intuition.
      apply Qle_shift_div_r; auto.
      apply Qlt_le_trans with y1; auto.
      rewrite Qmult_comm.
      rewrite Qmult_div_r; intuition.
      assert (0 < 0). 
      rewrite <- H1 at 2. 
      apply Qlt_le_trans with y1; intuition.
      red in H2. omega.

      exists x1. exists y2.
      intuition.
      apply Qle_antisym.
      assert ((q / y2) * y2 <= x1 * y2).
      apply Qmult_le_compat; intuition.
      apply Qle_shift_div_l; auto.
      apply Qlt_le_trans with y1; auto.
      apply Qle_trans with (x1*y1); auto.
      apply Qle_trans with (0*0).
      compute. discriminate.
      apply Qmult_le_compat; intuition.
      apply Qle_trans with y1; intuition.
      rewrite (Qmult_comm) in H1.
      rewrite Qmult_div_r in H1; intuition.
      assert (0 < 0).
      apply Qlt_le_trans with y1; intuition.
      rewrite <- H2. auto.
      red in H3. omega.
      assert (x1 * y2 <= x1 * (q / x1)).
      apply Qmult_le_compat; intuition.
      apply Qle_trans with y1; intuition.
      rewrite Qmult_div_r in H1; intuition.
      assert (0 < 0).
      rewrite <- H2 at 2. auto.
      red in H3. omega.
    Qed.
  End case1.




Lemma rint_mult_correct r1 r2 q:
  in_interval q (rint_mult r1 r2) <-> 
  exists q1 q2,
    in_interval q1 r1 /\ in_interval q2 r2 /\ q == q1 * q2.
Proof.
  split; intros. destruct H.

  simpl in *.
  
  

admit.

  destruct H as [q1 [q2 [?[??]]]].
  red. rewrite H1. simpl.
  destruct H. destruct H0.
  split.
  destruct (Qlt_le_dec 0 (rint_start r1)).
  destruct (Qlt_le_dec 0 (rint_start r2)).
  eapply Qle_trans. apply Q.le_min_l.
  apply Qmult_le_compat; intuition.
  destruct (Qlt_le_dec q2 0).
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_l.
  apply Qmult_le_compat'; intuition.
  apply Qle_trans with (rint_start r1); intuition.
  eapply Qle_trans. apply Q.le_min_l.
  apply Qle_trans with (0 * 0)%Q.
  apply Qmult_le_compat'; intuition.
  apply Qmult_le_compat; intuition.
  apply Qle_trans with (rint_start r1); intuition.
  destruct (Qlt_le_dec 0 (rint_start r2)).
  destruct (Qlt_le_dec q1 0).
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_l.
  rewrite (Qmult_comm (rint_start r1)).
  rewrite (Qmult_comm q1).
  apply Qmult_le_compat'; intuition.
  apply Qle_trans with (rint_start r2); intuition.
  eapply Qle_trans. apply Q.le_min_l.
  apply Qle_trans with (0 * 0)%Q.
  rewrite (Qmult_comm (rint_start r1)).
  apply Qmult_le_compat'; intuition.
  apply Qmult_le_compat; intuition.
  apply Qle_trans with (rint_start r2); intuition.
  destruct (Qlt_le_dec 0 q1).
  destruct (Qlt_le_dec 0 q2).
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_l.
  apply Qle_trans with (0 * 0)%Q.
  rewrite (Qmult_comm (rint_start r1)).
  apply Qmult_le_compat'; intuition.
  apply Qle_trans with q2; intuition.
  apply Qmult_le_compat; intuition.
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_l.
  apply Qmult_le_compat'; intuition.
  destruct (Qlt_le_dec 0 q2).
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_l.
  rewrite (Qmult_comm (rint_start r1)).
  rewrite (Qmult_comm q1).
  apply Qmult_le_compat'; intuition.
  destruct (Qlt_le_dec 0 (rint_end r1)).
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_l.
  apply Qle_trans with (0 * 0)%Q.
  apply Qmult_le_compat'; intuition.
  apply Qmult_le_compat''; intuition.
  destruct (Qlt_le_dec 0 (rint_end r2)).
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_l.
  apply Qle_trans with (0 * 0)%Q.
  rewrite (Qmult_comm (rint_start r1)).
  apply Qmult_le_compat'; intuition.
  apply Qmult_le_compat''; intuition.
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_r.
  apply Qmult_le_compat''; intuition.
  
  destruct (Qlt_le_dec 0 q1).
  destruct (Qlt_le_dec 0 q2).
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_r.
  apply Qmult_le_compat; intuition.
  destruct (Qlt_le_dec 0 (rint_end r2)).
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_r.
  apply Qle_trans with (0 * 0)%Q.
  apply Qmult_le_compat'; intuition.
  apply Qmult_le_compat; intuition.
  apply Qle_trans with q1; intuition.
  destruct (Qlt_le_dec 0 (rint_start r1)).
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_l.
  apply Qmult_le_compat'; intuition.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_l.
  apply Qle_trans with (0 * 0)%Q.
  apply Qmult_le_compat'; intuition.
  apply Qmult_le_compat''; intuition.
  
  destruct (Qlt_le_dec 0 q2).
  destruct (Qlt_le_dec 0 (rint_end r1)).
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_r.
  apply Qle_trans with (0 * 0)%Q.
  rewrite (Qmult_comm q1).
  apply Qmult_le_compat'; intuition.
  apply Qmult_le_compat; intuition.
  apply Qle_trans with q2; intuition.
  destruct (Qlt_le_dec 0 (rint_start r2)).
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_l.
  rewrite (Qmult_comm q1).
  rewrite (Qmult_comm (rint_end r1)).
  apply Qmult_le_compat'; intuition.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_l.
  apply Qle_trans with (0 * 0)%Q.
  rewrite (Qmult_comm q1).
  apply Qmult_le_compat'; intuition.
  apply Qmult_le_compat''; intuition.
  
  eapply Qle_trans. 2: apply Q.le_max_l.
  apply Qmult_le_compat''; intuition.
Qed.
