Require Import QArith.
Require Import Qminmax.
Require Import Setoid.

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

Definition way_inside (x y:rational_interval) :=
  rint_start y < rint_start x /\
  rint_end x < rint_end y.


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

Lemma Qle_shift_div_l' : forall a b c:Q, c < 0 -> b <= a*c -> a <= b / c.
Proof.
  intros.
  cut (b / (-c) <= -a ).
  intros.
  rewrite <- (Qopp_involutive a).
  rewrite <- (Qopp_involutive (b/c)).
  apply Qopp_le_compat.
  revert H1. apply Qle_trans.
  cut (- (b/c) == b / -c).
  intros. rewrite H1. apply Qle_refl.
  field.
  intro. apply (Qlt_irrefl 0).
  rewrite <- H1 at 1. auto.
  apply Qle_shift_div_r.
  rewrite <- (Qplus_lt_l _ _ c). ring_simplify. auto.
  ring_simplify. auto.
Qed.

Lemma Qle_shift_div_r' : forall a b c : Q, b < 0 -> c * b <= a -> a / b <= c.
Proof.
  intros.
  cut (-c <= a / (-b)).
  intros.
  rewrite <- (Qopp_involutive c).
  rewrite <- (Qopp_involutive (a/b)).
  apply Qopp_le_compat.
  revert H1. apply Qle_trans'.
  cut (- (a/b) == a / -b).
  intros. rewrite H1. apply Qle_refl.
  field.
  intro. apply (Qlt_irrefl 0).
  rewrite <- H1 at 1. auto.
  apply Qle_shift_div_l.
  rewrite <- (Qplus_lt_l _ _ b). ring_simplify. auto.
  ring_simplify. auto.
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

  Section case2.
    Hypothesis Hx : 0 < x1.
    Hypothesis Hy : y1 <= 0 <= y2.

    Lemma case2_q : y1 * x2 <= q <= x2 * y2.
    Proof.
      destruct HQ. split.
      revert H.
      apply Q.min_case; auto.
      intros. apply H1. rewrite H. auto.
      apply Qle_trans.
      rewrite (Qmult_comm y1).
      apply Qmult_le_compat'; intuition.
      apply Q.min_case; auto.
      intros. apply H1. rewrite H. auto.
      apply Qle_trans.
      rewrite (Qmult_comm y1).
      apply Qle_trans with (0 * 0).
      apply Qmult_le_compat'; intuition.
      apply Qle_trans with x1; intuition.
      apply Qmult_le_compat; intuition.
      apply Q.min_case; auto.
      intros. apply H1. rewrite H. auto.
      apply Qle_trans.
      rewrite (Qmult_comm y1). apply Qle_refl.
      apply Qle_trans.
      rewrite (Qmult_comm y1).
      apply Qle_trans with (0 * 0).
      apply Qmult_le_compat'; intuition.
      apply Qle_trans with x1; intuition.
      apply Qmult_le_compat; intuition.
      apply Qle_trans with x1; intuition.
      
      revert H0.
      apply Q.max_case.
      intros. apply H1. rewrite H0; auto.
      apply Qle_trans'.
      apply Qle_trans with (0 * 0).
      apply Qmult_le_compat'; intuition.
      apply Qmult_le_compat; intuition.
      apply Qle_trans with x1; intuition.
      apply Q.max_case.
      intros. apply H1. rewrite H0; auto.
      apply Qle_trans'. apply Qmult_le_compat; intuition.
      apply Q.max_case.
      intros. apply H1. rewrite H0; auto.
      apply Qle_trans'. 
      apply Qle_trans with (0 * 0).
      apply Qmult_le_compat'; intuition.
      apply Qle_trans with x1; intuition.
      apply Qmult_le_compat; intuition.
      apply Qle_trans with x1; intuition.
      apply Qle_trans'. 
      apply Qle_refl.
    Qed.
 
    Lemma case2 : exists q1 q2, x1 <= q1 <= x2 /\ y1 <= q2 <= y2 /\ q == q1 * q2.
    Proof.
      clear HQ. destruct case2_q.
      exists x2. exists (q/x2).
      intuition.
      apply Qle_shift_div_l; auto.
      apply Qlt_le_trans with x1; auto.
      apply Qle_shift_div_r; auto.
      apply Qlt_le_trans with x1; auto.
      rewrite (Qmult_comm y2); auto.
      rewrite Qmult_div_r; auto. reflexivity.
      intro.
      assert (0 < 0).
      apply Qlt_le_trans with x1; auto.
      apply Qle_trans with x2; auto.
      rewrite H3. apply Qle_refl.
      red in H4. omega.
    Qed.
  End case2.


  Section case3.
    Hypothesis Hx : 0 < x1.
    Hypothesis Hy : y2 < 0.

    Lemma case3_q : y1 * x2 <= q <= x1 * y2.
    Proof.
      destruct HQ. split.

      revert H.
      apply Q.min_case; auto.
      intros. apply H1. rewrite H. auto.
      apply Qle_trans.
      rewrite (Qmult_comm y1).
      apply Qmult_le_compat'; intuition.
      apply Qle_trans with y2; intuition.
      apply Q.min_case; auto.
      intros. apply H1. rewrite H. auto.
      apply Qle_trans.
      rewrite (Qmult_comm y1).
      apply Qmult_le_compat'; intuition.
      apply Q.min_case; auto.
      intros. apply H1. rewrite H. auto.
      apply Qle_trans.
      rewrite (Qmult_comm y1).
      apply Qmult_le_compat'; intuition.
      apply Qle_trans with x1; intuition.
      apply Qle_trans with y2; intuition.
      apply Qle_trans.
      rewrite (Qmult_comm y1).
      apply Qmult_le_compat'; intuition.
      apply Qle_trans with x1; intuition.
      
      revert H0.
      apply Q.max_case.
      intros. apply H1. rewrite H0; auto.
      apply Qle_trans'.
      apply Qmult_le_compat'; intuition.
      apply Q.max_case.
      intros. apply H1. rewrite H0; auto.
      apply Qle_trans'. apply Qmult_le_compat'; intuition.
      apply Q.max_case.
      intros. apply H1. rewrite H0; auto.
      apply Qle_trans'. 
      apply Qmult_le_compat'; intuition.
      apply Qle_trans'. 
      apply Qmult_le_compat'; intuition.
    Qed.
  

    Lemma case3 : exists q1 q2, x1 <= q1 <= x2 /\ y1 <= q2 <= y2 /\ q == q1 * q2.
    Proof.
      clear HQ. destruct case3_q.
      
      destruct (Qlt_le_dec (x1*y1) q).
      exists x1. exists (q/x1).
      intuition.
      apply Qle_shift_div_l; intuition.
      rewrite Qmult_comm; intuition.
      apply Qle_shift_div_r; intuition.
      rewrite Qmult_comm; intuition.
      rewrite Qmult_div_r; auto. reflexivity.
      intro. apply (Qlt_irrefl 0).
      rewrite <- H1 at 2; auto.
      
      destruct (Qlt_le_dec q (x2*y2)).
      exists x2. exists (q/x2).
      intuition.
      apply Qle_shift_div_l; intuition.
      apply Qlt_le_trans with x1; auto.
      apply Qle_shift_div_r; intuition.
      apply Qlt_le_trans with x1; auto.
      rewrite Qmult_comm; intuition.
      rewrite Qmult_div_r; auto. reflexivity.
      intro. apply (Qlt_irrefl 0).
      rewrite <- H1 at 2; auto.
      apply Qlt_le_trans with x1; auto.
      
      assert (y1+y2 < 0).
        apply Qle_lt_trans with y2; auto.
        rewrite <- (Qplus_le_l _ _ (-y2)). ring_simplify.
        apply Qle_trans with y2; intuition.
      exists ((q+q) / (y1+y2)).
      exists ((y1+y2) / (2#1)).
      intuition.
      apply Qle_shift_div_l'; auto.
      ring_simplify (x1*(y1+y2)).
      apply Qplus_le_compat; auto.
      apply Qle_shift_div_r'; auto.
      ring_simplify (x2*(y1+y2)).
      apply Qplus_le_compat; auto.
      rewrite Qmult_comm; auto.

      apply Qle_shift_div_l; intuition.
      rewrite <- (Qplus_le_l _ _ (-y1)). ring_simplify. auto.
      apply Qle_shift_div_r; intuition.
      rewrite <- (Qplus_le_l _ _ (-y2)). ring_simplify. auto.
      assert (~ (y1+y2 == 0)).
      intro. apply (Qlt_irrefl 0).
      rewrite <- H2 at 1. auto.
      field_simplify; auto.
      field_simplify; auto.
      field_simplify; auto.
      reflexivity.
    Qed.
  End case3.

  Section case4.
    Hypothesis Hx : x1 <= 0 <= x2.
    Hypothesis Hy : y1 <= 0 <= y2.

    Lemma case4_hi : (q <= x1*y1) \/ (q <= x2*y2).
    Proof.
      destruct HQ. revert H0.
      apply Q.max_case; auto. intros. apply H1. rewrite H0; auto.
      apply Q.max_case_strong; intros. apply H1. rewrite H0; auto.
      apply Q.max_lub_r in H0.
      destruct (Qlt_le_dec 0 y2).
      apply (Qmult_le_r) in H0; auto.
      assert (x1 == x2).
      apply Qle_antisym; auto.
      right. rewrite <- H2. auto.
      assert (y2 == 0).
      apply Qle_antisym; auto.
      destruct Hy; auto.
      right.
      rewrite H2.
      rewrite H2 in H1.
      ring_simplify. ring_simplify in H1. auto.
      revert H1.
      apply Q.max_case_strong; intros. apply H2. rewrite H1; auto.
      destruct (Qlt_le_dec 0 x2).
      apply (Qmult_le_l) in H1; auto.
      assert (y1 == y2).
      apply Qle_antisym; auto.
      right. rewrite <- H3. auto.
      assert (x2 == 0).
      apply Qle_antisym; auto. destruct Hx; auto.
      right. rewrite H3. rewrite H3 in H2.
      ring_simplify. ring_simplify in H2. auto.
      auto.
    Qed.

    Lemma case4_low : (x1*y2 <= q) \/ (x2*y1 <= q).
    Proof.
      destruct HQ.
      revert H.
      apply Q.min_case_strong; intros. apply H1. rewrite H; auto.
      apply Q.min_glb_l in H.
      apply Qopp_le_compat in H.
      assert (y2 * (-x1) <= y1 * (-x1)).
      rewrite (Qmult_comm y2).
      rewrite (Qmult_comm y1).
      ring_simplify.
      ring_simplify in H.
      auto.
      destruct (Qlt_le_dec x1 0).
      apply (Qmult_le_r) in H2.
      left.
      assert (y1 == y2).
      apply Qle_antisym; auto.
      rewrite <- H3. auto.
      rewrite <- (Qplus_lt_l _ _ x1). ring_simplify. auto.
      assert (x1 == 0).
      apply Qle_antisym; auto.
      destruct Hx; auto.
      left. rewrite H3.
      ring_simplify.
      rewrite H3 in H1. ring_simplify in H1. auto.

      revert H1.
      apply Q.min_case; auto. intros. apply H2. rewrite H1; auto.
      apply Q.min_case_strong; auto. intros. apply H2. rewrite H1; auto.
      intros.
      destruct (Qlt_le_dec 0 x2).
      rewrite Qmult_le_l in H1.
      assert (y1 == y2).
      apply Qle_antisym; auto. 
      right. rewrite H3. auto.
      auto.
      assert (x2 == 0).
      apply Qle_antisym; auto. 
      destruct Hx; auto.
      rewrite H3.
      right.
      ring_simplify.
      rewrite H3 in H2.
      ring_simplify in H2.
      auto.
    Qed.

    Lemma case4 : exists q1 q2, x1 <= q1 <= x2 /\ y1 <= q2 <= y2 /\ q == q1 * q2.
    Proof.
      clear HQ.
      destruct case4_low; destruct case4_hi.
      destruct (Qeq_dec x1 0).
      exists 0. exists 0.
      intuition.
      ring_simplify. apply Qle_antisym.
      rewrite q0 in H0. ring_simplify in H0. auto.
      rewrite q0 in H. ring_simplify in H. auto.
      exists x1. exists (q/x1).
      intuition.
      apply Qle_shift_div_l'.
      apply Qle_lteq in H3. intuition.
      rewrite Qmult_comm. auto.
      apply Qle_shift_div_r'.
      apply Qle_lteq in H3. intuition.
      rewrite Qmult_comm. auto.
      rewrite Qmult_div_r; auto. reflexivity.

      destruct (Qeq_dec y2 0).
      exists 0. exists 0.
      intuition.
      ring_simplify. apply Qle_antisym.
      rewrite q0 in H0. ring_simplify in H0. auto.
      rewrite q0 in H. ring_simplify in H. auto.
      exists (q/y2). exists y2.
      intuition.
      apply Qle_shift_div_l.
      apply Qle_lteq in H4. intuition.
      auto.
      apply Qle_shift_div_r.
      apply Qle_lteq in H4. intuition.
      auto.
      rewrite Qmult_comm.
      rewrite Qmult_div_r; auto. reflexivity.
      
      destruct (Qeq_dec y1 0).
      exists 0. exists 0.
      intuition.
      ring_simplify. apply Qle_antisym.
      rewrite q0 in H0. ring_simplify in H0. auto.
      rewrite q0 in H. ring_simplify in H. auto.
      exists (q/y1). exists y1.
      intuition.
      apply Qle_shift_div_l'.
      apply Qle_lteq in H3. intuition.
      auto.
      apply Qle_shift_div_r'.
      apply Qle_lteq in H3. intuition.
      auto.
      rewrite Qmult_comm.
      rewrite Qmult_div_r; auto. reflexivity.

      destruct (Qeq_dec x2 0).
      exists 0. exists 0.
      intuition.
      ring_simplify. apply Qle_antisym.
      rewrite q0 in H0. ring_simplify in H0. auto.
      rewrite q0 in H. ring_simplify in H. auto.
      exists x2. exists (q/x2).
      intuition.
      apply Qle_shift_div_l.
      apply Qle_lteq in H2. intuition.
      rewrite Qmult_comm. auto.
      apply Qle_shift_div_r.
      apply Qle_lteq in H2. intuition.
      rewrite Qmult_comm.
      auto.
      rewrite Qmult_div_r; auto. reflexivity.
    Qed.
  End case4.
End mult_correct.

Lemma mult_opp_simpl (p q:Q) :
  (-p) * (-q) == p * q. 
Proof.
  ring.
Qed.

Lemma rint_mult_opp r1 r2 q :
  in_interval q (rint_mult r1 r2) ->
  in_interval q (rint_mult (rint_opp r1) (rint_opp r2)).
Proof.
  unfold in_interval.
  simpl. intuition.
  repeat rewrite mult_opp_simpl.
  revert H0. apply Qle_trans.
  match goal with [ |- ?X <= _ ] => remember X as m end.
  apply Q.min_case. intros. rewrite <- H; auto.
  rewrite Heqm.
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_r.
  apply Q.le_min_r.
  apply Q.min_case. intros. rewrite <- H; auto.
  rewrite Heqm.
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_r.
  apply Q.le_min_l.
  apply Q.min_case. intros. rewrite <- H; auto.
  rewrite Heqm.
  eapply Qle_trans. apply Q.le_min_r.
  apply Q.le_min_l.
  rewrite Heqm.
  apply Q.le_min_l.

  repeat rewrite mult_opp_simpl.
  revert H1. apply Qle_trans'.
  match goal with [ |- _ <= ?X ] => remember X as m end.
  apply Q.max_case. intros. rewrite <- H; auto.
  rewrite Heqm.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_r.
  apply Q.le_max_r.
  apply Q.max_case. intros. rewrite <- H; auto.
  rewrite Heqm.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_r.
  apply Q.le_max_l.
  apply Q.max_case. intros. rewrite <- H; auto.
  rewrite Heqm.
  eapply Qle_trans. 2: apply Q.le_max_r.
  apply Q.le_max_l.
  rewrite Heqm.
  apply Q.le_max_l.
Qed.

Lemma rint_mult_swap r1 r2 q :
  in_interval q (rint_mult r1 r2) ->
  in_interval q (rint_mult r2 r1).
Proof.
  unfold in_interval; simpl; intuition.
  revert H0. apply Qle_trans.
  match goal with [ |- ?X <= _ ] => remember X as m end.
  apply Q.min_case. intros. rewrite <- H; auto.
  rewrite Heqm.
  eapply Qle_trans. apply Q.le_min_l.
  rewrite Qmult_comm. apply Qle_refl.
  apply Q.min_case. intros. rewrite <- H; auto.
  rewrite Heqm.
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_l.
  rewrite Qmult_comm. apply Qle_refl.
  apply Q.min_case. intros. rewrite <- H; auto.
  rewrite Heqm.
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_l.
  rewrite Qmult_comm. apply Qle_refl.
  rewrite Heqm.
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_r.
  eapply Qle_trans. apply Q.le_min_r.
  rewrite Qmult_comm. apply Qle_refl.

  revert H1. apply Qle_trans'.
  match goal with [ |- _ <= ?X ] => remember X as m end.
  apply Q.max_case. intros. rewrite <- H; auto.
  rewrite Heqm.
  eapply Qle_trans. 2: apply Q.le_max_l.
  rewrite Qmult_comm. apply Qle_refl.
  apply Q.max_case. intros. rewrite <- H; auto.
  rewrite Heqm.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_l.
  rewrite Qmult_comm. apply Qle_refl.
  apply Q.max_case. intros. rewrite <- H; auto.
  rewrite Heqm.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_l.
  rewrite Qmult_comm. apply Qle_refl.
  rewrite Heqm.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_r.
  eapply Qle_trans. 2: apply Q.le_max_r.
  rewrite Qmult_comm. apply Qle_refl.
Qed.

Lemma rint_mult_correct r1 r2 q:
  in_interval q (rint_mult r1 r2) <-> 
  exists q1 q2,
    in_interval q1 r1 /\ in_interval q2 r2 /\ q == q1 * q2.
Proof.
  split; intros. destruct H.

  generalize (rint_proper r1).
  generalize (rint_proper r2). intros.
  destruct (Qlt_le_dec 0 (rint_start r1)).
  destruct (Qlt_le_dec 0 (rint_start r2)).
  apply case1; auto.
  destruct (Qlt_le_dec (rint_end r2) 0).
  apply case3; auto.
  apply case2; auto.

  destruct (Qlt_le_dec 0 (rint_start r2)).
  destruct (Qlt_le_dec (rint_end r1) 0).
  destruct (case3 _ _ _ _ q H1 H2) as [m [n [?[??]]]]; auto.
  apply rint_mult_swap; red; auto.
  exists n, m. unfold in_interval. intuition.
  rewrite H5. rewrite Qmult_comm. reflexivity.
  destruct (case2 _ _ (rint_start r1) (rint_end r1) q H1) as [m [n [?[??]]]]; auto.
  apply rint_mult_swap; red; auto.
  exists n, m. unfold in_interval. intuition.
  rewrite H5. rewrite Qmult_comm. reflexivity.

  destruct (Qlt_le_dec (rint_end r1) 0).
  destruct (Qlt_le_dec (rint_end r2) 0).
  
  destruct (case1 (- rint_end r1) (- rint_start r1) (- rint_end r2) (- rint_start r2) q) as [m [n [?[??]]]].
  apply Qopp_le_compat; auto.
  apply Qopp_le_compat; auto.
  apply rint_mult_opp. split; auto.
  rewrite <- (Qplus_lt_l _ _ (rint_end r1)). ring_simplify. auto.
  rewrite <- (Qplus_lt_l _ _ (rint_end r2)). ring_simplify. auto.
  exists (-m). exists (-n).
  unfold in_interval. intuition.
  rewrite <- (Qopp_involutive (rint_start r1)). apply Qopp_le_compat; auto.
  rewrite <- (Qopp_involutive (rint_end r1)). apply Qopp_le_compat; auto.
  rewrite <- (Qopp_involutive (rint_start r2)). apply Qopp_le_compat; auto.
  rewrite <- (Qopp_involutive (rint_end r2)). apply Qopp_le_compat; auto.
  rewrite H5. ring.
  
  destruct (Qlt_le_dec 0 (rint_start r2)).
  
  destruct (case3 _ _ _ _ q H1 H2) as [m [n [?[??]]]]; auto.
  apply rint_mult_swap; red; auto.
  exists n, m. unfold in_interval; intuition.
  rewrite H5. ring.

  destruct (case2 (- rint_end r1) (- rint_start r1) (- rint_end r2) (- rint_start r2) q) as [m [n [?[??]]]].
  apply Qopp_le_compat; auto.
  apply rint_mult_opp. split; auto.
  rewrite <- (Qplus_lt_l _ _ (rint_end r1)). ring_simplify. auto.
  split.
  rewrite <- (Qplus_le_l _ _ (rint_end r2)). ring_simplify. auto.
  rewrite <- (Qplus_le_l _ _ (rint_start r2)). ring_simplify. auto.
  exists (-m). exists (-n).
  unfold in_interval. intuition.
  rewrite <- (Qopp_involutive (rint_start r1)). apply Qopp_le_compat; auto.
  rewrite <- (Qopp_involutive (rint_end r1)). apply Qopp_le_compat; auto.
  rewrite <- (Qopp_involutive (rint_start r2)). apply Qopp_le_compat; auto.
  rewrite <- (Qopp_involutive (rint_end r2)). apply Qopp_le_compat; auto.
  rewrite H5. ring.
  
  destruct (Qlt_le_dec (rint_end r2) 0).
  destruct (case2 (- rint_end r2) (- rint_start r2) (- rint_end r1) (- rint_start r1) q) as [m [n [?[??]]]].
  apply Qopp_le_compat; auto.
  apply rint_mult_opp.
  apply rint_mult_swap.
  split; auto.
  rewrite <- (Qplus_lt_l _ _ (rint_end r2)). ring_simplify. auto.
  split.
  rewrite <- (Qplus_le_l _ _ (rint_end r1)). ring_simplify. auto.
  rewrite <- (Qplus_le_l _ _ (rint_start r1)). ring_simplify. auto.
  exists (-n). exists (-m).
  unfold in_interval. intuition.
  rewrite <- (Qopp_involutive (rint_start r1)). apply Qopp_le_compat; auto.
  rewrite <- (Qopp_involutive (rint_end r1)). apply Qopp_le_compat; auto.
  rewrite <- (Qopp_involutive (rint_start r2)). apply Qopp_le_compat; auto.
  rewrite <- (Qopp_involutive (rint_end r2)). apply Qopp_le_compat; auto.
  rewrite H5. ring.
  
  apply case4; repeat split; auto.


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
