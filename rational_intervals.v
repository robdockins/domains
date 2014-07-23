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

Lemma Qmult_lt_compat a b x y :
  0 < a /\ a <= x ->
  0 <= b /\ b < y ->
  a * b < x * y.
Proof.
  intuition.
  apply Qlt_le_trans with (a * y).
  do 2 rewrite (Qmult_comm a).
  apply Qmult_lt_compat_r; auto.
  apply Qmult_le_compat_r; auto.
  apply Qle_trans with b; intuition.
Qed.

Lemma mult_opp_simpl (p q:Q) :
  (-p) * (-q) == p * q. 
Proof.
  ring.
Qed.

Lemma Qopp_le_compat': forall p q : Q, -p <= -q -> q <= p.
Proof.
  intros.
  rewrite <- (Qopp_involutive p).
  rewrite <- (Qopp_involutive q).
  apply Qopp_le_compat. auto.
Qed.

Lemma min_unicity_le:
  forall n m p : Q, n <= m /\ p == n \/ m <= n /\ p == m -> p == Qmin n m.
Proof.
  intros.
  destruct (Q.min_spec_le n m).
  destruct H0. 
  rewrite H1.
  intuition. rewrite H3.
  apply Qle_antisym; auto.
  destruct H0. rewrite H1.
  intuition. rewrite H3.
  apply Qle_antisym; auto.
Qed.  

Lemma max_unicity_le:
  forall n m p : Q, n <= m /\ p == m \/ m <= n /\ p == n -> p == Qmax n m.
Proof.
  intuition.
  apply Qle_lteq in H. destruct H.
  apply Q.max_unicity; auto.
  apply Q.max_unicity. right.
  split.
  rewrite H. apply Qle_refl. rewrite H. auto.
  apply Q.max_unicity; auto.
Qed.


Lemma Qopp_lt_compat (a b:Q) :
  a < b ->
  -b < -a.
Proof.
  intros.
  destruct (Qlt_le_dec (-b) (-a)); auto.
  apply Qopp_le_compat in q.
  rewrite (Qopp_involutive b) in q.
  rewrite (Qopp_involutive a) in q.
  assert (a < a). apply Qlt_le_trans with b; auto.
  exfalso. red in H0. omega.
Qed.


Lemma Qmult_lt_compat' a b x y :
  0 < a /\ a <= x ->
  y < b /\ b <= 0 ->
  x * y < a * b.
Proof.
  intuition.
  rewrite <- (Qopp_involutive (x*y)).
  rewrite <- (Qopp_involutive (a*b)).
  apply Qopp_lt_compat.
  apply Qle_lt_trans with (a * (-b)).
  ring_simplify. apply Qle_refl.
  apply Qlt_le_trans with (x * (-y)).
  apply Qmult_lt_compat.
  split; auto.
  split.
  apply Qle_trans with (-0).
  compute. discriminate.
  apply Qopp_le_compat; auto.
  apply Qopp_lt_compat; auto.
  ring_simplify. apply Qle_refl.
Qed.

Lemma Qmult_lt_compat'' a b x y :
  x <= a /\ a < 0 ->
  y < b /\ b <= 0 ->
  a * b < x * y.
Proof.
  intuition.
  rewrite <- (Qopp_involutive (x*y)).
  rewrite <- (Qopp_involutive (a*b)).
  apply Qopp_lt_compat.
  apply Qle_lt_trans with ((-x) * y).
  ring_simplify. apply Qle_refl.
  apply Qlt_le_trans with ((-a) * b).
  apply Qmult_lt_compat'; auto.
  split.
  apply Qle_lt_trans with (-0).
  compute. discriminate.
  apply Qopp_lt_compat; auto.
  apply Qopp_le_compat; auto.
  ring_simplify. apply Qle_refl.
Qed.

Lemma Qmult_lt0 : forall (a b:Q),
  0 < a -> 0 < b -> 0 < a*b.
Proof.
  intros.
  apply Qle_lt_trans with (0*b); auto.
  ring_simplify; intuition.
  apply Qmult_lt_compat_r; auto.
Qed.

Lemma Qmult_lt0' : forall (a b:Q),
  a < 0 -> 0 < b -> a*b < 0.
Proof.
  intros.
  apply Qlt_le_trans with (0*b); auto.
  apply Qmult_lt_compat_r; auto.
  ring_simplify. intuition.
Qed.

Lemma Qmult_lt0'' : forall (a b:Q),
  a < 0 -> b < 0 -> 0 < a*b.
Proof.
  intros.
  apply Qlt_le_trans with ( (-a) * (-b)); auto.
  apply Qmult_lt0.
  change 0 with (-0).
  apply Qopp_lt_compat. auto.
  change 0 with (-0).
  apply Qopp_lt_compat. auto.
  rewrite mult_opp_simpl.
  intuition.
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

Section solve_simple_quadratic.
  Variables t s z:Q.

  Hypothesis Hs : 0 <= s.
  
  Hypothesis Hst : s^2 < t.
  Hypothesis Htz : t < z^2.
  Hypothesis Hsz : s < z.

  Let a := (z^2 - s^2) / (z - s).
  Let b := s^2 - t - s*a.
  Let b' := z^2 - t - z*a.

  Let f (x:Q) := a*x + b.

  Let fzero := -b / a.

  Lemma bb' : b == b'.
  Proof.
    unfold b, b'.
    unfold a. field.
    intro.
    assert (z == s).
    apply  (Qplus_inj_r _ _ (-s)). ring_simplify.
    ring_simplify in H. auto.
    apply (Qlt_irrefl (s^2)).
    apply Qlt_trans with t; auto.
    rewrite <- H0. auto.
  Qed.    

  Lemma f_s : f s == s^2 - t.
  Proof.
    unfold f, b, a. ring.
  Qed.    

  Lemma f_z : f z == z^2 - t.
  Proof.
    unfold f. rewrite bb'.
    unfold b', a. ring.
  Qed.    

  Lemma f_0 : f fzero == 0.
  Proof.
    unfold f, fzero. field.
    unfold a. intro.
    assert (~(z - s == 0)).
    intro.
    assert (z == s).
    apply  (Qplus_inj_r _ _ (-s)). ring_simplify.
    ring_simplify in H0; auto.
    apply (Qlt_irrefl (s^2)).
    apply Qlt_trans with t; auto.
    rewrite <- H1. auto.
    rewrite <- (Qmult_inj_r _ _ (z-s)) in H; auto.
    field_simplify in H. 2: contradiction.
    assert (z^2 == s^2).
    apply  (Qplus_inj_r _ _ (-(s^2))). ring_simplify.
    field_simplify. auto.
    apply (Qlt_irrefl (s^2)).
    apply Qlt_trans with t; auto.
    rewrite <- H1. auto.
  Qed.

  Lemma fa_lt0 : 0 < a.
  Proof.
    unfold a.
    apply Qlt_shift_div_l; auto.
    apply (Qplus_lt_l _ _ s). ring_simplify.
    auto.
    apply (Qplus_lt_l _ _ (s^2)). ring_simplify.
    apply Qlt_trans with t; auto.
  Qed.

  Lemma s_fzero : s < fzero.
  Proof.
    unfold fzero.
    unfold b.
    apply Qlt_shift_div_l; auto.
    apply fa_lt0.
    rewrite <- (Qplus_lt_l _ _ (-s*a)). ring_simplify. 
    rewrite <- (Qplus_lt_l _ _ (s^2)). ring_simplify. 
    auto.
  Qed.

  Lemma fzero_z : fzero < z.
  Proof.
    unfold fzero.
    rewrite bb'.
    unfold b'.
    apply Qlt_shift_div_r; auto.
    apply fa_lt0.
    rewrite <- (Qplus_lt_l _ _ (-z*a)). ring_simplify. 
    rewrite <- (Qplus_lt_l _ _ (z^2)). ring_simplify. 
    auto.
  Qed.
    
  Lemma fsz : forall x, s < x /\ x < z -> x^2 < f x + t.
  Proof.
    intros. destruct H.
    unfold f.
    rewrite bb'.
    unfold b'.
    ring_simplify.
    unfold a. field_simplify.
    apply Qlt_shift_div_l; auto.
    rewrite <- (Qplus_lt_l _ _ s). ring_simplify. auto.
    field_simplify.    
    rewrite <- (Qplus_lt_l _ _ ((z^2)*s)). field_simplify.
    rewrite <- (Qplus_lt_l _ _ (-(z*(s^2)))). field_simplify.
    apply Qle_lt_trans with ((x^2 + z*s)*(z - s)).
    field_simplify. apply Qle_refl.
    apply Qlt_le_trans with ((x*(z+s))*(z-s)).
    2: field_simplify; apply Qle_refl.
    rewrite (Qmult_comm _ (z-s)).
    rewrite (Qmult_comm _ (z-s)).
    apply Qmult_lt_compat.
    split.
    rewrite <- (Qplus_lt_l _ _ s). ring_simplify.
    auto.
    apply Qle_refl.
    split.
    apply (Qplus_le_compat 0 (x^2) 0 (z*s)).
    apply (Qmult_le_compat 0 0 x x); intuition.
    apply Qle_trans with s; intuition.
    apply Qle_trans with s; intuition.
    apply (Qmult_le_compat 0 0 z s); intuition.
    apply Qle_trans with s; intuition.
    ring_simplify.
    rewrite <- (Qplus_lt_l _ _ (- (x^2))). ring_simplify.
    rewrite <- (Qplus_lt_l _ _ (- (x*s))). ring_simplify.
    apply Qle_lt_trans with
       ((z-x)*s).
    ring_simplify; apply Qle_refl.
    apply Qlt_le_trans with
       ((z-x)*x).
    2: ring_simplify; apply Qle_refl.
    apply Qmult_lt_compat; intuition.
    rewrite <- (Qplus_lt_l _ _ x). ring_simplify. auto.
    intro.
    apply (Qlt_irrefl s).
    apply Qlt_trans with x; auto.
    apply Qlt_le_trans with z; auto.
    rewrite <- (Qplus_le_l _ _ (-s)). ring_simplify.
    rewrite <- H1. ring_simplify. apply Qle_refl.
  Qed.

  Lemma improve_quadratic_lower_bound : exists s', s < s' /\ s'^2 < t.
  Proof.
    exists fzero.
    split. apply s_fzero.
    apply Qlt_le_trans with (f fzero + t).
    apply fsz. split.
    apply s_fzero. apply fzero_z.
    rewrite f_0.
    ring_simplify. apply Qle_refl.
  Qed.    
End solve_simple_quadratic.

Lemma Qsolve_mult_quadratic (q ε:Q) :
  1 <= q -> 0 < ε ->
    exists γ, 0 < γ /\ γ^2 + (2#1)*q*γ < ε.
Proof.
  intros.
  assert (0 < q).
  apply Qlt_le_trans with 1; auto.
  compute. auto.
  destruct (improve_quadratic_lower_bound (q^2 + ε) q (q+ε)) as [r [??]]; auto.
  intuition.
  rewrite <- (Qplus_lt_l _ _ (-q^2)).
  ring_simplify. auto.
  ring_simplify.
  rewrite <- (Qplus_lt_l _ _ (-(q^2))). ring_simplify.
  apply Qlt_le_trans with ( (2#1)*ε + ε^2).
  apply Qle_lt_trans with ( ε + 0 ).
  ring_simplify. apply Qle_refl.
  apply (Qplus_lt_le_compat).
  rewrite <- (Qplus_lt_l _ _ (-ε)). ring_simplify. auto.
  apply Qlt_le_weak.
  apply Qmult_lt0; auto.
  apply Qplus_le_compat.
  apply Qmult_le_compat; intuition.
  apply (Qmult_le_compat (2#1) 1 (2#1) q); intuition.
  apply Qle_refl.
  apply Qle_lt_trans with (0+q).
  ring_simplify. apply Qle_refl.
  rewrite (Qplus_comm q ε).
  apply Qplus_lt_le_compat; intuition.

  exists (r - q). split.
  rewrite <- (Qplus_lt_l _ _ (q)). ring_simplify. auto.
  ring_simplify.
  rewrite <- (Qplus_lt_l _ _ (q^2)). ring_simplify.
  auto.
Qed.


Section ratint_mult_ind.
  Variable (P:rational_interval -> rational_interval -> rational_interval -> Prop).

  Hypothesis Hsymm :
    forall r1 r2,
      P r1 r2 (rint_mult r1 r2) ->
      P r2 r1 (rint_mult r2 r1).

  Hypothesis Hopp :
    forall r1 r2,
      P (rint_opp r1) (rint_opp r2) (rint_mult (rint_opp r1) (rint_opp r2)) ->
      P r1 r2 (rint_mult r1 r2).

  Hypothesis Hcase1 :
    forall x1 x2 y1 y2 z1 z2 Hx Hy Hz,
      let r1 := RatInt x1 x2 Hx in
      let r2 := RatInt y1 y2 Hy in
      let r3 := RatInt z1 z2 Hz in

      0 < x1 -> 0 < y1 ->
      z1 == x1*y1 ->
      z2 == x2*y2 ->
      P r1 r2 r3.

  Hypothesis Hcase2 :
    forall x1 x2 y1 y2 z1 z2 Hx Hy Hz,
      let r1 := RatInt x1 x2 Hx in
      let r2 := RatInt y1 y2 Hy in
      let r3 := RatInt z1 z2 Hz in

      0 < x1 -> y1 <= 0 <= y2 ->
      z1 == y1 * x2 ->
      z2 == x2 * y2 ->
      P r1 r2 r3.

  Hypothesis Hcase3 :
    forall x1 x2 y1 y2 z1 z2 Hx Hy Hz,
      let r1 := RatInt x1 x2 Hx in
      let r2 := RatInt y1 y2 Hy in
      let r3 := RatInt z1 z2 Hz in

      0 < x1 -> y2 < 0 ->
      z1 == y1 * x2 ->
      z2 == x1 * y2 ->
      P r1 r2 r3.

  Hypothesis Hcase4 :
    forall x1 x2 y1 y2 z1 z2 Hx Hy Hz,
      let r1 := RatInt x1 x2 Hx in
      let r2 := RatInt y1 y2 Hy in
      let r3 := RatInt z1 z2 Hz in

      z1 == Qmin (x1*y2) (x2*y1) ->
      z2 == Qmax (x1*y1) (x2*y2) ->

      x1 <= 0 <= x2 -> y1 <= 0 <= y2 ->

      P r1 r2 r3.

  Let rstart x1 x2 y1 y2 := 
            (Qmin (x1 * y1)
            (Qmin (x1 * y2)
            (Qmin (x2 * y1)
                  (x2 * y2)))).

  Let rend x1 x2 y1 y2 :=
            (Qmax (x1 * y1)
            (Qmax (x1 * y2)
            (Qmax (x2 * y1)
                  (x2 * y2)))).

  Lemma case1_start x1 x2 y1 y2 :
    0 < x1 -> x1 <= x2 ->
    0 < y1 -> y1 <= y2 ->
    rstart x1 x2 y1 y2 == x1*y1.
  Proof.    
    intros. unfold rstart.
    apply Q.min_l.
    apply Q.min_case; auto.
    intros. rewrite <- H3; auto.
    apply Qmult_le_compat; intuition.
    apply Q.min_case; auto.
    intros. rewrite <- H3. auto.
    apply Qmult_le_compat; intuition.
    apply Qmult_le_compat; intuition.
  Qed.

  Lemma case1_end x1 x2 y1 y2 :
    0 < x1 -> x1 <= x2 ->
    0 < y1 -> y1 <= y2 ->
    rend x1 x2 y1 y2 == x2*y2.
  Proof.
    intros. unfold rend.
    repeat rewrite Q.max_assoc.
    apply Q.max_r.
    apply Q.max_case; auto.
    intros. rewrite <- H3; auto.
    apply Q.max_case; auto.
    intros. rewrite <- H3; auto.
    apply Qmult_le_compat; intuition.
    apply Qmult_le_compat; intuition.
    apply Qle_trans with y1; intuition.
    apply Qmult_le_compat; intuition.
    apply Qle_trans with x1; intuition.
  Qed.

  Lemma case2_start x1 x2 y1 y2 :
    0 < x1 -> x1 <= x2 ->
    y1 <= 0 <= y2 ->
    rstart x1 x2 y1 y2 == x2 * y1.
  Proof.
    intros. unfold rstart.
    rewrite (Q.min_comm (x2*y1) (x2*y2)).
    repeat rewrite Q.min_assoc.
    apply Q.min_r.
    apply Q.min_case.
    intros. rewrite <- H2; auto.
    apply Q.min_case.
    intros. rewrite <- H2; auto.
    intros.
    apply Qmult_le_compat'; intuition.
    intros.
    apply Qle_trans with (0*0); auto.
    apply Qmult_le_compat'; intuition.
    apply Qle_trans with x1; intuition.
    apply Qmult_le_compat; intuition.
    intros.
    apply Qle_trans with (0*0); auto.
    apply Qmult_le_compat'; intuition.
    apply Qle_trans with x1; intuition.
    apply Qmult_le_compat; intuition.
    apply Qle_trans with x1; intuition.
  Qed.

  Lemma case2_end x1 x2 y1 y2 :
    0 < x1 -> x1 <= x2 ->
    y1 <= 0 <= y2 ->
    rend x1 x2 y1 y2 == x2 * y2.
  Proof.
    intros. unfold rend.
    repeat rewrite Q.max_assoc.
    apply Q.max_r.
    apply Q.max_case.
    intros. rewrite <- H2; auto.
    apply Q.max_case.
    intros. rewrite <- H2; auto.
    apply Qle_trans with (0*0); auto.
    apply Qmult_le_compat'; intuition.
    apply Qmult_le_compat; intuition.
    apply Qle_trans with x1; intuition.
    apply Qmult_le_compat; intuition.
    apply Qle_trans with (0*0); auto.
    apply Qmult_le_compat'; intuition.
    apply Qle_trans with x1; intuition.
    apply Qmult_le_compat; intuition.
    apply Qle_trans with x1; intuition.
  Qed.

  Lemma case3_start x1 x2 y1 y2 :
    0 < x1 -> x1 <= x2 ->
    y1 <= y2 -> y2 < 0 ->
    rstart x1 x2 y1 y2 == x2 * y1.
  Proof.
    intros. unfold rstart.
    rewrite (Q.min_comm (x2*y1) (x2*y2)).
    repeat rewrite Q.min_assoc.
    apply Q.min_r.
    apply Q.min_case.
    intros. rewrite <- H3; auto.
    apply Q.min_case.
    intros. rewrite <- H3; auto.
    apply Qmult_le_compat'; intuition.
    apply Qle_trans with y2; intuition.
    apply Qmult_le_compat'; intuition.
    apply Qmult_le_compat'; intuition.
    apply Qle_trans with x1; intuition.
  Qed.

  Lemma case3_end x1 x2 y1 y2 :
    0 < x1 -> x1 <= x2 ->
    y1 <= y2 -> y2 < 0 ->
    rend x1 x2 y1 y2 == x1 * y2.
  Proof.
    intros. unfold rend.
    rewrite Q.max_assoc.
    rewrite (Q.max_comm (x1*y1) (x1*y2)).
    rewrite <- Q.max_assoc.
    apply Q.max_l.
    apply Q.max_case.
    intros. rewrite <- H3; auto.
    apply Qmult_le_compat'; intuition.
    apply Q.max_case.
    intros. rewrite <- H3; auto.
    apply Qmult_le_compat'; intuition.
    apply Qmult_le_compat'; intuition.
  Qed.

  Lemma case4_start x1 x2 y1 y2 z : 
      x1 <= 0 <= x2 ->
      y1 <= 0 <= y2 ->
      z == Qmin (x1 * y1) (Qmin (x1 * y2) (Qmin (x2 * y1) (x2 * y2))) ->
      z == Qmin (x1 * y2) (x2*y1).
  Proof.
    intros Hx Hy.
    remember (Qmin (x1*y2) (x2*y1)) as q.
    apply Q.min_case_strong; intros. apply H0. rewrite H; auto.
    generalize H; intro H'.
    apply Q.min_glb_l in H.
    destruct (Qlt_le_dec x1 0).
    rewrite <- (mult_opp_simpl x1 y1) in H.
    rewrite <- (mult_opp_simpl x1 y2) in H.
    apply (Qmult_le_l) in H.
    assert (y1 == y2).
    apply Qle_antisym; auto.
    apply Qle_trans with 0; intuition.
    apply Qopp_le_compat in H.
    rewrite Qopp_involutive in H.
    rewrite Qopp_involutive in H.
    auto.
    subst q. rewrite H0.
    apply min_unicity_le.
    left.
    split.
    rewrite <- H1.
    assert (y1 == 0).
    apply Qle_antisym; intuition.
    rewrite H1; auto.
    rewrite H2.
    ring_simplify. apply Qle_refl.
    rewrite H1; intuition.
    rewrite <- (Qplus_lt_l _ _ x1). ring_simplify. auto.
    assert (x1 == 0).
    apply Qle_antisym; intuition.
    rewrite H0. subst q.
    apply min_unicity_le.
    right.
    split.
    rewrite H1. ring_simplify.
    apply (Qmult_le_compat' 0 0 x2 y1); intuition.
    apply Q.min_glb_r in H'.
    apply Q.min_glb_l in H'.
    rewrite H1 in H'.
    rewrite H1. ring_simplify.
    ring_simplify in H'.
    apply Qle_antisym; auto.
    rewrite Qmult_comm.
    apply (Qmult_le_compat' 0 0 x2 y1); intuition.
    cut (z <= x1*y1).
    2: rewrite H0; auto.
    clear H.
    revert H0.
    apply Q.min_case_strong; intros. apply H0; auto. rewrite H; auto.
    rewrite H0.
    rewrite Heqq.
    apply min_unicity_le.
    left; split; auto.
    apply Q.min_glb_l in H. auto.
    reflexivity.
    cut (z <= x1*y2).
    2: rewrite H0; auto.
    clear H.
    revert H0.
    apply Q.min_case_strong; intros. apply H0; auto. rewrite H; auto.
    subst q.
    rewrite H0.
    apply min_unicity_le.
    right; split; auto.
    rewrite H0 in H2. auto.
    reflexivity.
    subst q.
    destruct Hx.
    apply Qle_lteq in H4.
    destruct H4.
    apply (Qmult_le_l) in H; auto.
    assert (y1 == y2).
    apply Qle_antisym; auto. 
    apply Qle_trans with 0; intuition.
    assert (y1 == 0).
    apply Qle_antisym; intuition.
    rewrite H5; auto.
    apply min_unicity_le.
    left. rewrite H0.
    rewrite <- H5. rewrite H6.
    split. ring_simplify. apply Qle_refl.
    ring.
    rewrite H0 in H2.
    rewrite <- H4 in H2.
    ring_simplify in H2.
    apply min_unicity_le.
    right. split.
    rewrite <- H4.
    ring_simplify.
    rewrite Qmult_comm. auto.
    rewrite H0. rewrite <- H4.
    ring.
  Qed.
    
  Lemma case4_end x1 x2 y1 y2 z : 
    x1 <= 0 <= x2 ->
    y1 <= 0 <= y2 ->

    z == Qmax (x1 * y1) (Qmax (x1 * y2) (Qmax (x2 * y1) (x2 * y2))) ->
    z == Qmax (x1 * y1) (x2 * y2).
  Proof.
    intros Hx Hy.
    remember (Qmax (x1*y1) (x2*y2)) as q.
    apply Q.max_case_strong; auto. intros. apply H0. rewrite H; auto.
    intro. subst q. intros.
    apply Q.max_lub_r in H.
    apply Q.max_lub_r in H.
    apply max_unicity_le.
    right; split; auto.
    intros.
    cut (x1*y1 <= z).
    2: rewrite H0; auto.
    clear H.
    revert H0.
    apply Q.max_case_strong; intros. apply H0; auto. rewrite H; auto.
    rewrite H0 in H1.
    apply Q.max_lub_r in H.

    destruct (Qlt_le_dec 0 y2).
    apply (Qmult_le_r) in H; auto.
    assert (x1 == x2).
    apply Qle_antisym; auto.
    apply Qle_trans with 0; intuition.
    subst q.
    apply max_unicity_le.
    left.
    split.
    rewrite <- H2; auto.
    rewrite H0.
    rewrite H2; auto. reflexivity.
    assert (y2 == 0).
    apply Qle_antisym; auto.
    destruct Hy; auto.
    subst q.
    rewrite H2 in H1.
    ring_simplify in H1.
    apply max_unicity_le.
    left.
    rewrite H0. rewrite H2. split.
    ring_simplify. auto.
    ring.
    cut (x1*y2 <= z). 2: rewrite H0; auto.
    clear H.
    revert H0.
    apply Q.max_case_strong; intros. apply H0; auto. rewrite H; auto.
    subst q.
    destruct (Qlt_le_dec 0 x2).
    apply (Qmult_le_l) in H; auto.
    assert (y1 == y2).
    apply Qle_antisym; auto.
    apply Qle_trans with 0; intuition.
    apply max_unicity_le.
    left. rewrite <- H3.
    split; auto.
    rewrite H0 in H2.
    rewrite H3 in H2; auto.
    rewrite H3. auto.
    assert (x2 == 0).
    apply Qle_antisym; auto. destruct Hx; auto.
    apply max_unicity_le.
    rewrite H0 in H2.
    rewrite H3 in H2.
    ring_simplify in H2.
    rewrite H3.
    left. split.
    ring_simplify.
    rewrite H0 in H1.
    rewrite H3 in H1.
    ring_simplify in H1.
    auto.
    rewrite H0.
    rewrite H3.
    ring.
    subst q.
    apply max_unicity_le.
    left.
    rewrite H0 in H2.
    split; auto.
    rewrite H0 in H1. auto.
  Qed.
  
  Lemma rint_mult_ind :
    forall r1 r2, P r1 r2 (rint_mult r1 r2).
  Proof.
    intros [x1 x2 Hx] [y1 y2 Hy].

    destruct (Qlt_le_dec 0 x1).
    destruct (Qlt_le_dec 0 y1).
    apply Hcase1; simpl; auto.
    apply case1_start; auto.
    apply case1_end; auto.
    
    destruct (Qlt_le_dec y2 0).
    apply Hcase3; simpl; auto.
    rewrite (Qmult_comm y1).
    apply case3_start; auto.
    apply case3_end; auto.

    apply Hcase2; simpl; auto.
    rewrite (Qmult_comm y1).
    apply case2_start; auto.
    apply case2_end; auto.
    
    destruct (Qlt_le_dec x2 0).
    destruct (Qlt_le_dec 0 y1).
    apply Hsymm. apply Hcase3; simpl; auto.
    rewrite (Qmult_comm x1 y2).
    apply case3_start; auto.
    apply case3_end; auto.

    destruct (Qlt_le_dec y2 0).
    apply Hopp. apply Hcase1; simpl; auto.
    rewrite <- (Qplus_lt_l _ _ (x2)). ring_simplify. auto.
    rewrite <- (Qplus_lt_l _ _ (y2)). ring_simplify. auto.
    apply case1_start; auto.
    rewrite <- (Qplus_lt_l _ _ (x2)). ring_simplify. auto.
    apply Qopp_le_compat; auto.
    rewrite <- (Qplus_lt_l _ _ (y2)). ring_simplify. auto.
    apply Qopp_le_compat; auto.
    apply case1_end; auto.
    rewrite <- (Qplus_lt_l _ _ (x2)). ring_simplify. auto.
    apply Qopp_le_compat; auto.
    rewrite <- (Qplus_lt_l _ _ (y2)). ring_simplify. auto.
    apply Qopp_le_compat; auto.
  
    apply Hopp. apply Hcase2; simpl.
    rewrite <- (Qplus_lt_l _ _ (x2)). ring_simplify. auto.
    split.
    rewrite <- (Qplus_le_l _ _ (y2)). ring_simplify. auto.
    rewrite <- (Qplus_le_l _ _ (y1)). ring_simplify. auto.
    rewrite (Qmult_comm (-y2) (-x1)).
    apply case2_start; auto.
    rewrite <- (Qplus_lt_l _ _ (x2)). ring_simplify. auto.
    apply Qopp_le_compat; auto.
    split.
    rewrite <- (Qplus_le_l _ _ (y2)). ring_simplify. auto.
    rewrite <- (Qplus_le_l _ _ (y1)). ring_simplify. auto.
    apply case2_end.
    rewrite <- (Qplus_lt_l _ _ (x2)). ring_simplify. auto.
    apply Qopp_le_compat; auto.
    split.
    rewrite <- (Qplus_le_l _ _ (y2)). ring_simplify. auto.
    rewrite <- (Qplus_le_l _ _ (y1)). ring_simplify. auto.
    
    destruct (Qlt_le_dec 0 y1).
    apply Hsymm. apply Hcase2; simpl; auto.
    rewrite (Qmult_comm x1 y2).
    apply case2_start; auto.
    apply case2_end; auto.

    destruct (Qlt_le_dec y2 0).
    apply Hsymm. apply Hopp.
    apply Hcase2; simpl; auto.
    rewrite <- (Qplus_lt_l _ _ (y2)). ring_simplify. auto.
    split.
    rewrite <- (Qplus_le_l _ _ (x2)). ring_simplify. auto.
    rewrite <- (Qplus_le_l _ _ (x1)). ring_simplify. auto.
    rewrite (Qmult_comm (-x2) (-y1)).
    apply case2_start; auto.
    rewrite <- (Qplus_lt_l _ _ (y2)). ring_simplify. auto.
    apply Qopp_le_compat; auto.
    split.
    rewrite <- (Qplus_le_l _ _ (x2)). ring_simplify. auto.
    rewrite <- (Qplus_le_l _ _ (x1)). ring_simplify. auto.
    apply case2_end.
    rewrite <- (Qplus_lt_l _ _ (y2)). ring_simplify. auto.
    apply Qopp_le_compat; auto.
    split.
    rewrite <- (Qplus_le_l _ _ (x2)). ring_simplify. auto.
    rewrite <- (Qplus_le_l _ _ (x1)). ring_simplify. auto.

    apply Hcase4; simpl; auto.
    apply case4_start; intuition.
    apply case4_end; intuition.
  Qed.  
End ratint_mult_ind.


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

    Hypothesis case1_q : x1 * y1 <= q <= x2 * y2.

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
      rewrite <- H3 at 2. auto.
      red in H4. omega.

      destruct (Qlt_le_dec x1 (q/y2)).
      exists (q/y2). exists y2.
      intuition.
      apply Qle_shift_div_r; auto.
      apply Qlt_le_trans with y1; auto.
      rewrite Qmult_comm.
      rewrite Qmult_div_r; intuition.
      assert (0 < 0). 
      rewrite <- H3 at 2. 
      apply Qlt_le_trans with y1; intuition.
      red in H4. omega.

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
      rewrite (Qmult_comm) in H3.
      rewrite Qmult_div_r in H3; intuition.
      assert (0 < 0).
      apply Qlt_le_trans with y1; intuition.
      rewrite <- H4. auto.
      red in H5. omega.
      assert (x1 * y2 <= x1 * (q / x1)).
      apply Qmult_le_compat; intuition.
      apply Qle_trans with y1; intuition.
      rewrite Qmult_div_r in H3; intuition.
      assert (0 < 0).
      rewrite <- H4 at 2. auto.
      red in H5. omega.
    Qed.
  End case1.

  Section case2.
    Hypothesis Hx : 0 < x1.
    Hypothesis Hy : y1 <= 0 <= y2.

    Hypothesis case2_q : y1 * x2 <= q <= x2 * y2.
 
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
      rewrite H5. apply Qle_refl.
      red in H6. omega.
    Qed.
  End case2.

  Section case3.
    Hypothesis Hx : 0 < x1.
    Hypothesis Hy : y2 < 0.

    Hypothesis case3_q : y1 * x2 <= q <= x1 * y2.

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
      rewrite <- H3 at 2; auto.
      
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
      rewrite <- H3 at 2; auto.
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
      rewrite <- H4 at 1. auto.
      field_simplify; auto.
      field_simplify; auto.
      field_simplify; auto.
      reflexivity.
    Qed.
  End case3.

  Section case4.
    Hypothesis Hx : x1 <= 0 <= x2.
    Hypothesis Hy : y1 <= 0 <= y2.

    Hypothesis case4_hi : (q <= x1*y1) \/ (q <= x2*y2).
    Hypothesis case4_low : (x1*y2 <= q) \/ (x2*y1 <= q).

    Lemma case4 : exists q1 q2, x1 <= q1 <= x2 /\ y1 <= q2 <= y2 /\ q == q1 * q2.
    Proof.
      clear HQ.
      destruct case4_low; destruct case4_hi;
        clear case4_low case4_hi.
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

Lemma rint_mult_opp' r1 r2 q :
  in_interval q (rint_mult (rint_opp r1) (rint_opp r2)) ->
  in_interval q (rint_mult r1 r2).
Proof.
  intros.
  apply rint_mult_opp in H.
  red in H. red.
  unfold rint_opp in H.
  simpl in H.
  repeat rewrite (Qopp_involutive) in H.
  auto.
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
  apply rint_mult_ind.

  simpl; intuition.
  destruct H0 as [q1 [q2 [?[??]]]].
  apply rint_mult_swap. auto.
  exists q2. exists q1. intuition.
  rewrite Qmult_comm; auto.
  apply rint_mult_swap. apply H1.
  destruct H as [q1 [q2 [?[??]]]].
  exists q2. exists q1. intuition.
  rewrite Qmult_comm; auto.

  simpl; intuition.
  destruct H0 as [q1 [q2 [?[??]]]].
  apply rint_mult_opp. auto.
  exists (-q1). exists (-q2). intuition.
  apply rint_opp_correct.
  red. rewrite (Qopp_involutive). auto.
  apply rint_opp_correct.
  red. rewrite (Qopp_involutive). auto.
  rewrite mult_opp_simpl. auto.
  apply rint_mult_opp'. apply H1.
  destruct H as [q1 [q2 [?[??]]]].
  exists (-q1), (-q2).
  intuition.
  apply rint_opp_correct; auto.
  apply rint_opp_correct; auto.
  rewrite mult_opp_simpl. auto.

  simpl; intros. split; intros.
  red in H3; simpl in *.
  apply case1; simpl; intuition.
  rewrite <- H1; auto.
  rewrite <- H2; auto.
  unfold in_interval in *; simpl in *.
  destruct H3 as [q1 [q2 [?[??]]]].
  rewrite H5. rewrite H1. rewrite H2.
  split.
  apply Qmult_le_compat; intuition.
  apply Qmult_le_compat; intuition.
  apply Qle_trans with x1; intuition.
  apply Qle_trans with y1; intuition.

  simpl; intros. split; intros.
  red in H3; simpl in *.
  apply case2; simpl; intuition.
  rewrite <- H1; auto.
  rewrite <- H2; auto.
  unfold in_interval in *; simpl in *.
  destruct H3 as [q1 [q2 [?[??]]]].
  rewrite H5. rewrite H1. rewrite H2.
  split.
  rewrite (Qmult_comm y1 x2).
  destruct (Qlt_le_dec 0 q2).
  apply Qle_trans with (0*0).
  apply Qmult_le_compat'; intuition.
  apply Qle_trans with x1; intuition.
  apply Qmult_le_compat; intuition.
  apply Qle_trans with x1; intuition.
  apply Qmult_le_compat'; intuition.
  apply Qle_trans with x1; intuition.
  
  destruct (Qlt_le_dec 0 q2).
  apply Qmult_le_compat; intuition.
  apply Qle_trans with x1; intuition.
  apply Qle_trans with (0*0).
  apply Qmult_le_compat'; intuition.
  apply Qle_trans with x1; intuition.
  apply Qmult_le_compat; intuition.
  apply Qle_trans with x1; intuition.

  simpl; intros. split; intros.
  red in H3; simpl in *.
  unfold in_interval; simpl.
  apply case3; simpl; intuition.
  rewrite <- H1; auto.
  rewrite <- H2; auto.
  unfold in_interval in *; simpl in *.
  destruct H3 as [q1 [q2 [?[??]]]].
  rewrite H5. rewrite H1. rewrite H2.
  split.

  rewrite (Qmult_comm y1 x2).
  apply Qmult_le_compat'; intuition.
  apply Qle_trans with x1; intuition.
  apply Qle_trans with y2; intuition.
  apply Qmult_le_compat'; intuition.
  
  simpl; intros.
  unfold in_interval; simpl.
  split; intros.
  apply case4; auto.
  destruct H3.
  revert H4.
  rewrite H0.
  apply Q.max_case; auto.
  intros. apply H5; auto. rewrite H4; auto.
  destruct H3. 
  revert H3. rewrite H.
  apply Q.min_case; auto.
  intros. apply H5. rewrite H3; auto.
  
  destruct H3 as [q1 [q2 [?[??]]]].
  rewrite H5. split.
  rewrite H.
  apply Q.min_case_strong; intros.
  rewrite <- H6; auto.
  destruct (Qlt_le_dec q1 0).
  destruct (Qlt_le_dec q2 0).
  apply Qle_trans with (0*0).
  rewrite (Qmult_comm x1 y2).
  apply Qmult_le_compat'; intuition.
  apply Qmult_le_compat''; intuition.
  rewrite (Qmult_comm x1 y2).
  rewrite (Qmult_comm q1 q2).
  apply Qmult_le_compat'; intuition.
  destruct (Qlt_le_dec q2 0).
  apply Qle_trans with (x2*y1); auto.
  apply Qmult_le_compat'; intuition.  
  rewrite (Qmult_comm x1 y2).
  rewrite (Qmult_comm q1 q2).
  apply Qle_trans with (0*0).
  apply Qmult_le_compat'; intuition.  
  apply Qmult_le_compat; intuition.  
  
  destruct (Qlt_le_dec q1 0).
  destruct (Qlt_le_dec q2 0).
  apply Qle_trans with (0*0).
  apply Qmult_le_compat'; intuition.
  apply Qmult_le_compat''; intuition.
  apply Qle_trans with (x1*y2); auto.
  rewrite (Qmult_comm x1 y2).
  rewrite (Qmult_comm q1 q2).
  apply Qmult_le_compat'; intuition.
  destruct (Qlt_le_dec q2 0).
  apply Qmult_le_compat'; intuition.  
  apply Qle_trans with (0*0).
  apply Qmult_le_compat'; intuition.  
  apply Qmult_le_compat; intuition.  

  rewrite H0.
  apply Q.max_case_strong; intros.
  rewrite <- H6; auto.

  destruct (Qlt_le_dec q1 0).
  destruct (Qlt_le_dec q2 0).
  apply Qmult_le_compat''; intuition.
  apply Qle_trans with (0*0).
  rewrite (Qmult_comm q1 q2).
  apply Qmult_le_compat'; intuition.  
  apply Qmult_le_compat''; intuition.  
  destruct (Qlt_le_dec q2 0).
  apply Qle_trans with (0*0).
  apply Qmult_le_compat'; intuition.  
  apply Qmult_le_compat''; intuition.  
  apply Qle_trans with (x2*y2); auto.
  apply Qmult_le_compat; intuition.  
  
  destruct (Qlt_le_dec q1 0).
  destruct (Qlt_le_dec q2 0).
  apply Qle_trans with (x1*y1); auto.
  apply Qmult_le_compat''; intuition.
  apply Qle_trans with (0*0).
  rewrite (Qmult_comm q1 q2).
  apply Qmult_le_compat'; intuition.  
  apply Qmult_le_compat; intuition.  
  destruct (Qlt_le_dec q2 0).
  apply Qle_trans with (0*0).
  apply Qmult_le_compat'; intuition.  
  apply Qmult_le_compat; intuition.  
  apply Qmult_le_compat; intuition.  
Qed.


Lemma in_interior_alt q r :
  in_interior q r <-> in_interval q r /\ ~q == rint_start r /\ ~q == rint_end r. 
Proof.
  split; intros.
  destruct H.
  split.
  red; intuition.
  split; intro.
  rewrite H1 in H.
  apply (Qlt_irrefl (rint_start r)); auto.
  rewrite H1 in H0.
  apply (Qlt_irrefl (rint_end r)); auto.
  destruct H as [?[??]]. destruct H.
  split.
  apply Qle_lteq in H.
  destruct H; auto. elim H0. symmetry; auto.
  apply Qle_lteq in H2.
  destruct H2; auto. elim H1. auto.
Qed.

Lemma rint_mult_interior_swap r1 r2 q :
  in_interior q (rint_mult r1 r2) ->
  in_interior q (rint_mult r2 r1).
Proof.
  intros.
  apply in_interior_alt in H.
  apply in_interior_alt.
  intuition.
  apply rint_mult_swap; auto.
  apply H.
  simpl in H1.
  repeat rewrite (Qmult_comm (rint_start r2)) in H1.
  repeat rewrite (Qmult_comm (rint_end r2)) in H1.
  rewrite (Q.min_assoc (rint_end r1 * rint_start r2)) in H1.
  rewrite (Q.min_comm  (rint_end r1 * rint_start r2)) in H1.
  rewrite <- Q.min_assoc in H1.
  auto.
  apply H2.
  simpl in H1.
  repeat rewrite (Qmult_comm (rint_start r2)) in H1.
  repeat rewrite (Qmult_comm (rint_end r2)) in H1.
  rewrite (Q.max_assoc (rint_end r1 * rint_start r2)) in H1.
  rewrite (Q.max_comm  (rint_end r1 * rint_start r2)) in H1.
  rewrite <- Q.max_assoc in H1.
  auto.
Qed.

Lemma rint_mult_interior_opp r1 r2 q :
  in_interior q (rint_mult r1 r2) ->
  in_interior q (rint_mult (rint_opp r1) (rint_opp r2)).
Proof.
  intros.
  apply in_interior_alt in H.
  apply in_interior_alt.
  intuition.
  apply rint_mult_opp; auto.
  apply H.
  simpl in H1.
  repeat rewrite mult_opp_simpl in H1.
  simpl.
  rewrite Q.min_comm in H1.
  rewrite (Q.min_comm _ (rint_start r1 * rint_start r2)) in H1.
  rewrite  Q.min_assoc in H1.
  rewrite (Q.min_comm _ (rint_start r1 * rint_start r2)) in H1.
  rewrite <- Q.min_assoc in H1.
  rewrite <- Q.min_assoc in H1.
  rewrite (Q.min_assoc (rint_end r1 * rint_start r2)) in H1.
  rewrite (Q.min_comm  (rint_end r1 * rint_start r2)) in H1.
  rewrite <- Q.min_assoc in H1.
  auto.
  apply H2.
  simpl in H1.
  repeat rewrite mult_opp_simpl in H1.
  simpl.
  rewrite Q.max_comm in H1.
  rewrite (Q.max_comm _ (rint_start r1 * rint_start r2)) in H1.
  rewrite  Q.max_assoc in H1.
  rewrite (Q.max_comm _ (rint_start r1 * rint_start r2)) in H1.
  rewrite <- Q.max_assoc in H1.
  rewrite <- Q.max_assoc in H1.
  rewrite (Q.max_assoc (rint_end r1 * rint_start r2)) in H1.
  rewrite (Q.max_comm  (rint_end r1 * rint_start r2)) in H1.
  rewrite <- Q.max_assoc in H1.
  auto.
Qed.


Lemma rint_mult_interior_opp' r1 r2 q :
  in_interior q (rint_mult (rint_opp r1) (rint_opp r2)) ->
  in_interior q (rint_mult r1 r2).
Proof.
  intros.
  apply rint_mult_interior_opp in H.
  red in H. red.
  unfold rint_opp in H.
  simpl in H.
  repeat rewrite (Qopp_involutive) in H.
  auto.
Qed.

Lemma rint_mult_correct_interior r1 r2 q q1 q2 :
  in_interior q1 r1 -> in_interior q2 r2 -> q == q1 * q2 ->
  in_interior q (rint_mult r1 r2).
Proof.
  revert q q1 q2.
  apply rint_mult_ind; unfold in_interior; simpl; intros.
  apply rint_mult_interior_swap.
  apply H with q2 q1; auto.
  rewrite Qmult_comm; auto.
  apply rint_mult_interior_opp'.
  apply H with (-q1) (-q2).
  destruct H0; split; simpl.
  rewrite <- (Qplus_lt_l _ _ (rint_end r0)).
  rewrite <- (Qplus_lt_l _ _ q1).
  ring_simplify. auto.
  rewrite <- (Qplus_lt_l _ _ (rint_start r0)).
  rewrite <- (Qplus_lt_l _ _ q1).
  ring_simplify. auto.
  destruct H1; split; simpl.
  rewrite <- (Qplus_lt_l _ _ (rint_end r3)).
  rewrite <- (Qplus_lt_l _ _ q2).
  ring_simplify. auto.
  rewrite <- (Qplus_lt_l _ _ (rint_start r3)).
  rewrite <- (Qplus_lt_l _ _ q2).
  ring_simplify. auto.
  rewrite mult_opp_simpl. auto.

  rewrite H5.
  rewrite H1.
  rewrite H2.
  split.
  apply Qmult_lt_compat; intuition.
  apply Qmult_lt_compat; intuition.
  apply Qlt_trans with x1; auto.
  apply Qle_trans with y1; intuition.
  rewrite H1.
  rewrite H2.
  rewrite H5.
  split.
  destruct (Qlt_le_dec 0 q2).
  apply Qle_lt_trans with (0*0).
  rewrite (Qmult_comm y1 x2).
  apply Qmult_le_compat'; intuition.
  apply Qle_trans with x1; intuition.
  apply Qmult_lt0; auto.
  apply Qlt_trans with x1; intuition.

  rewrite (Qmult_comm y1 x2).
  apply Qmult_lt_compat'; intuition.
  apply Qlt_trans with x1; auto.

  destruct (Qlt_le_dec 0 q2).
  apply Qmult_lt_compat; intuition.
  apply Qlt_trans with x1; auto.
  apply Qle_lteq in q0.
  destruct q0.
  apply Qlt_le_trans with (0*0).
  rewrite (Qmult_comm q1 q2).
  apply Qmult_lt0'; auto.
  apply Qlt_trans with x1; intuition.
  apply Qmult_le_compat; intuition.
  apply Qle_trans with x1; intuition.
  rewrite H6.
  ring_simplify.
  apply Qmult_lt0.
  apply Qlt_trans with x1; intuition.
  apply Qlt_trans with q1; intuition.
  destruct H4. rewrite H6 in H7. auto.

  rewrite H1. rewrite H2. rewrite H5.
  split.
  rewrite (Qmult_comm y1 x2).
  apply Qmult_lt_compat'.
  intuition.
  apply Qlt_trans with x1; auto.
  intuition.
  apply Qle_trans with y2; intuition.
  apply Qmult_lt_compat'; intuition.
  
  rewrite H. rewrite H0. rewrite H5.
  split.
  apply Q.min_case_strong; intros.
  rewrite <- H6; auto.
  destruct (Qlt_le_dec q1 0); destruct (Qlt_le_dec q2 0).
  apply Qle_lt_trans with (0*0).
  rewrite (Qmult_comm x1 y2).
  apply Qmult_le_compat'; intuition.
  apply Qmult_lt0''; auto.
  apply Qle_lteq in q3.
  destruct q3.
  rewrite (Qmult_comm x1 y2).
  rewrite (Qmult_comm q1 q2).
  apply Qmult_lt_compat'; intuition.
  rewrite <- H7.
  ring_simplify.
  apply Qmult_lt0'.
  apply Qlt_trans with q1; intuition.
  rewrite <- H7 in H4. intuition.
  apply Qle_lt_trans with (x2*y1); auto.
  apply Qle_lteq in q0.
  destruct q0.
  apply Qmult_lt_compat'; intuition.
  rewrite <- H7.
  ring_simplify.
  rewrite (Qmult_comm x2 y1).
  apply Qmult_lt0'.
  apply Qlt_trans with q2; intuition.
  rewrite <- H7 in H3.
  intuition.
  destruct H1.
  apply Qle_lteq in q0. destruct q0.
  apply Qle_lteq in q3. destruct q3.
  apply Qle_lt_trans with (0*0).
  rewrite (Qmult_comm x1 y2).
  apply Qmult_le_compat'; intuition.
  apply Qmult_lt0; auto.
  rewrite <- H9. ring_simplify.
  rewrite <- H9 in H4.
  apply Qle_lt_trans with (x2*y1). auto.
  rewrite (Qmult_comm x2 y1).
  apply Qmult_lt0'; intuition.
  apply Qlt_trans with q1; auto.
  rewrite <- H8 in H3.
  rewrite <- H8. ring_simplify.
  apply Qmult_lt0'; intuition.
  apply Qle_lt_trans with q2; auto.
  
  destruct (Qlt_le_dec q1 0); destruct (Qlt_le_dec q2 0).
  apply Qle_lt_trans with (0*0).
  apply Qmult_le_compat'; intuition.
  apply Qmult_lt0''; auto.
  apply Qle_lteq in q3.
  destruct q3.
  apply Qle_lt_trans with (x1*y2); auto.
  rewrite (Qmult_comm x1 y2).
  rewrite (Qmult_comm q1 q2).
  apply Qmult_lt_compat'; intuition.
  rewrite <- H7.
  ring_simplify.
  apply Qle_lt_trans with (x1*y2); auto.
  apply Qmult_lt0'.
  apply Qlt_trans with q1; intuition.
  rewrite <- H7 in H4. intuition.
  apply Qle_lteq in q0.
  destruct q0.
  apply Qmult_lt_compat'; intuition.
  rewrite <- H7.
  ring_simplify.
  rewrite (Qmult_comm x2 y1).
  apply Qmult_lt0'.
  apply Qlt_trans with q2; intuition.
  rewrite <- H7 in H3.
  intuition.
  destruct H1.
  apply Qle_lteq in q0. destruct q0.
  apply Qle_lteq in q3. destruct q3.
  apply Qle_lt_trans with (0*0).
  apply Qle_trans with (x1*y2); auto.
  rewrite (Qmult_comm x1 y2).
  apply Qmult_le_compat'; intuition.
  apply Qmult_lt0; auto.
  rewrite <- H9. ring_simplify.
  rewrite <- H9 in H4.
  rewrite (Qmult_comm x2 y1).
  apply Qmult_lt0'; intuition.
  apply Qlt_trans with q1; auto.
  rewrite <- H8 in H3.
  rewrite <- H8. ring_simplify.
  apply Qle_lt_trans with (x1*y2); auto.
  apply Qmult_lt0'; intuition.
  apply Qle_lt_trans with q2; auto.

  apply Q.max_case_strong; intros.
  rewrite <- H6; auto.

  destruct (Qlt_le_dec q1 0); destruct (Qlt_le_dec q2 0).
  apply Qmult_lt_compat''; intuition.
  apply Qle_lteq in q3. destruct q3.
  apply Qlt_le_trans with (0*0).
  apply Qmult_lt0'; auto.
  apply Qmult_le_compat''; intuition.
  rewrite <- H7 in H4.
  rewrite <- H7. ring_simplify.
  apply Qmult_lt0''.
  apply Qlt_trans with q1; intuition.
  intuition.
  apply Qle_lteq in q0. destruct q0.
  apply Qlt_le_trans with (0*0).
  rewrite (Qmult_comm q1 q2).
  apply Qmult_lt0'; auto.
  apply Qmult_le_compat''; intuition.
  rewrite <- H7 in H3.
  rewrite <- H7. ring_simplify.
  apply Qmult_lt0''; intuition.
  apply Qlt_trans with q2; intuition.
  apply Qle_lteq in q0.
  destruct q0.
  apply Qlt_le_trans with (x2*y2); auto.
  apply Qmult_lt_compat; intuition.
  rewrite <- H7 in H3.
  rewrite <- H7.
  ring_simplify.
  apply Qlt_le_trans with (x2*y2); auto.
  apply Qmult_lt0; intuition.
  apply Qle_lt_trans with q2; auto.

  destruct (Qlt_le_dec q1 0); destruct (Qlt_le_dec q2 0).
  apply Qlt_le_trans with (x1*y1); auto.
  apply Qmult_lt_compat''; intuition.
  apply Qlt_le_trans with (x1*y1); auto.
  apply Qle_lteq in q3. destruct q3.
  apply Qlt_le_trans with (0*0).
  apply Qmult_lt0'; auto.
  apply Qmult_le_compat''; intuition.
  rewrite <- H7 in H4.
  rewrite <- H7. ring_simplify.
  apply Qmult_lt0''.
  apply Qlt_trans with q1; intuition.
  intuition.
  apply Qle_lteq in q0. destruct q0.
  apply Qlt_le_trans with (0*0).
  rewrite (Qmult_comm q1 q2).
  apply Qmult_lt0'; auto.
  apply Qle_trans with (x1*y1); auto.
  apply Qmult_le_compat''; intuition.
  rewrite <- H7 in H3.
  rewrite <- H7. ring_simplify.
  apply Qlt_le_trans with (x1*y1); auto.
  apply Qmult_lt0''; intuition.
  apply Qlt_trans with q2; intuition.
  apply Qle_lteq in q0.
  destruct q0.
  apply Qmult_lt_compat; intuition.
  rewrite <- H7 in H3.
  rewrite <- H7.
  ring_simplify.
  apply Qmult_lt0; intuition.
  apply Qle_lt_trans with q2; auto.
Qed.
