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
Require Import realdom.

Require Import Qabs.
Require Import Qminmax.


Record convergence_rate :=
  { convg :> N -> Q
  ; convg_decreasing : forall n1 n2, (n1 <= n2)%N -> (convg n1 >= convg n2)%Q
  ; convg_pos : forall n, 0 < convg n
  ; convg_small : forall ε:Q, 0 < ε -> exists n, convg n <= ε
  }.

Program Definition convg_interval (θ:convergence_rate) (n:N) :=
  RatInt (-θ n) (θ n) _.
Next Obligation.
  intros.
  apply Qle_trans with 0%Q.
  rewrite <- (Qplus_le_l _ _ (θ n)). ring_simplify.
  apply Qlt_le_weak. apply convg_pos.
  apply Qlt_le_weak. apply convg_pos.
Qed.

Require Import flat.

Program Definition enumN : enumtype :=
  Enumtype N (fun n => Some n) _ N.eq_dec.
Next Obligation.
  intro x. exists x. auto.
Qed.

Lemma Ndownset (n:N) :
  { l:finset (flat enumN) | forall m:flat enumN, (m < n)%N <-> m ∈ l }.
Proof.
  induction n using N.peano_rect.
  exists nil.
  intuition.
  compute in H. destruct m; discriminate.
  apply nil_elem in H. elim H.
  destruct IHn as [l ?].
  exists (n::l)%list.
  intuition.
  apply N.lt_succ_r in H.
  apply N.le_lteq in H.
  destruct H.
  apply (@cons_elem (flat enumN)).
  right. apply i. auto.
  apply (@cons_elem (flat enumN)).
  left. split; hnf; auto.
  apply N.lt_succ_r.
  apply N.le_lteq.
  apply (@cons_elem (flat enumN)) in H.
  destruct H.
  right.
  destruct H. hnf in H. auto.
  left. apply i. auto.
Qed.  


(**)

  Definition partial_limit (n:N) (x:cut_preord) :=
    forall m, (m <= n)%N -> widen_cut m (seq m) ≤ x.

  Program Definition limit_uppers (n:N) : eset Qpreord :=
    image (Preord.Hom _ _ (Qplus (oneOver2n n)) _)
     (esubset
            (fun q => forall m:flat enumN, m ∈ proj1_sig (Ndownset n) ->
                      exists q', 
                        q' ∈ cut_upper (seq m) /\
                        q' <= q + oneOver2n n + oneOver2n m )
            _
            (cut_upper (seq n))).
  Next Obligation.
    intros. red in H. simpl in H.
    red; simpl. rewrite H. reflexivity.
  Qed.
  Next Obligation.
    intros.
    apply all_finset_semidec.
    intros. destruct H0 as  [q' [??]]. exists q'; split; auto.
    destruct H. hnf in H . subst a0. auto.
    destruct H. hnf in H . subst a0. auto.
admit.
(*
    intro m.
    apply (semidec_ex _ _ (fun a q' => q' ∈ cut_upper (seq m) /\ q' + oneOver2n m <= a)).
    intros x y z [??]. red in H. simpl in H.
    intros [??].
    rewrite H in H2. split; auto.
    apply member_eq with y; auto.
    apply Qpreord_eff.
    intros [a' q']. simpl.
    apply semidec_conj.
    apply semidec_in.
    constructor. apply eff_ord_dec. apply Qpreord_eff.
    apply dec_semidec.
*)
(*
    destruct (Qlt_le_dec (a' + oneOver2n m) q').
    right; intro.
    eapply Qlt_irrefl.
    eapply Qle_lt_trans; eauto.
    left; auto.
*)
  Qed.

    

  Lemma limit_least_partial_limit_upper l : 
    (forall n x, partial_limit n x -> x ≤ l) ->
    limit_upper ⊆ cut_upper l.
  Proof.
    repeat intro.
    unfold limit_upper in H0.
    apply union_axiom in H0.
    destruct H0 as [X [??]].
    destruct H0 as [n ?].
    rewrite H0 in H1. clear X H0.
    unfold limit_uppers in H1.
    apply image_axiom2 in H1.
    destruct H1 as [y [??]]; simpl in *.
    apply esubset_elem in H0.
    destruct H0.
    


  Qed.

  Lemma cut_upper_partial_limit a n :
    a ∈ limit_uppers n ->
    exists x, partial_limit n x /\ a ∈ cut_upper x.
  Proof.
    intros. 
    unfold limit_uppers in H.
    apply image_axiom2 in H. destruct H as [y [??]].
    simpl in H0.
    apply esubset_elem in H.
    destruct H.
    
    assert (exists w:cut,
              (forall ru, ru ∈ cut_upper w <-> 
                          y+oneOver2n n <= ru /\
                          (forall m, (m <= n)%N ->
                              exists q', q' ∈ cut_upper (seq m) /\
                                         q' + oneOver2n m <= ru))
               /\
               (forall rl, rl ∈ cut_lower w ->
                           (forall m, (m <= n)%N ->
                                      (rl + oneOver2n m)%Q ∈ cut_lower (seq m)))).
admit.

    destruct H2 as [w [??]].
    exists w.
    split.
    red; intros.
    split; red; simpl; intros.
    apply image_axiom1'. simpl.
    apply H2 in H5.
    destruct H5.
    destruct (H6 m) as [q' [??]]; auto.
    exists (a0 - oneOver2n m).
    split.
    simpl in *; split; red; simpl; ring.
    apply cut_is_upper with q'; auto.
    apply (Qplus_le_l _ _ (oneOver2n m)).
    ring_simplify. auto.
    apply image_axiom1'.
    simpl.
    exists (a0 + oneOver2n m)%Q.
    split.
    simpl in *; split; red; simpl; ring.
    apply H3; auto.

    apply H2.
    split.
    destruct H0. red in H0. simpl in H0.
    rewrite H0. rewrite Qplus_comm. apply Qle_refl.
    intros.
    apply N.lt_eq_cases in H4. destruct H4.    
    destruct (H1 m) as [q' [??]].
    destruct (Ndownset n); simpl. apply i; auto.
    exists q'. split; auto.
    destruct H0. red in H0. simpl in H0. rewrite H0.
    apply (Qplus_le_l _ _ (- oneOver2n m)).
    ring_simplify.
    eapply Qle_trans. apply H6.
    ring_simplify. apply Qle_refl.
    
    subst n.
    exists y. split; auto.
    destruct H0.
    red in H0. simpl in H0.
    rewrite H0.
    rewrite (Qplus_comm). apply Qle_refl.

    

  Qed.
*)

  Program Definition limit_lowers (n:N) : eset Qpreord :=
    image (Preord.Hom _ _ (Qplus (-oneOver2n n)) _)
     (esubset
            (fun q => forall m:flat enumN, m ∈ proj1_sig (Ndownset n) ->
                      exists q', 
                        q' ∈ cut_lower (seq m) /\
                        q <= q' + oneOver2n m + oneOver2n n)
            _
            (cut_lower (seq n))).
  Next Obligation.
    intros. red; simpl.
    red in H; simpl in H. rewrite H. reflexivity.
  Qed.
  Next Obligation.
    intros.
    apply all_finset_semidec.
    intros. destruct H0 as  [q' [??]]. exists q'; split; auto.
    destruct H. hnf in H . subst a0. auto.
    destruct H. hnf in H . subst a0. auto.
    intro m.    
    apply (semidec_ex _ _ (fun a q' => q' ∈ cut_lower (seq m) /\ a <= q' + oneOver2n m + oneOver2n n )).
    intros x y z [??]. red in H. simpl in H.
    intros [??].
    rewrite H in H2. split; auto.
    apply member_eq with y; auto.
    apply Qpreord_eff.
    intros [a' q']. simpl.
    apply semidec_conj.
    apply semidec_in.
    constructor. apply eff_ord_dec. apply Qpreord_eff.
    apply dec_semidec.
    destruct (Qlt_le_dec (q'  + oneOver2n m  + oneOver2n n) (a')).
    right; intro.
    apply (Qlt_irrefl a').
    eapply Qle_lt_trans; eauto.
    left; auto.
  Qed.


  Definition limit_lower : eset Qpreord :=
    union ( (fun n => Some (limit_lowers n)) : eset (eset Qpreord)).

  
  Program Definition limit : cut :=
    Cut limit_upper limit_lower _ _ _ _.
  Next Obligation.
    simpl; intros.
    apply union_axiom in H.
    apply union_axiom in H0.
    destruct H as [R [??]].
    destruct H0 as [S [??]].
    destruct H as [n ?].
    destruct H0 as [m ?].
    rewrite H in H1.
    rewrite H0 in H2. clear H H0.
    unfold limit_uppers in H1.
    apply image_axiom2 in H1.
    destruct H1 as [y [??]].
    simpl in *.
    destruct H0 as [? _]. red in H0; simpl in H0.
    rewrite H0.
    apply esubset_elem in H.
    destruct H.
    unfold limit_lowers in H2.
    apply image_axiom2 in H2.
    destruct H2 as [y' [??]].
    simpl in *.
    destruct H3 as [? _]. red in H3. simpl in H3. rewrite H3.
    apply esubset_elem in H2.
    destruct H2.
    destruct (N.compare_spec n m).
    subst m.
    apply Qplus_le_compat.
    apply Qle_trans with 0%Q.
    rewrite <- (Qplus_le_l _ _ (oneOver2n n)).
    ring_simplify. apply Qlt_le_weak. apply oneOver2n_pos.
    apply Qlt_le_weak. apply oneOver2n_pos.
    apply cut_proper with (seq n); auto.
    destruct (H4 n) as [q' [??]].
    destruct (Ndownset m); simpl in *.
    apply i; auto.
    rewrite <- (Qplus_le_l _ _ (oneOver2n m)).
    ring_simplify.
    apply Qle_trans with (q' + oneOver2n n + oneOver2n m)%Q. auto.
    rewrite <- (Qplus_le_l _ _ (- (oneOver2n n + oneOver2n m))). ring_simplify.
    apply cut_proper with (seq n); auto.
    destruct (H1 m) as [q' [??]].
    destruct (Ndownset n); simpl in *.
    apply i; auto.
    rewrite <- (Qplus_le_l _ _ (oneOver2n m)).
    ring_simplify.
    apply Qle_trans with q'; auto.
    apply cut_proper with (seq m); auto.
    eapply Qle_trans. apply H7.
    ring_simplify. apply Qle_refl.

    simpl; intros.
    destruct (H5 m0) as [q' [??]]; auto.
    exists q'; split; auto.
    destruct H4. red in H4. simpl in H4.
    rewrite <- H4; auto.
    
    simpl; intros.
    destruct (H3 m0) as [q' [??]]; auto.
    exists q'; split; auto.
    destruct H1. red in H1. simpl in H1.
    rewrite <- H1; auto.
  Qed.
  Next Obligation.
    unfold limit_lower.
    simpl; intros.
    apply union_axiom in H0.
    apply union_axiom.
    destruct H0 as [X [??]].
    exists X. split; auto.
    destruct H0 as [n ?].
    rewrite H0. rewrite H0 in H1.
    unfold limit_lowers in H1.
    unfold limit_lowers.
    apply image_axiom2 in H1.
    destruct H1 as [q [??]]. simpl in *.
    apply image_axiom1'. simpl.
    apply esubset_elem in H1.
    destruct H1.
    exists (q1 + oneOver2n n)%Q.
    split.
    split; red; simpl; ring.
    apply esubset_elem.
    intros.
    destruct (H5 m) as [q' [??]]; auto.
    exists q'.
    split; auto.
    destruct H4.
    red in H4. simpl in H4. rewrite <- H4; auto.
    split.
    apply cut_is_lower with q; auto.
    apply Qle_trans with (q2 + oneOver2n n)%Q.
    apply Qplus_le_compat; auto. apply Qle_refl.
    destruct H2. red in H2; simpl in H2. rewrite H2.
    ring_simplify. apply Qle_refl.
    intros.
    destruct (H3 m) as [q' [??]]; auto.
    exists q'. split; auto.
    apply Qle_trans with q; auto.
    apply Qle_trans with (q2 + oneOver2n n)%Q.
    apply Qplus_le_compat; auto. apply Qle_refl.
    destruct H2. red in H2; simpl in H2. rewrite H2.
    ring_simplify. apply Qle_refl.
    intros.
    destruct (H4 m) as [q' [??]]; auto. exists q'; split; auto.
    destruct H3 as [? _]. red in H3. simpl in H3.
    rewrite <- H3; auto.
  Qed.
  Next Obligation.
    unfold limit_upper.
    simpl; intros.
    apply union_axiom in H0.
    apply union_axiom.
    destruct H0 as [X [??]].
    exists X. split; auto.
    destruct H0 as [n ?].
    rewrite H0. rewrite H0 in H1.
    unfold limit_uppers in H1.
    unfold limit_uppers.
    apply image_axiom2 in H1.
    destruct H1 as [q [??]]. simpl in *.
    apply image_axiom1'. simpl.
    apply esubset_elem in H1.
    destruct H1.
    exists (q2 - oneOver2n n)%Q.
    split.
    split; red; simpl; ring.
    apply esubset_elem.
    intros.
    destruct (H5 m) as [q' [??]]; auto.
    exists q'.
    split; auto.
    destruct H4.
    red in H4. simpl in H4. rewrite <- H4; auto.
    split.
    apply cut_is_upper with q; auto.
    apply Qle_trans with (q1 - oneOver2n n)%Q.
    destruct H2. red in H2; simpl in H2. rewrite H2.
    ring_simplify. apply Qle_refl.
    apply Qplus_le_compat; auto. apply Qle_refl.
    intros.
    destruct (H3 m) as [q' [??]]; auto.
    exists q'. split; auto.
    eapply Qle_trans. apply H6.
    apply (Qplus_le_l _ _ (oneOver2n n)). 
    apply (Qplus_le_l _ _ (oneOver2n m)). 
    apply Qle_trans with (q1 - oneOver2n n)%Q.
    destruct H2. red in H2. simpl in H2. rewrite H2.
    ring_simplify. apply Qle_refl.
    apply Qplus_le_compat; auto. apply Qle_refl.
    intros.
    destruct (H4 m) as [q' [??]]; auto. exists q'; split; auto.
    destruct H3 as [? _]. red in H3. simpl in H3.
    rewrite <- H3; auto.
  Qed.
  Next Obligation.
    unfold limit_upper, limit_lower.
    split; intros [x ?].
    apply union_axiom in H.
    destruct H as [X [??]].
    destruct H as [n ?]. rewrite H in H0.
    unfold limit_uppers in H0.
    apply image_axiom2 in H0.
    destruct H0 as [y [??]]. simpl in *.
    apply esubset_elem in H0. destruct H0.
    assert (exists q', q' ∈ cut_upper (seq 0) /\ q' <= y + oneOver2n 0 + oneOver2n n).
    destruct (N.compare_spec 0 n).
    subst n.
    exists y; split; auto.
    apply Qle_trans with (y+0)%Q.
    ring_simplify; auto. apply Qle_refl.
    rewrite <- Qplus_assoc.
    apply Qplus_le_compat. apply Qle_refl.
    apply Qle_trans with (0+0)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_le_compat; apply Qlt_le_weak; apply oneOver2n_pos.
    destruct (H2 0)%N as [q' [??]].
    destruct (Ndownset n); simpl.
    apply i. auto.
    exists q'; split; auto.
    compute in H3.
    destruct n; discriminate.
    destruct H3 as [q' [??]].
    destruct (cut_nonextended (seq 0)).
    destruct H5 as [z ?]; eauto.
    exists (z  - oneOver2n 0).
    apply union_axiom.
    exists (limit_lowers 0).
    split. exists 0%N. auto.
    unfold limit_lowers.
    apply image_axiom1'.
    simpl.
    exists z. split.
    split; red; simpl in *; ring.
    apply esubset_elem.
      intros.
      destruct (H8 m) as [w [??]]; auto.
      exists w; split; auto.
      destruct H7. red in H7; simpl in H7; rewrite <- H7; auto.
    split; auto.
    intros.
    destruct (Ndownset 0); simpl in *.
    apply i in H7.
    destruct m; compute in H7; discriminate.
      intros.
      destruct (H3 m) as [w [??]]; auto.
      exists w; split; auto.
      destruct H2. red in H2; simpl in H2; rewrite <- H2; auto.

    apply union_axiom in H.
    destruct H as [X [??]].
    destruct H as [n ?]. rewrite H in H0.
    unfold limit_lowers in H0.
    apply image_axiom2 in H0.
    destruct H0 as [y [??]]. simpl in *.
    apply esubset_elem in H0. destruct H0.
    assert (exists q', q' ∈ cut_lower (seq 0) /\ y <= q' + oneOver2n 0 + oneOver2n n).
    destruct (N.compare_spec 0 n).
    subst n.
    exists y; split; auto.
    apply Qle_trans with (y+0)%Q.
    ring_simplify; auto. apply Qle_refl.
    rewrite <- Qplus_assoc.
    apply Qplus_le_compat. apply Qle_refl.
    apply Qle_trans with (0+0)%Q.
    ring_simplify. apply Qle_refl.
    apply Qplus_le_compat; apply Qlt_le_weak; apply oneOver2n_pos.
    destruct (H2 0)%N as [q' [??]].
    destruct (Ndownset n); simpl.
    apply i. auto.
    exists q'; split; auto.
    compute in H3.
    destruct n; discriminate.
    destruct H3 as [q' [??]].
    destruct (cut_nonextended (seq 0)).
    destruct H6 as [z ?]; eauto.
    exists (z  + oneOver2n 0)%Q.
    apply union_axiom.
    exists (limit_uppers 0).
    split. exists 0%N. auto.
    unfold limit_uppers.
    apply image_axiom1'.
    simpl.
    exists z. split.
    split; red; simpl in *; ring.
    apply esubset_elem.
      intros.
      destruct (H8 m) as [w [??]]; auto.
      exists w; split; auto.
      destruct H7. red in H7; simpl in H7; rewrite <- H7; auto.
    split; auto.
    intros.
    destruct (Ndownset 0); simpl in *.
    apply i in H7.
    destruct m; compute in H7; discriminate.
      intros.
      destruct (H3 m) as [w [??]]; auto.
      exists w; split; auto.
      destruct H2. red in H2; simpl in H2; rewrite <- H2; auto.
  Qed.


  Lemma cut_lower_partial_limit a n :
    a ∈ limit_lowers n ->
    exists x, partial_limit n x /\ a ∈ cut_lower x.
  Admitted.  

  Lemma limit_least_partial_limit l : 
    (forall n x, partial_limit n x -> x ≤ l) ->
    limit ≤ l.
  Proof.
    intros. split; red; simpl; intros.
    unfold limit_upper in H0.
    apply union_axiom in H0.
    destruct H0 as [?[??]].
    destruct H0 as [n ?]. rewrite H0 in H1. clear x H0.
    apply cut_upper_partial_limit in H1.
    destruct H1 as [x [??]].
    destruct (H n x); auto.
    unfold limit_lower in H0.
    apply union_axiom in H0.
    destruct H0 as [?[??]].
    destruct H0 as [n ?]. rewrite H0 in H1. clear x H0.
    apply cut_lower_partial_limit in H1.
    destruct H1 as [x [??]].
    destruct (H n x); auto.
  Qed.

  Lemma limit_partial_limit n x : 
    partial_limit n x -> x ≤ limit.
  Proof.
    intros. split.
    red; simpl; intros.
    red in H.
    unfold limit_upper.
    apply union_axiom.
    exists (limit_uppers n).
    split; simpl. exists n. auto.
    unfold limit_uppers.
    apply image_axiom1'. simpl.
    exists (a - oneOver2n n).
    split.
    split; red; simpl; ring.
    apply esubset_elem.
admit.
    split.
    destruct (H n). apply N.le_refl.
    simpl in H1.
    generalize (H1 a H0).
    intros. apply image_axiom2 in H3.
    destruct H3 as [?[??]]. simpl in *.
    apply member_eq with x0; auto.
    destruct H4. red in H4; simpl in H4.
    split; red; simpl; rewrite H4; ring.
    intros.
    destruct (H m).
    destruct (Ndownset n); simpl in *.
    apply i in H1. 
    apply N.lt_le_incl; auto.
    generalize (H2 a H0); intros.
    simpl in H4.
    apply image_axiom2 in H4.
    destruct H4 as [y [??]].
    simpl in *.
    exists y. split; auto.
    ring_simplify.
    destruct H5 as [??]. red in H5. simpl in H5.
    rewrite H5.
        

  Qed.
  

Section cut_limit.



Section real_limit.
  Variable θ:convergence_rate.
  Variable A:∂PLT.
  Variable f:(A ⊗ flat enumN → PreRealDom)%plt.

  Let P (anr:(prod_preord (prod_preord A (flat enumN)) PreRealDom)) := 
      forall m:flat enumN, m ∈ proj1_sig (Ndownset (snd (fst anr))) ->
         exists r', 
           (fst (fst anr),m,r') ∈ PLT.hom_rel f /\
           rint_plus r' (convg_interval θ m) ≤ snd anr.

  Program Definition widen_sequence :
    Preord.hom (prod_preord (prod_preord A (flat enumN)) PreRealDom)
               (prod_preord A PreRealDom)
    := Preord.Hom _ _ 
                  (fun anr => (fst (fst anr)
                  , rint_plus (convg_interval θ (snd (fst anr))) (snd anr)
                  ))
        _.
  Next Obligation.
    simpl; intros.
    destruct a as [[??]?].
    destruct b as [[??]?].
    destruct H as [[??]?]. simpl in *.
    split; simpl; auto.
    hnf; intros.
    apply rint_plus_correct in H2.
    apply rint_plus_correct.
    destruct H2 as [q1 [q2 [?[??]]]].
    exists q1. exists q2. intuition.
    hnf in H0. subst n0. auto.
  Qed.    



  Lemma Psemidec : forall ar, semidec (P ar).
Admitted.
(*
  Proof.
    intro ar.
    unfold P. 
    apply (semidec_ex (prod_preord A PreRealDom) (flat enumN)
            (fun ar n => 
               rint_end (snd ar) - rint_start (snd ar) >= θ n /\
      (forall m:flat enumN, m ∈ proj1_sig (Ndownset n) ->
         exists r', 
           (fst ar,m,r') ∈ PLT.hom_rel f /\
           exists q, in_interval q r' /\ in_interval q (snd ar)) /\

               (fst ar, n, snd ar) ∈ PLT.hom_rel f)). 
    intros a b c ?. intuition.
    hnf in H. destruct H. hnf in H. subst c. auto.
    destruct H. hnf in H. subst c. auto.
    revert H3. apply (PLT.hom_order _ _ _ f); auto.
    destruct H; split; auto.
    apply PLT.effective.
    intros. 
    apply semidec_conj.
    apply dec_semidec.
    destruct (Qlt_le_dec
                (rint_end (snd (fst ab)) - rint_start (snd (fst ab)))
                (θ (snd ab))).
    right. intro.
    apply (Qlt_irrefl (θ (snd ab))).
    eapply Qle_lt_trans; eauto.
    left; auto.
    apply semidec_conj.
    apply all_finset_semidec.
    intros. destruct H. hnf in H. subst b. auto.
    intro a.
    apply (semidec_ex (flat enumN) PreRealDom
      (fun a r' => 
        (fst (fst ab), a, r') ∈ PLT.hom_rel f /\
        (exists q : Q, in_interval q r' /\ in_interval q (snd (fst ab))))).
    intuition.
    revert H1.
    apply (PLT.hom_order _ _ _ f); auto.
    destruct H2 as [q [??]]. exists q. split; auto.
    destruct H. apply H3. auto.
    apply PLT.effective.
    intros.
    apply semidec_conj.
    apply semidec_in.
    constructor.
    apply eff_ord_dec.
    apply effective_prod.
    apply effective_prod.
    apply PLT.effective.
    apply PLT.effective.
    apply PLT.effective.
    apply dec_semidec.
    destruct (cusl_lub _ rint_cusl (snd ab0) (snd (fst ab))).
    destruct s as [z [?[??]]].
    left.
    exists (rint_start z).
    split.
    apply H.
    split. apply Qle_refl. apply rint_proper.
    apply H0.
    split. apply Qle_refl. apply rint_proper.
    right; intro.
    destruct H as [q [??]].
    apply (f0 (RatInt q q (Qle_refl q))).
    apply rint_ord_test; simpl; auto.
    apply rint_ord_test; simpl; auto.
    apply semidec_in.
    constructor.
    apply eff_ord_dec.
    apply effective_prod.
    apply effective_prod.
    apply PLT.effective.
    apply PLT.effective.
    apply PLT.effective.
  Qed.
*)

  Definition real_limit_rel : erel A PreRealDom :=
    image widen_sequence (esubset P Psemidec (PLT.hom_rel f)).

  Lemma real_limit_rel_elem a r :
    (a,r) ∈ real_limit_rel <->
    exists x,
      x ∈ PLT.hom_rel f /\ P x /\ widen_sequence x ≈ (a,r).
  Proof.
    unfold real_limit_rel.
    split; intros.
    apply image_axiom2 in H. destruct H as [x [??]].
    apply esubset_elem in H. destruct H. eauto.
    unfold P; intros.
    destruct a0 as [[??]?].
    destruct b as [[??]?].
    destruct H1 as [[[??]?][[??]?]]. simpl in *.
    hnf in H7. subst c3. clear H4.
    destruct (H2 m) as [r' [??]]; auto.
    exists r'; intuition.
    apply (PLT.hom_order _ _ _ f) with (c,m) r'; auto.
    split; auto.
    etransitivity; eauto.

    destruct H as [x [?[??]]].
    apply image_axiom1'.
    exists x; intuition.
    rewrite esubset_elem. split; auto.

    unfold P; intros.
    destruct a0 as [[??]?].
    destruct b as [[??]?].
    destruct H2 as [[[??]?][[??]?]]. simpl in *.
    hnf in H8. subst c3. clear H5.
    destruct (H3 m) as [r' [??]]; auto.
    exists r'; intuition.
    apply (PLT.hom_order _ _ _ f) with (c,m) r'; auto.
    split; auto.
    etransitivity; eauto.
  Qed.
    
    
(*
  Definition real_limit_rel : erel A PreRealDom :=
      (@esubset (prod_preord A PreRealDom) P Psemidec 
                (eff_enum _ (effective_prod (PLT.effective A) (PLT.effective PreRealDom)))
       ).

  Lemma real_limit_rel_elem : forall a r,
    (a,r) ∈ real_limit_rel <->
    P (a,r).
  Proof.
    intros. unfold real_limit_rel.
    rewrite esubset_elem.
    intuition. apply eff_complete.
    unfold P; simpl; intros.
    destruct H0 as [n [??]]. exists n. split; auto.
    destruct H.
    destruct a0 as [p q]. destruct b as [p' q'].
    destruct H. destruct H2. simpl in *.
    apply rint_ord_test in H3.
    apply rint_ord_test in H4.
    assert (rint_end q == rint_end q').
    apply Qle_antisym; intuition.
    assert (rint_start q == rint_start q').
    apply Qle_antisym; intuition.
    rewrite <- H5. rewrite <- H6.
    auto.
    destruct H1. split.
    intros.
    destruct (H1 m) as [r' [?[?[??]]]]; auto.
    exists r'; intuition.
    destruct H as [[??][??]].
    revert H4. apply (PLT.hom_order _ _ _ f); auto.
    split; simpl; auto.
    exists x; split; auto.
    destruct H as [[??][??]].
    apply H9. auto.
    destruct H as [[??][??]].

    revert H2. apply (PLT.hom_order _ _ _ f); auto.
    split; auto.
  Qed.
*)
  
  Program Definition real_limit : A → PreRealDom :=
    PLT.Hom true A PreRealDom real_limit_rel _ _ .
  Next Obligation.
    intros; simpl.
    apply real_limit_rel_elem in H1.
    apply real_limit_rel_elem.
    destruct H1 as [z [?[??]]].
    destruct z as [[x0 n] y0].
    simpl in H3.
    destruct H3 as [[??][??]].
    simpl in *.
    admit.
Qed.
Next Obligation.
    intro a.
    apply prove_directed; auto.
    simpl; intros.
    apply erel_image_elem in H.
    apply erel_image_elem in H0.
    apply real_limit_rel_elem in H.
    apply real_limit_rel_elem in H0.

    destruct H as [[[a1 n1] r1] [?[??]]].
    destruct H0 as [[[a2 n2] r2] [?[??]]].

    destruct (N.compare_spec n1 n2).
admit.

    


    exists y. split.
    red in H3.
    destruct (H3 n1) as [r' [??]].
    simpl.
    destruct (Ndownset n2).
    simpl. apply i. auto.
    simpl in H6. simpl in H7.
    simpl in H4.
    destruct H4 as [[??][??]].
    simpl in *.
    etransitivity. 2: apply H8.
    destruct H2 as [[??][??]].
    simpl in *.
    etransitivity. apply H13.
    apply rint_ord_test; simpl.
    apply rint_ord_test in H7. simpl in H7.
    destruct H7; split.
    




    etransitivity. apply H13.
    hnf; intros.
    hnf in H9.
    hnf in H7.    



admit.



    destruct (plt_hom_directed2 _ _ _ f (a,n1) r1 r2)
       as [z [?[??]]]; auto.
admit. admit.    
    exists (rint_plus (convg_interval θ n1) z).
    split.
admit.
    split.
admit.

    apply erel_image_elem.
    apply real_limit_rel_elem.
    exists (a,n1,z). simpl; split; auto. split; auto.
    red; simpl; intros.
    destruct (H1 m) as [q1 [??]]; simpl; auto.
    simpl in *.
    destruct (H3 m) as [q2 [??]]; simpl; auto.
    simpl in *.
    destruct (plt_hom_directed2 _ _ _ f (a1,m) q1 q2)
       as [q [?[??]]]; auto.
admit.
    
admit.
    
    hnf in H3. simpl in H3.
    destruct (H3 n1) as [r' [??]].
    destruct (Ndownset n2). simpl. apply i. auto.
    destruct (cusl_lub _ rint_cusl r' r1).
    destruct s as [r'' [?[??]]].
    exists (rint_plus r'' (convg_interval θ n1)).
    split.
admit.
    split.
    hnf; intros.
admit.    
    apply erel_image_elem.
    apply real_limit_rel_elem.
    


    exists q. split; auto.
admit.
    etransitivity. 2: apply H10.
    


    red.
    exists n1. simpl.

    


    exists (x', n, rint_plus y' (rint_opp (convg_interval θ n))). simpl. split.
    revert H1. apply (PLT.hom_order _ _ _ f).
    split; simpl; auto.
    etransitivity; eauto.
    hnf; intros.
    apply rint_plus_correct.
    hnf in H6.
    hnf in H0.
    exists q. exists 0%Q.
    intuition.
    apply H0.
    apply H6.
    apply rint_plus_correct.
    exists 0%Q. exists q.
    intuition.
    split; simpl.
    rewrite <- (Qplus_le_l _ _ (θ n)). ring_simplify.
    generalize (convg_pos θ n). intuition.
    generalize (convg_pos θ n). intuition.
    ring.
    split; simpl.
    rewrite <- (Qplus_le_l _ _ (θ n)). ring_simplify.
    generalize (convg_pos θ n). intuition.
    rewrite Qopp_involutive.
    generalize (convg_pos θ n). intuition.
    ring.
    split.
    red. simpl. intros.
    destruct (H2 m H7) as [r' [??]]. simpl in *.
    exists r'. split; auto.
    revert H8.
    apply (PLT.hom_order _ _ _ f).
    split; simpl; auto.
    etransitivity; eauto.
    auto.
    hnf; intros.
    apply H9 in H10.
    apply rint_plus_correct in H10.
    destruct H10 as [q1 [q2 [?[??]]]].
    hnf in H6.
    hnf in H0.
    apply rint_plus_correct.
    exists q1. exists q2. intuition.
    apply rint_plus_correct.
    exists q1. exists 0%Q.
    split.
    apply H0.
    apply H6.
    apply rint_plus_correct.
    exists 0%Q. exists q1. 
    intuition.
    split; simpl.
    rewrite <- (Qplus_le_l _ _ (θ n)). ring_simplify.
    generalize (convg_pos θ n). intuition.
    generalize (convg_pos θ n). intuition.
    ring.
    split. split; simpl.
    rewrite <- (Qplus_le_l _ _ (θ n)). ring_simplify.
    generalize (convg_pos θ n). intuition.
    rewrite Qopp_involutive.
    generalize (convg_pos θ n). intuition.
    ring.

    split; split; simpl; auto.
    apply rint_ord_test. simpl.
    split; ring_simplify.
    admit. admit.
    apply rint_ord_test. simpl.
    split; ring_simplify.

    hnf; simpl. intros.
    



    subst P. simpl in *.
    destruct H1 as [n [??]].
    exists n. split.
    eapply Qle_trans. apply H1.
    rewrite <- (Qplus_le_l _ _ (rint_start y')).
    rewrite <- (Qplus_le_l _ _ (rint_start y)).
    ring_simplify.
    rewrite (Qplus_comm (rint_end y)).
    apply rint_ord_test in H0. destruct H0.
    apply Qplus_le_compat; auto.
    destruct H2. split.
    intros.
    destruct (H2 m) as [r' [?[?[??]]]]; auto.
    exists r'; split; auto.
    revert H5. apply (PLT.hom_order _ _ _ f); auto.
    split; auto.
    exists x0; split; auto.
    revert H3. apply (PLT.hom_order _ _ _ f); auto.
    split; auto.
  Qed.
  Next Obligation.
    intro a.
    apply prove_directed; auto.
    simpl; intros.
    apply erel_image_elem in H.
    apply erel_image_elem in H0.
    apply real_limit_rel_elem in H.
    apply real_limit_rel_elem in H0.
    unfold P in H.
    unfold P in H0. simpl in *.
    destruct H as [n1 [?[??]]].
    destruct H0 as [n2 [?[??]]].
    
    destruct (N.compare_spec n1 n2).
    subst n2.
    destruct (plt_hom_directed2 _ _ _ f (a,n1) x y)
       as [z [?[??]]]; auto.
    

    exists z. intuition.
    apply erel_image_elem.
    apply real_limit_rel_elem.
    red.
    exists n1. simpl.


  Qed.  
  
  
  
semidec_ex:
  forall (A B : preord) (P : A -> B -> Prop),
  (forall (a : A) (b c : Preord_Eq B), b ≈ c -> P a b -> P a c) ->
  effective_order B ->
  (forall ab : A * B, semidec (P (fst ab) (snd ab))) ->
  forall a : A, semidec (exists x, P a x)

