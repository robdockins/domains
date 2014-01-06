(* Copyright (c) 2014, Robert Dockins *)

Require Import List.

Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import directed.


Definition is_mub_complete hf (A:preord) :=
  forall (M:finset A) (x:A), inh hf M -> upper_bound x M ->
    exists mub:A, minimal_upper_bound mub M /\ mub ≤ x.

Definition mub_closed hf (A:preord) (X:finset A) :=
  forall M:finset A, inh hf M -> M ⊆ X ->
    forall x:A, minimal_upper_bound x M -> x ∈ X.

Record plotkin_order (hf:bool) (A:preord) :=
  PlotkinOrder
  { mub_complete : is_mub_complete hf A
  ; mub_closure : finset A -> finset A
  ; mub_clos_incl : forall M:finset A, M ⊆ mub_closure M
  ; mub_clos_mub : forall (M:finset A), mub_closed hf A (mub_closure M)
  ; mub_clos_smallest : forall (M X:finset A),
        M ⊆ X ->
        mub_closed hf A X -> 
        mub_closure M ⊆ X
  }.
Arguments mub_closure [hf] [A] p _.
Arguments mub_complete [hf] [A] p _ _ _ _.
Arguments mub_clos_incl [hf] [A] p _ _ _.
Arguments mub_clos_mub [hf] [A] p _ _ _ _ _ _.
Arguments mub_clos_smallest [hf] [A] p _ _ _ _ _ _.

Lemma mub_clos_mono : forall hf A (H:plotkin_order hf A),
  forall (M N:finset A),
    M ⊆ N -> mub_closure H M ⊆ mub_closure H N.
Proof.
  intros.
  apply mub_clos_smallest; auto.
  apply incl_trans with finset_theory N; auto.
  apply mub_clos_incl.
  apply mub_clos_mub; eauto.
Qed.

Lemma mub_clos_idem : forall hf A (H:plotkin_order hf A), 
  forall (M:finset A),
    mub_closure H M ≈ mub_closure H (mub_closure H M).
Proof.
  intros. split.
  apply mub_clos_incl.
  apply mub_clos_smallest; auto.
  red; auto.
  apply mub_clos_mub; auto.
Qed.

Program Definition empty_plotkin hf : plotkin_order hf emptypo :=
  PlotkinOrder hf emptypo _ (fun _ => nil) _ _ _.
Solve Obligations of empty_plotkin using (repeat intro; simpl in *; intuition).

Program Definition unit_plotkin hf : plotkin_order hf unitpo :=
  PlotkinOrder hf _ _ (fun M => if hf then M else (tt::nil)) _ _ _.
Solve Obligations of unit_plotkin using (repeat intro; hnf; auto).
Next Obligation.
  repeat intro. exists tt.
  split; hnf; auto.
Qed.
Next Obligation.
  repeat intro.
  destruct hf.
  auto.
  destruct a. apply cons_elem; auto.
Qed.
Next Obligation.
  repeat intro.
  destruct hf.
  hnf in H. destruct H.
  destruct x0. destruct x. apply H0. auto.
  destruct x. apply cons_elem; auto.
Qed.
Next Obligation.
  repeat intro.
  destruct hf. apply H; auto.
  apply (H0 M); auto. red; auto.
  split; hnf; auto.
  repeat intro. hnf. auto.
Qed.
 
Section dec_lemmas.
  Variable hf:bool.
  Variable A:preord.
  Variable Heff : effective_order A.
  Variable Hplt : plotkin_order hf A.

  Lemma upper_bound_dec : forall (M:finset A) (x:A),
    { upper_bound x M } + { ~upper_bound x M }.
  Proof.
    induction M; intros.
    left. red. intros. destruct H as [q [??]]. elim H.
    destruct (IHM x).
    destruct (eff_ord_dec A Heff a x).
    left.
    red. simpl; intros.
    destruct H as [q [??]].
    simpl in H. destruct H; subst.
    rewrite H0; auto.
    apply u. exists q; split; auto.
    right.
    intro. apply n.
    apply H.
    exists a. split; simpl; auto.
    right. intro.
    apply n.
    red; intros.
    apply H.
    destruct H0 as [q[??]].
    exists q; split; simpl; auto.
  Qed.

  Lemma mub_finset_dec : forall (M:finset A) (x:A) (Hinh:inh hf M),
    { minimal_upper_bound x M } + { ~minimal_upper_bound x M }.
  Proof.
    intros M x.
    destruct (upper_bound_dec M x).
    destruct (eff_in_dec Heff (mub_closure Hplt M) x).
    set (P b := upper_bound b M -> b ≤ x -> x ≤ b).
    destruct (finset_find_dec' A P) with (mub_closure Hplt M).
    subst P; simpl; intuition.
    rewrite <- H. apply H0.
    red; intros. rewrite H. apply H1. auto.
    rewrite H; auto.
    unfold P. simpl.
    intro b.
    destruct (upper_bound_dec M b).
    destruct (eff_ord_dec A Heff b x).
    destruct (eff_ord_dec A Heff x b).
    left. auto.
    right. intro.
    apply n. apply H; auto.
    left. intros. elim n. auto.
    left. intros. elim n. auto.

    destruct s.
    destruct a.
    red in H0.
    subst P. simpl in H0.
    right. intro.
    destruct H1.
    apply H0.
    intros.
    apply H2; auto.
    left.
    split; auto.
    intros.
    destruct (mub_complete Hplt M b) as [b0 [??]]; auto.
    transitivity b0; auto.
    apply p; auto.
    apply mub_clos_mub with M; auto.
    apply mub_clos_incl; auto.
    destruct H1; auto.
    transitivity b; auto.
    right. intro.
    apply n.
    apply mub_clos_mub with M; auto.
    apply mub_clos_incl; auto.
    right.
    intro. destruct H.
    apply n; auto.
  Qed.
End dec_lemmas.


Lemma upper_bound_ok : forall A (G:finset A) (x y:A),
  x ≈ y -> upper_bound x G -> upper_bound y G.
Proof.
  unfold upper_bound; intros.
  rewrite <- H. apply H0; auto.
Qed.

Lemma minimal_upper_bound_ok : forall A (G:finset A) (x y:A),
  x ≈ y -> minimal_upper_bound x G -> minimal_upper_bound y G.
Proof.
  unfold minimal_upper_bound. intros.
  destruct H0; split.
  eapply upper_bound_ok; eauto.
  intros. rewrite <- H. apply H1; auto.
  rewrite H; auto.
Qed.

Section normal_sets.
  Variable A:preord.
  Variable Heff: effective_order A.
  Variable hf:bool.

  Definition normal_set (X:finset A) :=
    (inh hf X) /\
    forall z, directed hf (finsubset A (fun x => x ≤ z) (fun x => eff_ord_dec A Heff x z) X).

  Definition has_normals :=
    forall (X:finset A) (Hinh:inh hf X),
      { Z:finset A | X ⊆ Z /\ normal_set Z }.
    
  Section plt_normal.
    Hypothesis Hplt : plotkin_order hf A.

    Lemma plt_has_normals : has_normals.
    Proof.
      red. intros X Xinh.
      exists (mub_closure Hplt X).
      split. apply mub_clos_incl.
      red; intros.
      split.
      apply inh_sub with X; auto.
      apply mub_clos_incl.
      red; simpl; intros.
      destruct (mub_complete Hplt M z); auto.
      red; intros.
      apply H in H0.
      apply finsubset_elem in H0.
      destruct H0; auto.
      intros. rewrite <- H1; auto.
      destruct H0.
      exists x. split; auto.
      destruct H0; auto.
      apply finsubset_elem.
      intros. rewrite <- H2; auto.
      split; auto.
      apply (mub_clos_mub Hplt X) with M; auto.
      red; intros.
      apply H in H2.
      apply finsubset_elem in H2.
      destruct H2; auto.
      intros. rewrite <- H3; auto.
    Qed.
  End plt_normal.

  Lemma normal_has_ubs Q :
    normal_set Q ->
    forall (X:finset A) (Hinh:inh hf X), X ⊆ Q ->
      { Y:finset A | Y ⊆ Q /\
        (forall y, y ∈ Y -> upper_bound y X) /\
        (forall z, upper_bound z X -> exists m, m ≤ z /\ m ∈ Y /\ upper_bound m X) }.
  Proof.
    intros. red in H.
    set (Y := finsubset A (fun x => upper_bound x X) (fun x => upper_bound_dec A Heff X x) Q).
    exists Y. split.
    unfold Y.
    red. intros.
    apply finsubset_elem in H1.
    destruct H1; auto.
    apply upper_bound_ok.
    split.
    intros.
    unfold Y in H1.
    apply finsubset_elem in H1.
    destruct H1; auto.
    apply upper_bound_ok.
    intros z Hz.
    destruct H as [HQ H].
    destruct (H z X); auto.
    red; intros.
    apply finsubset_elem.
    intros. rewrite <- H2; auto.
    split. apply H0; auto.
    apply Hz. auto.
    destruct H1.
    apply finsubset_elem in H2.
    destruct H2.
    exists x. intuition.
    unfold Y.
    apply finsubset_elem.
    apply upper_bound_ok.
    split; auto.
    intros. rewrite <- H3. auto.
  Qed.

  Section normal_mubs.
    Variable Q:finset A.
    Hypothesis H : normal_set Q.
    
    Variable X:finset A.
    Variable Hinh : inh hf X.
    Hypothesis H0 : X ⊆ Q.

    Let Y := proj1_sig (normal_has_ubs Q H X Hinh H0).
    Let H1 := proj1 (proj2_sig (normal_has_ubs Q H X Hinh H0)).
    Let H2 := proj2 (proj2_sig (normal_has_ubs Q H X Hinh H0)).

    Let P (x y:A) := (y ≤ x /\ x ≰ y).
    
    Lemma normal_mubs' : forall x, { z | z ∈ Y /\ P x z } + { forall z, z ∈ Y -> ~P x z }.
    Proof.
      intro x.
      apply (finset_find_dec A (P x)).
      clear; unfold P; intros.
      rewrite <- H. auto.
      unfold P.
      intro y.
      destruct (eff_ord_dec A Heff y x).
      destruct (eff_ord_dec A Heff x y).
      right. intros [??]. apply H4; auto.
      left. split; auto.
      right. intros [??]. apply n; auto.
    Qed.

    Lemma normal_sub_mub_dec : forall x, { minimal_upper_bound x X }+{~minimal_upper_bound x X}.
    Proof.
      intro x.
      destruct (normal_mubs' x).
      destruct s as [m [??]].
      red in H4.
      right. intro.
      destruct H4.
      apply H6.
      apply H5; auto.
      destruct H2. apply H2. auto.
      destruct (upper_bound_dec A Heff X x).
      left. red; intros.
      split; auto.
      intros.
      destruct H2.
      destruct (H6 b) as [m [?[??]]]; auto.
      destruct (eff_ord_dec A Heff x b); auto.
      elim (n m); auto.
      red. split; auto.
      transitivity b; auto.
      red; intros.
      apply n0.
      transitivity m; auto.
      right. intros [??]. contradiction.
    Qed.

    Lemma normal_has_mubs :
        { Y:finset A | Y ⊆ Q /\
          (forall y, y ∈ Y -> minimal_upper_bound y X) /\
          forall z, upper_bound z X -> exists m, m ≤ z /\ m ∈ Y /\ minimal_upper_bound m X }.
    Proof.
      exists (finsubset A (fun x => minimal_upper_bound x X) normal_sub_mub_dec Y).
      split.
      red; intros.
      apply finsubset_elem in H3.
      destruct H3.
      apply H1; auto.
      apply minimal_upper_bound_ok.
      split; intros.
      apply finsubset_elem in H3.
      destruct H3; auto.
      apply minimal_upper_bound_ok.
      destruct H2.
      destruct (H5 z) as [m [?[??]]]; auto.    
      cut (forall (Y1 Y2:finset A), (Y1++Y2)%list = Y -> forall m,
        (forall y, y ∈ Y1 -> y ≤ m -> m ≤ y) ->
        m ∈ Y2 -> m ≤ z -> exists m', m' ∈ Y2 /\ m' ≤ z /\ minimal_upper_bound m' X).
      intros.
      destruct (H9 nil Y) with m; auto.
      intros. destruct H10 as [?[??]]. elim H10.
      exists x. intuition.
      apply finsubset_elem.
      apply minimal_upper_bound_ok.
      split; auto.
      clear m H6 H7 H8.
      intros Y1 Y2. revert Y1. induction Y2; simpl; intros.
      rewrite <- List.app_nil_end in H6.
      destruct H8 as [?[??]].
      elim H8.
      destruct (eff_ord_dec A Heff a m).
      destruct (normal_mubs' a).
      destruct s as [m' [??]].
      destruct H11.
      assert (m' ∈ (Y2:finset A)).
      destruct H10 as [q [??]].
      rewrite <- H6 in H10.
      apply List.in_app_or in H10.
      destruct H10.
      elim H12.
      transitivity m; auto.
      apply H7; auto.
      exists q; split; auto.
      transitivity a; auto.
      destruct H10.
      subst q.
      elim H12. rewrite H13. auto.
      exists q; split; auto.

      destruct (IHY2 (Y1 ++ a::nil)%list) with m'.
      rewrite List.app_ass.
      simpl. auto.
      intros.
      destruct H14 as [p [??]].
      apply List.in_app_or in H14.
      destruct H14.
      transitivity a; auto.
      transitivity m; auto.
      apply H7; auto.
      exists p; split; auto.
      transitivity m'; auto.
      transitivity a; auto.
      simpl in H14. intuition subst.
      rewrite H16; auto.
      auto.
      transitivity m; auto.
      transitivity a; auto.
      exists x.
      intuition.
      destruct H2 as [p [??]]. exists p; split; simpl; auto.
      exists a. split.
      exists a; split; simpl; auto. split; auto.
      transitivity m; auto.
      split.
      apply H2.
      fold Y.
      rewrite <- H6.
      exists a; split; simpl; auto.
      apply List.in_or_app; auto.
      right; simpl; auto.
      intros.
      destruct (eff_ord_dec A Heff a b); auto.
      destruct (H5 b) as [q [??]]; auto.
      destruct H13.
      elim (n q); auto.
      split; auto.
      transitivity b; auto.
      intro.
      apply n0.
      transitivity q; auto.
      destruct (IHY2 (Y1++(a::nil))%list) with m.
      rewrite <- H6.
      rewrite List.app_ass; auto.
      intros.
      destruct H10 as [p [??]].
      apply List.in_app_or in H10.
      destruct H10.
      apply H7; auto.
      exists p; split; auto.
      simpl in H10; intuition subst.
      elim n. rewrite <- H12. auto.
      destruct H8 as [?[??]].
      destruct H8. subst a.
      elim n. destruct H10; auto.
      exists x; split; auto.
      auto.
      exists x; intuition.
      destruct H2 as [p [??]]. 
      exists p; split; simpl; auto.
    Qed.    
  End normal_mubs.

  Lemma normal_sub_mub_closed_dec Q : normal_set Q ->
    forall (M:finset A), M ⊆ Q -> { mub_closed hf A M }+{ ~mub_closed hf A M }.
  Proof.
    intros HQ M HM. 
    unfold mub_closed.
    set (P' (N:finset A) := inh hf N -> N ⊆ M -> forall x, minimal_upper_bound x N -> x ∈ M).
    assert (forall x y, x ≈ y -> P' x -> P' y).
    clear. unfold P'. intros.
    apply H0.
    apply inh_eq with y; auto.
    rewrite H. auto.
    destruct H3. split.
    red; intros. apply H3.
    rewrite <- H; auto.
    intros. apply H4.
    red; intros. apply H5.
    rewrite H; auto.
    auto.
    destruct (finsubset_dec' A (OrdDec A (eff_ord_dec A Heff)) P') with M; auto.
    intro x.
    unfold P'.
    destruct (inh_dec A hf x).
    destruct (finset_find_dec' A
      (fun p:A => p ∈ M)) with x.
    intros. rewrite <- H0; auto.
    intros. apply finset_in_dec. 
    constructor. apply eff_ord_dec. auto.
    left. intros Hx ?.
    destruct s.
    destruct a.
    apply H0 in H1. elim H2; auto.
    destruct (normal_has_mubs Q HQ x) as [MUBS [?[??]]]; auto.
    red; intros. apply HM. apply m. auto.
    destruct (finset_find_dec' A (fun p => p ∈ M)) with MUBS.
    intros. rewrite <- H3; auto.
    intros. apply finset_in_dec. 
    constructor. apply eff_ord_dec. auto.
    right. intro.
    destruct s. destruct a. apply H5.
    apply H3; auto.
    left. intros _. intros.
    apply m0.
    destruct (H2 x0) as [x0' [?[??]]].
    destruct H4; auto.
    apply member_eq with x0'; auto.
    split; auto.
    destruct H4.
    apply H8; auto.
    destruct H7; auto.
    left; intro. contradiction.
    left.
    intros. 
    unfold P' in p.
    apply p with M0; auto.
    right. intro.
    destruct e as [X [??]].
    apply H2.
    red. intros.
    apply H0 with X; auto.
  Qed.    
 
  Lemma normal_set_mub_closed_sets Q : normal_set Q ->
    { CLS : finset (finset A) | 
      forall X, X ∈ CLS <-> (inh hf X /\ X ⊆ Q /\ mub_closed hf A X) }.
  Proof.        
    intros.
    set (SUBS := list_finsubsets Q).    
    assert (forall X, X ∈ SUBS -> X ⊆ Q).
    intros.
    unfold SUBS in H0.
    apply list_finsubsets_correct; auto.
    assert { XS:finset (finset A) | XS ⊆ SUBS /\ 
      forall X, X ∈ XS <-> (inh hf X /\ X ∈ SUBS /\ mub_closed hf A X) }.
    revert H0.
    generalize SUBS.
    clear SUBS.
    induction SUBS; intros.
    exists nil. split.
    red; auto.
    intuition.
    destruct H1 as [?[??]]. elim H1.
    destruct H1 as [?[??]]. elim H1.
    destruct IHSUBS as [XS [??]].
    intros. apply H0.
    destruct H1 as [q [??]]. exists q; split; simpl; auto.
    destruct (inh_dec A hf a).
    destruct (normal_sub_mub_closed_dec Q H a); auto.
    apply H0. exists a; split; simpl; auto.
    exists (a::XS)%list.
    split.
    red; intros.
    destruct H3 as [q [??]].
    destruct H3. subst q.
    exists a; split; simpl; auto.
    destruct (H1 a0).
    exists q; split; simpl; auto.
    destruct H5. exists x; split; simpl; auto.
    split; intros.
    destruct H3 as [q [??]].
    destruct H3. subst q.
    split. apply inh_eq with a; auto.
    split.
    exists a; split; simpl; auto.
    red. intros.
    rewrite H4. 
    apply (m M); auto.
    rewrite <- H4; auto.
    assert (X ∈ XS).
    exists q; split; simpl; auto.
    apply H2 in H5.
    destruct H5; split; auto.
    destruct H6; split; auto.
    destruct H6 as [q' [??]].
    exists q'; split; simpl; auto.
    destruct H3 as [HQ [??]].
    destruct H3 as [q [??]].
    destruct H3. subst q.
    exists a; split; simpl; auto.
    assert (X ∈ XS).
    apply H2.
    split; auto.
    split; auto.
    exists q; split; simpl; auto.
    destruct H6 as [q' [??]].
    exists q'; split; simpl; auto.
    exists XS.
    split.
    red; intros.
    apply H1 in H3.
    destruct H3 as [q [??]]. exists q; split; simpl; auto.
    split; intros.
    rewrite H2 in H3.
    destruct H3 as [HQ [??]]; split; auto. split; auto.
    destruct H3 as [q [??]]. exists q; split; simpl; auto.
    destruct H3 as [HQ [??]].
    destruct H3 as [q [??]].
    destruct H3. subst q.
    elim n; auto.
    red; intros.
    red in H4.
    rewrite <- H5.
    apply (H4 M); auto.
    rewrite H5; auto.
    rewrite H2. split; auto.
    split; auto.
    exists q; split; simpl; auto.
    exists XS.
    split.
    red; intros.
    apply H1 in H3.
    destruct H3 as [q [??]]. exists q; split; simpl; auto.
    split; intros.
    rewrite H2 in H3.
    destruct H3 as [HQ [??]]; split; auto. split; auto.
    destruct H3 as [q [??]]. exists q; split; simpl; auto.
    destruct H3 as [HQ [??]].
    destruct H3 as [q [??]].
    destruct H3. subst q.
    elim n; auto.
    apply inh_eq with X; auto.
    rewrite H2. split; auto.
    split; auto.
    exists q; split; simpl; auto.

    destruct X as [XS [??]].
    exists XS.
    intro X; split; intros.
    apply H2 in H3.
    destruct H3. split; auto.
    destruct H4; split; auto.
    destruct H3 as [?[??]].
    apply H2; split; auto. split; auto.
    apply list_finsubsets_complete; auto.
    constructor. apply (eff_ord_dec A Heff).
  Qed.

  Let OD := (OrdDec A (eff_ord_dec A Heff)).

  Lemma mub_closed_intersect : forall (X Y:finset A),
    mub_closed hf A X -> mub_closed hf A Y ->
    mub_closed hf A (fin_intersect A OD X Y).
  Proof.
    repeat intro.
    apply fin_intersect_elem.
    split.
    apply (H M); auto.
    red; intros.
    apply H2 in H4.
    apply fin_intersect_elem in H4.
    destruct H4; auto.
    apply (H0 M); auto.
    red; intros.
    apply H2 in H4.
    apply fin_intersect_elem in H4.
    destruct H4; auto.
  Qed.

  Lemma normal_set_mub_closed Q : normal_set Q -> mub_closed hf A Q.
  Proof.
    repeat intro.
    destruct (normal_has_mubs Q H M H0) as [MUBS [?[??]]]; auto.
    destruct (H5 x) as [m [?[??]]].
    destruct H2; auto.
    apply H3.
    apply member_eq with m; auto.
    split; auto.
    destruct H2. apply H9; auto.
    destruct H8; auto.
  Qed.

  Lemma normal_set_mub_closure Q : normal_set Q ->
    forall (M:finset A) (Minh : inh hf M), M ⊆ Q ->
      { CL:finset A | M ⊆ CL /\ mub_closed hf A CL /\
          forall CL':finset A, M ⊆ CL' -> mub_closed hf A CL' -> CL ⊆ CL' }.
  Proof.
    intros.
    destruct (normal_set_mub_closed_sets Q H) as [CLS ?]; auto.
    assert (Hsubdec : forall X:finset A, {M⊆X}+{~(M ⊆ X)}).
    intros.
    destruct (finset_find_dec' A (fun z => z ∈ X)) with M.
    intros. rewrite <- H1; auto.
    apply finset_in_dec.
    constructor. apply eff_ord_dec; auto.
    destruct s as [z [??]].
    right. intro. apply H3 in H1.
    contradiction.
    left. red; auto.
    set (CLS' := finsubset (finset A) (fun X => M ⊆ X) Hsubdec CLS).
    exists (fin_list_intersect A OD CLS' Q).
    split.
    red; intros.
    apply fin_list_intersect_elem.
    split. apply H0; auto.
    intros.
    unfold CLS' in H2.
    apply finsubset_elem in H2.
    destruct H2.
    apply H3; auto.
    intros. rewrite <- H3; auto.
    split.
    cut (forall x, x ∈ CLS' -> mub_closed hf A x).
    generalize CLS'. clear -H.
    induction CLS'; intros.
    simpl.
    apply normal_set_mub_closed; auto.
    simpl.
    apply mub_closed_intersect.
    apply H0.
    exists a; split; simpl; auto.
    apply IHCLS'.
    intros. apply H0.
    destruct H1 as [q [??]]. exists q; split; simpl; auto.
    intros.
    unfold CLS' in H1.
    apply finsubset_elem in H1.
    destruct H1.
    apply i in H1.
    destruct H1 as [Hx [??]]; auto.
    intros. rewrite <- H2; auto.
    intros.
    red; intros.
    apply fin_list_intersect_elem in H3.
    destruct H3.
    assert (fin_intersect A OD CL' Q ∈ CLS').
    unfold CLS'.
    apply finsubset_elem.
    intros. rewrite <- H5; auto.
    split; auto.
    apply i.
    split.

    destruct hf; auto.
    red in Minh. simpl.
    destruct Minh as [x ?].
    exists x.
    apply fin_intersect_elem. split; auto.

    split; auto.
    red; intros.
    apply fin_intersect_elem in H5.
    destruct H5; auto.
    apply mub_closed_intersect; auto.
    apply normal_set_mub_closed; auto.
    red; intros.
    apply fin_intersect_elem.
    split; auto.
    apply H4 in H5.
    apply fin_intersect_elem in H5.
    destruct H5; auto.
  Qed.

  Lemma mub_closed_normal_set : forall Q (HQ:inh hf Q),
    is_mub_complete hf A ->
    mub_closed hf A Q ->
    normal_set Q.
  Proof.
    intros. split; auto. repeat intro.
    set (Q' := finsubset A (fun x => x ≤ z) (fun x => eff_ord_dec A Heff x z) Q).
    destruct (H Q' z).
    apply inh_sub with M; auto.
    red; intros.
    unfold Q' in H2.
    apply finsubset_elem in H2. destruct H2; auto.
    intros. rewrite <- H3; auto.
    destruct H2.
    assert (x ∈ Q).
    apply (H0 Q'); auto.
    apply inh_sub with M; auto.
    unfold Q'; red; intros.
    apply finsubset_elem in H4. destruct H4; auto.
    intros. rewrite <- H5; auto.
    exists x. split; auto.
    red; intros.
    destruct H2.
    apply H2.
    unfold Q'.
    apply finsubset_elem.
    intros. rewrite <- H7; auto.
    split; auto.
    apply H1 in H5.
    apply finsubset_elem in H5. destruct H5; auto.
    intros. rewrite <- H7; auto.
    apply H1 in H5.
    apply finsubset_elem in H5. destruct H5; auto.
    intros. rewrite <- H7; auto.
    unfold Q'.
    apply finsubset_elem.
    intros. rewrite <- H5; auto.
    split; auto.
  Qed.

  Hypothesis Hnorm : has_normals.

  Lemma check_inh (X:finset A) : { X = nil /\ hf = true }+{ inh hf X }.
  Proof.
    destruct hf. simpl.
    destruct X. left; auto.
    right. exists c. apply cons_elem; auto.
    right. red. auto.
  Qed.

  Definition norm_closure X :=
    match check_inh X with
    | left _ => nil
    | right Xinh =>
      match Hnorm X Xinh with
      | exist Q (conj HQ1 HQ2) => proj1_sig (normal_set_mub_closure Q HQ2 X Xinh HQ1)
      end
    end.

  Program Definition norm_plt : plotkin_order hf A :=
    PlotkinOrder hf A _ norm_closure _ _ _.
  Next Obligation.
    red; intros.
    destruct (Hnorm M) as [Q [??]]; auto.
    destruct (normal_has_mubs Q H2 M H H1) as [MUBS [?[??]]].
    destruct (H5 x) as [m [?[??]]]; auto.
    exists m; split; auto.
  Qed.
  Next Obligation.
    repeat intro.
    unfold norm_closure.
    destruct (check_inh M).
    destruct a0. subst M; auto.
    destruct (Hnorm M i) as [Q [??]].
    destruct (normal_set_mub_closure Q n M i i0).
    simpl.
    destruct a0.
    apply H0. auto.
  Qed.    
  Next Obligation.
    repeat intro.
    unfold norm_closure in *.
    destruct (check_inh M).
    destruct a. subst.
    destruct H. apply H0 in H.
    apply nil_elem in H. elim H.
    destruct (Hnorm M i) as [Q [??]].
    destruct (normal_set_mub_closure Q n M i i0).
    simpl in *.
    destruct a. 
    destruct H3.
    apply H3 with M0; auto.
  Qed.    
  Next Obligation.
    repeat intro.
    unfold norm_closure in *.
    destruct (check_inh M).
    apply nil_elem in H1. elim H1.
    destruct (Hnorm M i) as [Q [??]].
    destruct (normal_set_mub_closure Q n M i i0).
    simpl in *.
    destruct a0 as [?[??]].
    apply H4; auto.
  Qed.    
End normal_sets.

Lemma prod_has_normals hf (A B:preord)
  (HAeff:effective_order A)
  (HBeff:effective_order B)
  (HA:plotkin_order hf A)
  (HB:plotkin_order hf B) :
  has_normals (A×B) (effective_prod HAeff HBeff) hf.
Proof.
  red; intros.
  exists (finprod (mub_closure HA (image π₁ X))
                  (mub_closure HB (image π₂ X))).
  split.
  red; intros.
  destruct a.
  apply finprod_elem.
  split.
  apply mub_clos_incl.
  change c with (π₁#((c,c0):(A×B))).
  apply image_axiom1. auto.
  apply mub_clos_incl.
  change c0 with (π₂#((c,c0):(A×B))).
  apply image_axiom1. auto.
  apply mub_closed_normal_set.

  destruct hf; auto.
  destruct Hinh as [x ?].
  exists x.
  destruct x as [a b].
  apply finprod_elem.
  split; apply mub_clos_incl; auto.
  change a with (π₁#((a,b):A×B)).
  apply image_axiom1. auto.
  change b with (π₂#((a,b):A×B)).
  apply image_axiom1. auto.

  red. intros M x HMinh. intro.
  destruct x as [a b].
  destruct (mub_complete HA (image π₁ M) a).
  apply inh_image; auto.
  red; intros.
  apply image_axiom2 in H0.
  destruct H0 as [y [??]].
  apply H in H0.
  rewrite H1.
  destruct H0; auto.
  destruct (mub_complete HB (image π₂ M) b).
  apply inh_image; auto.
  red; intros.
  apply image_axiom2 in H1.
  destruct H1 as [y [??]].
  apply H in H1.
  rewrite H2.
  destruct H1; auto.
  exists (x,x0).
  destruct H0. destruct H1.
  split; [ | split; auto ].
  split.
  red; intros.
  split.
  apply H0.
  change (fst x1) with (π₁#x1). apply image_axiom1. auto.
  apply H1.
  change (snd x1) with (π₂#x1). apply image_axiom1. auto.
  intros.
  split.
  destruct H0. apply H6; auto.
  red; intros.
  apply image_axiom2 in H7.
  destruct H7 as [y [??]].
  apply H4 in H7.
  rewrite H8. destruct H7; auto.
  destruct H5; auto.
  destruct H1. apply H6.
  red; intros.
  apply image_axiom2 in H7.
  destruct H7 as [y [??]].
  apply H4 in H7.
  rewrite H8. destruct H7; auto.
  destruct H5; auto.

  red. intros M Minh. intros.
  destruct x.
  apply finprod_elem. split.
  apply (mub_clos_mub HA (image π₁ X) ) with (image π₁ M).
  apply inh_image; auto.

  red; intros.
  apply image_axiom2 in H1. destruct H1 as [y [??]].
  apply H in H1.
  destruct y.
  apply finprod_elem in H1.
  destruct H1.
  rewrite H2; auto.
  destruct H0; split.
  red; intros.
  apply image_axiom2 in H2. destruct H2 as [y [??]].
  apply H0 in H2.
  rewrite H3. destruct H2; auto.
  intros.
  destruct (H1 (b,c0)).
  red; intros.
  split.
  simpl.
  apply H2.
  change (fst x) with (π₁#x).
  apply image_axiom1. auto.
  simpl.
  apply H0 in H4.
  destruct H4; auto.
  split; auto.
  simpl in *. auto.

  apply (mub_clos_mub HB (image π₂ X)) with  (image π₂ M); auto.
  apply inh_image; auto.
  red; intros.
  apply image_axiom2 in H1. destruct H1 as [y [??]].
  apply H in H1.
  destruct y.
  apply finprod_elem in H1.
  destruct H1.
  rewrite H2; auto.
  destruct H0; split.
  red; intros.
  apply image_axiom2 in H2. destruct H2 as [y [??]].
  apply H0 in H2.
  rewrite H3. destruct H2; auto.
  intros.
  destruct (H1 (c,b)).
  red; intros.
  split.
  simpl.
  apply H0 in H4. destruct H4; auto.
  apply H2.
  change (snd x) with (π₂#x).
  apply image_axiom1. auto.
  split; auto.
  simpl in *. auto.
Qed.

Definition plotkin_prod hf (A B:preord)
  (HAeff:effective_order A) (HBeff:effective_order B)
  (HA:plotkin_order hf A) (HB:plotkin_order hf B)
  : plotkin_order hf (A×B)
  := norm_plt (A×B) (effective_prod HAeff HBeff) hf
         (prod_has_normals hf A B HAeff HBeff HA HB).


Lemma sum_has_normals hf (A B:preord)
  (HAeff:effective_order A)
  (HBeff:effective_order B)
  (HA:plotkin_order hf A)
  (HB:plotkin_order hf B) :
  has_normals (sum_preord A B) (effective_sum HAeff HBeff) hf.
Proof.
  hnf; intros.  
  set (L := left_finset A B X).
  set (R := right_finset A B X).
  destruct hf.
  
  case_eq L. intro.
  case_eq R. intro.
  elimtype False.
  destruct Hinh.
  destruct x.
  apply left_finset_elem in H1.
  unfold L in *.
  rewrite H in H1. apply nil_elem in H1. elim H1.
  apply right_finset_elem in H1.
  unfold R in *.
  rewrite H0 in H1. apply nil_elem in H1. elim H1.

  intros c l HR.
  destruct (plt_has_normals B HBeff true HB R) as [Z' [??]].
  hnf. exists c. rewrite HR. apply cons_elem; auto.
  exists (finsum nil Z').
  split.
  hnf. intros.
  rewrite (left_right_finset_finsum A B) in H2.
  destruct a.
  apply finsum_left_elem in H2.
  unfold L in H. rewrite H in H2.
  apply nil_elem in H2. elim H2.
  apply finsum_right_elem in H2.
  apply H0 in H2. 
  apply finsum_right_elem. auto.
  split.
  exists (inr c).
  apply finsum_right_elem. apply H0.
  rewrite HR. apply cons_elem; auto.
  repeat intro.
  destruct Hinh0 as [m Hm].
  destruct m as [m|m].
  apply H2 in Hm.
  apply finsubset_elem in Hm.
  destruct Hm.
  apply finsum_left_elem in H3.
  apply nil_elem in H3. elim H3.
  intros. rewrite <- H3; auto.
  generalize (H2 (inr m) Hm).  
  intros.
  apply finsubset_elem in H3.
  destruct H3.
  apply finsum_right_elem in H3.
  destruct z as [z|z]. elim H4.
  destruct H1.
  destruct (H5 z (right_finset A B M)) as [q [??]].
  exists m. apply right_finset_elem. auto.
  hnf; intros.
  apply finsubset_elem.
  intros. rewrite <- H7; auto.
  apply right_finset_elem in H6.
  apply H2 in H6.
  apply finsubset_elem in H6.
  destruct H6. split; auto.
  apply finsum_right_elem in H6.
  auto.
  intros. rewrite <- H7. auto.
  apply finsubset_elem in H7. destruct H7.
  exists (inr q). split.
  hnf; intros.
  destruct x.
  apply H2 in H9.
  apply finsubset_elem in H9.
  destruct H9. elim H10.
  intros. rewrite <- H10; auto.
  apply H6.
  apply right_finset_elem. auto.
  apply finsubset_elem.
  intros. rewrite <- H9; auto.
  split; auto.
  apply finsum_right_elem. auto.
  intros. rewrite <- H8. auto.
  intros. rewrite <- H4. auto.

  intros c l HL.
  case_eq R; intro.
  destruct (plt_has_normals A HAeff true HA L) as [Z' [??]].
  hnf. exists c. rewrite HL. apply cons_elem; auto.
  exists (finsum Z' nil).
  split.
  hnf. intros.
  rewrite (left_right_finset_finsum A B) in H2.
  destruct a.
  apply finsum_left_elem in H2.
  apply finsum_left_elem. auto.
  apply finsum_right_elem in H2.
  unfold R in H. rewrite H in H2.
  apply nil_elem in H2. elim H2.
  split.
  exists (inl c).
  apply finsum_left_elem. apply H0.
  rewrite HL. apply cons_elem; auto.
  repeat intro.
  destruct Hinh0 as [m Hm].
  destruct m as [m|m].
  generalize (H2 (inl m) Hm).  
  intros.
  apply finsubset_elem in H3.
  destruct H3.
  apply finsum_left_elem in H3.
  destruct z as [z|z]. 2: elim H4.
  destruct H1.
  destruct (H5 z (left_finset A B M)) as [q [??]].
  exists m. apply left_finset_elem. auto.
  hnf; intros.
  apply finsubset_elem.
  intros. rewrite <- H7; auto.
  apply left_finset_elem in H6.
  apply H2 in H6.
  apply finsubset_elem in H6.
  destruct H6. split; auto.
  apply finsum_left_elem in H6.
  auto.
  intros. rewrite <- H7. auto.
  apply finsubset_elem in H7. destruct H7.
  exists (inl q). split.
  hnf; intros.
  destruct x.
  apply H6.
  apply left_finset_elem. auto.
  apply H2 in H9.
  apply finsubset_elem in H9.
  destruct H9. elim H10.
  intros. rewrite <- H10; auto.
  apply finsubset_elem.
  intros. rewrite <- H9; auto.
  split; auto.
  apply finsum_left_elem. auto.
  intros. rewrite <- H8. auto.
  intros. rewrite <- H4. auto.
  apply H2 in Hm.
  apply finsubset_elem in Hm.
  destruct Hm.
  apply finsum_right_elem in H3.
  apply nil_elem in H3. elim H3.
  intros. rewrite <- H3; auto.

  intros l' HR.
  destruct (plt_has_normals A HAeff true HA L) as [ZL [??]].
  exists c. rewrite HL. apply cons_elem; auto.
  destruct (plt_has_normals B HBeff true HB R) as [ZR [??]].
  exists c0. rewrite HR. apply cons_elem; auto.
  exists (finsum ZL ZR).  
  split.
  hnf; intros.
  rewrite (left_right_finset_finsum A B) in H3.
  destruct a.
  apply finsum_left_elem in H3.
  apply H in H3.
  apply finsum_left_elem. auto.
  apply finsum_right_elem in H3.
  apply H1 in H3.
  apply finsum_right_elem. auto.
  hnf; intros.
  split.  
  exists (inl c).
  apply finsum_left_elem.
  apply H. rewrite HL. apply cons_elem; auto.
  repeat intro.
  destruct z as [z|z].
  destruct H0.
  destruct (H4 z (left_finset A B M)).
  destruct Hinh0.
  destruct x.
  exists c1.
  apply left_finset_elem. auto.
  apply H3 in H5.
  apply finsubset_elem in H5.
  destruct H5. elim H6.
  intros. rewrite <- H6; auto.
  hnf; simpl; intros.
  apply left_finset_elem in H5.
  apply H3 in H5.
  apply finsubset_elem in H5.
  destruct H5.
  apply finsubset_elem.
  intros. rewrite <- H7; auto.
  split; auto.
  apply finsum_left_elem in H5; auto.
  intros. rewrite <- H6; auto.
  destruct H5. exists (inl x).
  split.
  hnf; intros.
  destruct x0.
  apply H5.
  apply left_finset_elem. auto.
  apply H3 in H7.
  apply finsubset_elem in H7.
  destruct H7. elim H8.
  intros. rewrite <- H8; auto.
  apply finsubset_elem.
  intros. rewrite <- H7; auto.
  apply finsubset_elem in H6.
  destruct H6. split; auto.
  apply finsum_left_elem; auto.
  intros. rewrite <- H7; auto.
  destruct H2.
  destruct (H4 z (right_finset A B M)).
  destruct Hinh0 as [m Hm].
  destruct m.
  apply H3 in Hm.
  apply finsubset_elem in Hm.
  destruct Hm. elim H6.
  intros. rewrite <- H5; auto.
  exists c1. apply right_finset_elem; auto.
  hnf; intros.
  apply right_finset_elem in H5.
  apply finsubset_elem.
  intros. rewrite <- H6; auto.
  apply H3 in H5.
  apply finsubset_elem in H5.
  destruct H5. split; auto.
  apply finsum_right_elem in H5. auto.
  intros. rewrite <- H6; auto.
  exists (inr x).
  destruct H5. split.
  hnf; intros.
  destruct x0.
  apply H3 in H7.
  apply finsubset_elem in H7. destruct H7. elim H8.
  intros. rewrite <- H8; auto.
  apply H5. apply right_finset_elem; auto.
  apply finsubset_elem.
  intros. rewrite <- H7; auto.
  apply finsubset_elem in H6.
  destruct H6. split; auto.
  apply finsum_right_elem; auto.
  intros. rewrite <- H7; auto.
  
  destruct (plt_has_normals A HAeff false HA L) as [ZL [??]].
  hnf; auto.
  destruct (plt_has_normals B HBeff false HB R) as [ZR [??]].
  hnf; auto.
  exists (finsum ZL ZR).  
  split.
  hnf; intros.
  rewrite (left_right_finset_finsum A B) in H3.
  destruct a.
  apply finsum_left_elem in H3.
  apply H in H3.
  apply finsum_left_elem. auto.
  apply finsum_right_elem in H3.
  apply H1 in H3.
  apply finsum_right_elem. auto.
  hnf; intros.
  split.   hnf; auto.
  repeat intro.
  destruct z as [z|z].
  destruct H0.
  destruct (H4 z (left_finset A B M)).
  hnf; auto.
  hnf; simpl; intros.
  apply left_finset_elem in H5.
  apply H3 in H5.
  apply finsubset_elem in H5.
  destruct H5.
  apply finsubset_elem.
  intros. rewrite <- H7; auto.
  split; auto.
  apply finsum_left_elem in H5; auto.
  intros. rewrite <- H6; auto.
  destruct H5. exists (inl x).
  split.
  hnf; intros.
  destruct x0.
  apply H5.
  apply left_finset_elem. auto.
  apply H3 in H7.
  apply finsubset_elem in H7.
  destruct H7. elim H8.
  intros. rewrite <- H8; auto.
  apply finsubset_elem.
  intros. rewrite <- H7; auto.
  apply finsubset_elem in H6.
  destruct H6. split; auto.
  apply finsum_left_elem; auto.
  intros. rewrite <- H7; auto.
  destruct H2.
  destruct (H4 z (right_finset A B M)).
  hnf; auto.
  hnf; intros.
  apply right_finset_elem in H5.
  apply finsubset_elem.
  intros. rewrite <- H6; auto.
  apply H3 in H5.
  apply finsubset_elem in H5.
  destruct H5. split; auto.
  apply finsum_right_elem in H5. auto.
  intros. rewrite <- H6; auto.
  exists (inr x).
  destruct H5. split.
  hnf; intros.
  destruct x0.
  apply H3 in H7.
  apply finsubset_elem in H7. destruct H7. elim H8.
  intros. rewrite <- H8; auto.
  apply H5. apply right_finset_elem; auto.
  apply finsubset_elem.
  intros. rewrite <- H7; auto.
  apply finsubset_elem in H6.
  destruct H6. split; auto.
  apply finsum_right_elem; auto.
  intros. rewrite <- H7; auto.
Qed.

Definition plotkin_sum hf (A B:preord)
  (HAeff:effective_order A) (HBeff:effective_order B)
  (HA:plotkin_order hf A) (HB:plotkin_order hf B)
  : plotkin_order hf (sum_preord A B)
  := norm_plt (sum_preord A B) 
         (effective_sum HAeff HBeff) hf
         (sum_has_normals hf A B HAeff HBeff HA HB).

Fixpoint unlift_list {A} (x:list (option A)) :=
  match x with
  | nil => nil
  | None :: x' => unlift_list x'
  | Some a :: x' => a :: unlift_list x'
  end.

Lemma unlift_app A (l l':list (option A)) :
  unlift_list (l++l') = unlift_list l ++ unlift_list l'.
Proof.
  induction l; simpl; intuition.
  destruct a; simpl; auto.
  f_equal; auto.
Qed.

Lemma in_unlift A (l:list (option A)) x :
  In x (unlift_list l) <-> In (Some x) l.
Proof.
  induction l; simpl; intuition.
  destruct a; simpl in *.
  intuition subst; auto.
  right; auto.
  subst. simpl; auto.
  destruct a; simpl; auto.
Qed.

Lemma incl_unlift A (l l':list (option A)) :
  List.incl l l' -> List.incl (unlift_list l) (unlift_list l').
Proof.
  induction l; repeat intro; simpl in *; intuition.
  destruct a; simpl in *; intuition subst; auto.
  rewrite in_unlift.
  apply H; simpl; auto.
  rewrite in_unlift.
  rewrite in_unlift in H1.
  apply H; simpl; auto.
  apply IHl; auto.
  hnf; intros. apply H; simpl; auto.
Qed.

Definition lift_mub_closure hf (A:preord) (HA:plotkin_order hf A) (M:finset (lift A)) 
  : finset (lift A):=
  match unlift_list M with
  | nil => single None
  | X => None :: image (liftup A) (mub_closure HA X)
  end.

Lemma lift_has_normals hf1 hf2 (A:preord)
  (Heff:effective_order A)
  (Hplt:plotkin_order hf1 A) :
  has_normals (lift A) (effective_lift Heff) hf2.
Proof.
  red; intros.
  set (X' := unlift_list X : finset A).
  assert (forall a, a ∈ X' <-> Some a ∈ X).
  intro; split; intros.
  destruct H as [q [??]].
  apply in_unlift in H.
  exists (Some q). split; auto.
  destruct H as [q [??]].
  destruct q.
  exists c. split; auto.
  apply in_unlift. auto.
  destruct H0. elim H0.
  exists (lift_mub_closure hf1 A Hplt X).
  split.
  red; intros.
  unfold lift_mub_closure.
  case_eq (unlift_list X).
  intros.
  destruct H0 as [q [??]].
  destruct a.
  destruct q.
  assert (In c0 (unlift_list X)).
  apply in_unlift. auto.
  rewrite H1 in H3. elim H3.
  destruct H2. elim H2.
  apply single_axiom; auto.
  intros.
  destruct a.
  apply cons_elem. right.
  apply image_axiom1'.
  exists c0. split; auto.
  apply mub_clos_incl.
  destruct H0 as [q [??]].
  destruct q.
  exists c1. split; auto.
  rewrite <- H1.
  apply in_unlift. auto.
  destruct H2. elim H2.
  apply cons_elem; auto.

  hnf; intros.
  split.
  unfold lift_mub_closure.
  destruct hf2; simpl; auto.
  exists None.
  destruct (unlift_list X); simpl.
  apply single_axiom. auto.
  apply cons_elem; auto.
  
  repeat intro.
  case_eq (unlift_list M); intros.
  exists (None : lift A).
  split.
  hnf; intros.
  destruct x; auto.
  destruct H2 as [q [??]].
  destruct q.
  assert (In c0 (unlift_list M)).
  apply in_unlift. auto.
  rewrite H1 in H4. elim H4.
  destruct H3. elim H3.
  apply finsubset_elem.
  intuition. rewrite <- H2; auto.
  split; auto.
  unfold lift_mub_closure.
  destruct (unlift_list X); auto.
  apply single_axiom; auto.
  apply cons_elem; auto.
  red. simpl; auto.

  destruct z.
  destruct (mub_complete Hplt (unlift_list M) c0) as [ub [??]].
  rewrite H1.
  destruct hf1; simpl; auto.
  exists c. apply cons_elem; auto.
  hnf; intros.
  assert (Some x ∈ M).
  destruct H2 as [q [??]].
  apply in_unlift in H2.
  exists (Some q). split; auto.
  generalize H3; intros.
  apply H0 in H3.
  apply finsubset_elem in H3.
  destruct H3. auto.
  intros. rewrite <- H5; auto.
  exists (Some ub).
  split.
  hnf; intros.
  destruct H2.
  destruct x; auto.
  assert (c1 ∈ (unlift_list M : finset A)).
  destruct H4 as [q [??]].
  destruct q.
  exists c2.
  split; auto.
  apply in_unlift. auto.
  destruct H6. elim H6.
  apply H2 in H6. auto.
  red; simpl; auto.
  apply finsubset_elem.
  intros. rewrite <- H4; auto.
  split; auto.
  unfold lift_mub_closure.
  case_eq (unlift_list X).
  intros.
  assert (Some c ∈ M).
  exists (Some c); split; auto.
  apply in_unlift. rewrite H1. simpl; auto.
  apply H0 in H5.
  apply finsubset_elem in H5.
  destruct H5.
  unfold lift_mub_closure in H5.
  rewrite H4 in H5.
  apply single_axiom in H5. destruct H5. elim H5.
  intros. rewrite <- H6; auto.
  intros.
  apply cons_elem. right.
  apply image_axiom1'.
  exists ub. split; auto.
  rewrite <- H4.
  apply mub_clos_mub with (unlift_list M); auto.
  rewrite H1.
  destruct hf1; simpl; auto.
  exists c. apply cons_elem; auto.

  hnf; intros.
  assert (Some a ∈ M).
  destruct H5 as [q [??]].
  exists (Some q). split; auto.
  apply in_unlift; auto.
  apply H0 in H6.
  apply finsubset_elem in H6.
  destruct H6.
  unfold lift_mub_closure in H6.
  rewrite H4 in H6.
  rewrite <- H4 in H6.
  apply cons_elem in H6.
  destruct H6.
  destruct H6. elim H6.
  apply image_axiom2 in H6.
  destruct H6 as [y [??]].
  simpl in H8.
  apply member_eq with y; auto.
  intros. rewrite <- H7; auto.
  
  assert (Some c ∈ M).
  exists (Some c); split; auto.
  apply in_unlift. rewrite H1. simpl; auto.
  apply H0 in H2.
  apply finsubset_elem in H2.
  destruct H2. elim H3.
  intros. rewrite <- H3. auto.
Qed.


Program Definition lift_plotkin hf1 hf2 (A:preord)
  (Hplt:plotkin_order hf1 A) 
  (Heff:effective_order A)
  : plotkin_order hf2 (lift A)
  := norm_plt (lift A) (effective_lift Heff) hf2
         (lift_has_normals hf1 hf2 A Heff Hplt).
