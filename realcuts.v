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



Section cuts.
  Record cut  := Cut
    { cut_upper : eset Qpreord
    ; cut_lower : eset Qpreord
    ; cut_proper : forall u l, u ∈ cut_upper -> l ∈ cut_lower -> l <= u
    ; cut_is_lower : forall (q1 q2:Qpreord), q1 <= q2 -> q2 ∈ cut_lower -> q1 ∈ cut_lower
    ; cut_is_upper : forall (q1 q2:Qpreord), q1 <= q2 -> q1 ∈ cut_upper -> q2 ∈ cut_upper
     (** probably should reformulate the prereals as directed sets of
         intervals where the endpoints may be -∞ or ∞.
       *)
    ; cut_nonextended : (exists x, x ∈ cut_upper) <-> (exists x, x ∈ cut_lower)
    }.

  Definition cut_ord (x y:cut) :=
    cut_upper x ⊆ cut_upper y /\
    cut_lower x ⊆ cut_lower y.

  Program Definition cut_ord_mixin : Preord.mixin_of cut :=
    Preord.Mixin cut cut_ord _ _ .
  Next Obligation.
    intros. red; split; red; auto.
  Qed.
  Next Obligation.
    unfold cut_ord. intuition; repeat intro; eauto.
  Qed.

  Definition cut_preord := Preord.Pack cut cut_ord_mixin.

  Program Definition rints_to_cut
          (X:eset PreRealDom)
          (Hdir:directed true X)
          (Hdown:forall (r r':PreRealDom), r ≤ r' -> r' ∈ X -> r ∈ X )
          : cut :=
    Cut (eimage' _ _ rint_end   X)
        (eimage' _ _ rint_start X)
        _ _ _ _.
  Next Obligation.
    unfold eimage'.
    intros.
    destruct H as [n1 ?].
    destruct H0 as [n2 ?].
    revert H. case_eq (X n1); intros.
    revert H0. case_eq (X n2); intros.
    destruct H1 as [? _]. destruct H2 as [? _].
    red in H1. simpl in H1.
    red in H2. simpl in H2.
    rewrite H2. rewrite H1.
    destruct (Hdir (c::c0::nil)%list).
    exists c. apply cons_elem; auto.
    red; simpl; intros.
    apply cons_elem in H3. destruct H3. rewrite H3.
    exists n1. rewrite H. auto.
    apply cons_elem in H3. destruct H3. rewrite H3.
    exists n2. rewrite H0. auto.
    apply nil_elem in H3. elim H3.
    destruct H3.
    assert (c ≤ x).
    apply H3. apply cons_elem; auto.
    assert (c0 ≤ x).
    apply H3. apply cons_elem; right. apply cons_elem; auto.
    apply Qle_trans with (rint_start x).
    apply rint_ord_test in H6. intuition.
    apply Qle_trans with (rint_end x).
    apply rint_proper.
    apply rint_ord_test in H5. intuition.
    elim H2.
    elim H1.
  Qed.
  Next Obligation.
    repeat intro.
    unfold eimage' in H0.
    destruct H0 as [n ?].
    revert H0. case_eq (X n); intros.
    destruct H1 as [? _]. red in H1. simpl in H1.
    assert (q1 <= rint_end c).
    apply Qle_trans with q2; auto.
    rewrite H1. apply rint_proper.
    set (r := RatInt q1 (rint_end c) H2).
    assert (r ∈ X).
    apply Hdown with c.
    apply rint_ord_test.
    split; simpl; auto.
    apply Qle_trans with q2; auto.
    rewrite H1; auto.
    apply Qle_refl.
    apply Qle_refl.
    exists n. rewrite H0. auto.
    destruct H3 as [n' ?].
    exists n'.
    unfold eimage'.
    destruct (X n').
    assert (q1 == rint_start c0).
    destruct H3.
    assert (rint_start r == rint_start c0).
    apply rint_ord_test in H3.
    apply rint_ord_test in H4.
    apply Qle_antisym; intuition.
    simpl in H5. auto.
    split; red; simpl; auto.
    symmetry; auto.
    auto.
    elim H1.
  Qed.
  Next Obligation.
    repeat intro.
    unfold eimage' in H0.
    destruct H0 as [n ?].
    revert H0. case_eq (X n); intros.
    destruct H1 as [? _]. red in H1. simpl in H1.
    assert (rint_start c <= q2).
    apply Qle_trans with q1; auto.
    rewrite H1. apply rint_proper.
    set (r := RatInt (rint_start c) q2 H2).
    assert (r ∈ X).
    apply Hdown with c.
    apply rint_ord_test.
    split; simpl; auto.
    apply Qle_refl.
    apply Qle_trans with q1; auto.
    rewrite H1; auto.
    apply Qle_refl.
    exists n. rewrite H0. auto.
    destruct H3 as [n' ?].
    exists n'.
    unfold eimage'.
    destruct (X n').
    assert (q2 == rint_end c0).
    destruct H3.
    assert (rint_end r == rint_end c0).
    apply rint_ord_test in H3.
    apply rint_ord_test in H4.
    apply Qle_antisym; intuition.
    simpl in H5. auto.
    split; red; simpl; auto.
    symmetry; auto.
    auto.
    elim H1.
  Qed.
  Next Obligation.
    intros.
    unfold eimage'.
    split; intros [x ?].
    destruct H as [n ?].
    revert H. case_eq (X n); intros.
    exists (rint_start c).
    exists n. rewrite H. auto.
    elim H0.
    destruct H as [n ?].
    revert H. case_eq (X n); intros.
    exists (rint_end c).
    exists n. rewrite H. auto.
    elim H0.
  Qed.

  Lemma rints_to_cut_upper q X Hdir Hdown :
    q ∈ cut_upper (rints_to_cut X Hdir Hdown) <->
    exists r, r ∈ X /\ q == rint_end r.
  Proof.
    simpl; intros. unfold eimage'.
    split; intros.
    destruct H as [n ?].
    revert H. case_eq (X n); intros.
    exists c. split.
    exists n. rewrite H; auto.
    destruct H0; auto.
    elim H0.
    destruct H as [r [??]].
    destruct H as [n ?]. exists n.
    destruct (X n); auto.
    assert (rint_end r == rint_end c).
    destruct H.
    apply rint_ord_test in H.
    apply rint_ord_test in H1.
    apply Qle_antisym; intuition.
    rewrite H1 in H0.
    split; red; simpl; auto.
    symmetry; auto.
  Qed.

  Lemma rints_to_cut_lower q X Hdir Hdown :
    q ∈ cut_lower (rints_to_cut X Hdir Hdown) <->
    exists r, r ∈ X /\ q == rint_start r.
  Proof.
    simpl; intros. unfold eimage'.
    split; intros.
    destruct H as [n ?].
    revert H. case_eq (X n); intros.
    exists c. split.
    exists n. rewrite H; auto.
    destruct H0; auto.
    elim H0.
    destruct H as [r [??]].
    destruct H as [n ?]. exists n.
    destruct (X n); auto.
    assert (rint_start r == rint_start c).
    destruct H.
    apply rint_ord_test in H.
    apply rint_ord_test in H1.
    apply Qle_antisym; intuition.
    rewrite H1 in H0.
    split; red; simpl; auto.
    symmetry; auto.
  Qed.

  Opaque rints_to_cut.


  Parameter A:∂PLT.

  Program Definition hom_to_cut (f:A → PreRealDom) : PLT.ord A → cut_preord :=
    Preord.Hom (PLT.ord A) cut_preord 
               (fun a => rints_to_cut (erel_image _ _ (PLT.dec A) (PLT.hom_rel f) a) 
                                    (PLT.hom_directed _ _ _ f a)
                                     _)
               _.
  Next Obligation.
    intros.
    apply erel_image_elem in H0.
    apply erel_image_elem.
    revert H0. apply PLT.hom_order; auto.
  Qed.
  Next Obligation.
    simpl; intros.
    assert (erel_image _ _ (PLT.dec A) (PLT.hom_rel f) a ⊆
            erel_image _ _ (PLT.dec A) (PLT.hom_rel f) b).
    red; simpl; intros.
    apply erel_image_elem in H0.
    apply erel_image_elem.
    revert H0.
    apply PLT.hom_order; auto.

    split; red; intros.
    apply rints_to_cut_upper in H1.
    apply rints_to_cut_upper.
    destruct H1 as [r [??]]. exists r; split; auto.
    apply rints_to_cut_lower in H1.
    apply rints_to_cut_lower.
    destruct H1 as [r [??]]. exists r; split; auto.
  Qed.

  Program Definition cut_to_hom_rel (f:PLT.ord A → cut_preord) : erel A PreRealDom :=
    @esubset (prod_preord A PreRealDom)
            (fun ar => rint_end (snd ar) ∈ cut_upper (f (fst ar)) /\
                       rint_start (snd ar) ∈ cut_lower (f (fst ar)))
            _
            (eff_enum _ (effective_prod (PLT.effective A) (PLT.effective PreRealDom))).
  Next Obligation.
    intros.
    apply semidec_conj.
    apply semidec_in.
    constructor. apply Qeq_dec.
    apply semidec_in.
    constructor. apply Qeq_dec.
  Qed.

  Lemma cut_to_hom_rel_elem (f:PLT.ord A → cut_preord) a r :
    (a,r) ∈ cut_to_hom_rel f <-> 
       (rint_end r ∈ cut_upper (f a) /\ rint_start r ∈ cut_lower (f a)).
  Proof.
    unfold cut_to_hom_rel.
    rewrite esubset_elem. intuition.
    apply eprod_elem; split; apply eff_complete.
    simpl; intros.
    destruct H as [[??][??]].
    intuition.
    cut (rint_end (snd b) ∈ cut_upper (f (fst a0))).
    destruct (Preord.axiom _ _ f (fst a0) (fst b)); auto.
    revert H4. apply cut_is_upper.
    apply rint_ord_test in H3. intuition.
    cut (rint_start (snd b) ∈ cut_lower (f (fst a0))).
    destruct (Preord.axiom _ _ f (fst a0) (fst b)); auto.
    revert H5. apply cut_is_lower.
    apply rint_ord_test in H3. intuition.
  Qed.

  Program Definition cut_to_hom (f:PLT.ord A → cut_preord) : A → PreRealDom :=
    PLT.Hom true A PreRealDom (cut_to_hom_rel f) _ _. 
  Next Obligation.
    simpl; intros.
    apply cut_to_hom_rel_elem in H1.
    apply cut_to_hom_rel_elem.
    apply rint_ord_test in H0.
    intuition.
    cut (rint_end y' ∈ cut_upper (f x)).
    destruct (Preord.axiom _ _ f x x'); auto.
    revert H0.
    apply cut_is_upper; auto.
    cut (rint_start y' ∈ cut_lower(f x)).
    destruct (Preord.axiom _ _ f x x'); auto.
    revert H4.
    apply cut_is_lower; auto.
  Qed.
  Next Obligation.
    intros f a. apply prove_directed; auto.
    intros.
    apply erel_image_elem in H.
    apply erel_image_elem in H0.
    apply cut_to_hom_rel_elem in H.
    apply cut_to_hom_rel_elem in H0.
    destruct H. destruct H0.
    assert (Qmax (rint_start x) (rint_start y) <= Qmin (rint_end x) (rint_end y)).
    apply Q.max_case.
    intros. rewrite <- H3; auto.
    apply Q.min_case.
    intros. rewrite <- H3; auto.
    eapply cut_proper; eauto.
    eapply cut_proper; eauto.
    apply Q.min_case.
    intros. rewrite <- H3; auto.
    eapply cut_proper; eauto.
    eapply cut_proper; eauto.
    exists (RatInt _ _ H3).
    split.
    apply rint_ord_test. simpl.
    split. apply Q.le_max_l. apply Q.le_min_l.
    split.
    apply rint_ord_test. simpl.
    split. apply Q.le_max_r. apply Q.le_min_r.
    apply erel_image_elem.
    apply cut_to_hom_rel_elem.
    simpl. split.
    apply Q.min_case; simpl; auto.
    intros p q ?. apply member_eq.
    split; red; simpl; auto. symmetry; auto.
    apply Q.max_case; simpl; auto.
    intros p q ?. apply member_eq.
    split; red; simpl; auto. symmetry; auto.
  Qed.


  Lemma cut_roundtrip1 f :
    cut_to_hom (hom_to_cut f) ≈ f.
  Proof.
    split; hnf; simpl; intros [a r] H.
    apply cut_to_hom_rel_elem in H. destruct H.
    simpl in *.
    rewrite rints_to_cut_upper in H.
    rewrite rints_to_cut_lower in H0.
    destruct H as [r1 [??]].
    destruct H0 as [r2 [??]].
    apply erel_image_elem in H.
    apply erel_image_elem in H0.
    destruct (plt_hom_directed2 _ _ _ f a r1 r2) as [r' [?[??]]]; auto.
    apply PLT.hom_order with a r'; auto.
    apply rint_ord_test.
    apply rint_ord_test in H4.
    apply rint_ord_test in H5.
    split.
    rewrite H2; intuition.
    rewrite H1; intuition.

    apply cut_to_hom_rel_elem.
    split; simpl.
    rewrite rints_to_cut_upper.
    exists r. split; auto.
    apply erel_image_elem. auto. reflexivity.
    rewrite rints_to_cut_lower.
    exists r. split; auto.
    apply erel_image_elem. auto. reflexivity.
  Qed.

  Lemma cut_roundtrip2 f :
    hom_to_cut (cut_to_hom f) ≈ f.
  Proof.
    intro a. split; split; simpl; hnf; intros.
    apply rints_to_cut_upper in H.
    destruct H as [r [??]].
    apply erel_image_elem in H. 
    apply cut_to_hom_rel_elem in H. destruct H.
    revert H. apply member_eq.
    split; red; simpl; auto. symmetry; auto.
    apply rints_to_cut_lower in H.
    destruct H as [r [??]].
    apply erel_image_elem in H. 
    apply cut_to_hom_rel_elem in H. destruct H.
    revert H1. apply member_eq.
    split; red; simpl; auto. symmetry; auto.
    
    apply rints_to_cut_upper.
    destruct (cut_nonextended (f a)) as [? _].
    destruct H0 as [z ?]; eauto.
    assert (z <= a0).
    eapply cut_proper; eauto.
    exists (RatInt z a0 H1).
    split; simpl; auto.
    apply erel_image_elem.
    apply cut_to_hom_rel_elem.
    simpl. split; auto. reflexivity.
    
    apply rints_to_cut_lower.
    destruct (cut_nonextended (f a)) as [_ ?].
    destruct H0 as [z ?]; eauto.
    assert (a0 <= z).
    eapply cut_proper; eauto.
    exists (RatInt a0 z H1).
    split; simpl; auto.
    apply erel_image_elem.
    apply cut_to_hom_rel_elem.
    simpl. split; auto. reflexivity.
  Qed.

  Definition cut_canonical (x:cut) :=
    (forall u, u ∈ cut_upper x -> exists u', u' ∈ cut_upper x /\ u' < u) /\ 
    (forall l, l ∈ cut_lower x -> exists l', l' ∈ cut_lower x /\ l < l').

  Definition located (x:cut) :=
    forall (ε:Q), ε > 0 ->
      exists u l,
        u ∈ cut_upper x /\
        l ∈ cut_lower x /\
        u - l <= ε.

  Lemma canonical_to_hom (f:PLT.ord A → cut_preord) :
    (forall a, cut_canonical (f a)) ->
    canonical A (cut_to_hom f).
  Proof.
    repeat intro.
    destruct (H a).
    simpl in H0.
    apply cut_to_hom_rel_elem in H0. destruct H0.
    destruct (H1 (rint_end x)) as [u' [??]]; auto.
    destruct (H2 (rint_start x)) as [l' [??]]; auto.
    assert (l' <= u').
    apply cut_proper with (f a); auto.
    exists (RatInt l' u' H8).
    split; simpl.
    apply cut_to_hom_rel_elem; split; simpl; auto.
    red; split; simpl; auto.
  Qed.

  Lemma canonical_to_cut (f:A → PreRealDom) :
    canonical A f ->
    forall a, cut_canonical (hom_to_cut f a).
  Proof.
    repeat intro.
    split; simpl; intros.
    apply rints_to_cut_upper in H0.
    destruct H0 as [r [??]].
    apply erel_image_elem in H0.
    destruct (H a r) as [r' [??]]; auto.
    exists (rint_end r').
    split.
    apply rints_to_cut_upper.
    exists r'. split.
    apply erel_image_elem. auto.
    reflexivity.
    rewrite H1.
    destruct H3; auto.
    apply rints_to_cut_lower in H0.
    destruct H0 as [r [??]].
    apply erel_image_elem in H0.
    destruct (H a r) as [r' [??]]; auto.
    exists (rint_start r').
    split.
    apply rints_to_cut_lower.
    exists r'. split.
    apply erel_image_elem. auto.
    reflexivity.
    rewrite H1.
    destruct H3; auto.
  Qed.

  Lemma located_converges (f:PLT.ord A → cut_preord) :
    (forall a, located (f a)) ->
   realdom_converges A (cut_to_hom f).
  Proof.
    repeat intro.
    destruct (H a ε) as [u [l [?[??]]]]; auto.
    assert (l <= u).
    apply cut_proper with (f a); auto.
    exists (RatInt l u H4). split; simpl; auto.
    apply cut_to_hom_rel_elem. split; simpl; auto.
  Qed.

  Lemma converges_located (f:A → PreRealDom) :
    realdom_converges A f ->
    forall a, located (hom_to_cut f a).
  Proof.
    repeat intro.
    destruct (H a ε) as [r [??]]; auto.
    exists (rint_end r), (rint_start r); split; simpl; auto.
    apply rints_to_cut_upper.
    exists r; split; auto.
    apply erel_image_elem. auto. reflexivity.
    split.
    apply rints_to_cut_lower.
    exists r; split; auto.
    apply erel_image_elem. auto. reflexivity.
    auto.
  Qed.

  Lemma hom_to_cut_mono (f g:A → PreRealDom) :
    f ≤ g -> hom_to_cut f ≤ hom_to_cut g.
  Proof.
    repeat intro.
    split; red; simpl; intros.
    apply rints_to_cut_upper in H0.
    apply rints_to_cut_upper.
    destruct H0 as [r [??]].
    exists r. split; auto.
    apply erel_image_elem in H0.
    apply erel_image_elem.
    apply H; auto.
    apply rints_to_cut_lower in H0.
    apply rints_to_cut_lower.
    destruct H0 as [r [??]].
    exists r. split; auto.
    apply erel_image_elem in H0.
    apply erel_image_elem.
    apply H; auto.
  Qed.

  Lemma cut_to_hom_mono (f g:PLT.ord A → cut_preord) :
    f ≤ g -> cut_to_hom f ≤ cut_to_hom g.
  Proof.
    repeat intro; simpl in *.
    destruct a as [a r].
    apply cut_to_hom_rel_elem in H0.
    apply cut_to_hom_rel_elem.
    destruct H0. split.
    apply (H a); auto.
    apply (H a); auto.
  Qed.

End cuts.

Canonical Structure cut_preord.

Definition cut_lt (x y:cut) :=
  exists u l,
    u ∈ cut_upper x /\
    l ∈ cut_lower y /\
    u < l.

Module interval_limit_cuts.

Section limit.
  Variable seq_upper : N -> cut.
  Variable seq_lower : N -> cut.

  Hypothesis seq_proper : forall n, cut_lt (seq_lower n) (seq_upper n).
  Hypothesis seq_upper_inside : forall n m, (n < m)%N -> cut_lt (seq_upper m) (seq_upper n).
  Hypothesis seq_lower_inside : forall n m, (n < m)%N -> cut_lt (seq_lower n) (seq_lower m).

  Definition limit_upper : eset Qpreord :=
    union ( (fun n => Some (cut_upper (seq_upper n))) : eset (eset Qpreord)).

  Definition limit_lower : eset Qpreord :=
    union ( (fun n => Some (cut_lower (seq_lower n)))  : eset (eset Qpreord)).

  Program Definition interval_limit : cut :=
    Cut limit_upper limit_lower _ _ _ _.
  Next Obligation.
    unfold limit_upper, limit_lower. intros. 
    apply union_axiom in H.
    apply union_axiom in H0.
    destruct H as [XU [??]].
    destruct H0 as [XL [??]].
    destruct H as [n1 ?].
    destruct H0 as [n2 ?].
    set (o := (1 + N.max n1 n2)%N).
    destruct (seq_lower_inside n2 (1 + N.max n1 n2)) as [a [b [?[??]]]].
    zify. omega.
    apply Qle_trans with a.
    apply cut_proper with (seq_lower n2); auto.
    rewrite <- H0; auto.
    apply Qle_trans with b.
    intuition.
    destruct (seq_proper (1 + N.max n1 n2)) as [c [d [?[??]]]].
    apply Qle_trans with c.
    apply cut_proper with (seq_lower (1 + N.max n1 n2)); auto.
    apply Qle_trans with d.
    intuition.
    destruct (seq_upper_inside n1 (1 + N.max n1 n2)) as [e [f [?[??]]]].
    zify. omega.
    apply Qle_trans with e.
    apply cut_proper with (seq_upper (1 + N.max n1 n2)); auto.
    apply Qle_trans with f.
    intuition.
    apply cut_proper with (seq_upper n1); auto.
    rewrite <- H. auto.
  Qed.
  Next Obligation.
    unfold limit_lower; intros.
    apply union_axiom in H0.
    destruct H0 as [X [??]].
    destruct H0 as [n ?].
    apply union_axiom.
    exists X. split; auto.
    exists n. auto.
    rewrite H0. rewrite H0 in H1.
    revert H1. apply cut_is_lower. auto.
  Qed.
  Next Obligation.
    unfold limit_upper; intros.
    apply union_axiom in H0.
    destruct H0 as [X [??]].
    destruct H0 as [n ?].
    apply union_axiom.
    exists X. split; auto.
    exists n. auto.
    rewrite H0. rewrite H0 in H1.
    revert H1. apply cut_is_upper. auto.
  Qed.
  Next Obligation.
    unfold limit_upper, limit_lower.
    destruct (seq_proper 0) as [u [l [?[??]]]].
    split; intros.
    destruct (cut_nonextended (seq_lower 0)).
    destruct H3 as [l' ?].
    exists u. auto.
    exists l'.
    apply union_axiom.
    exists (cut_lower (seq_lower 0)).
    split; auto.
    exists 0%N. auto.
    
    destruct (cut_nonextended (seq_upper 0)).
    destruct H4 as [u' ?].
    exists l. auto.
    exists u'.
    apply union_axiom.
    exists (cut_upper (seq_upper 0)).
    split; auto.
    exists 0%N. auto.
  Qed.

  Lemma interval_limit_inside_upper : forall n,
    cut_lt interval_limit (seq_upper n).                                  
  Proof.
    repeat intro. hnf.
    destruct (seq_upper_inside n (n+1)) as [u' [l' [?[??]]]].
    zify. omega.
    exists u'. exists l'. intuition.
    unfold interval_limit. simpl.
    unfold limit_upper.
    apply union_axiom.
    exists (cut_upper (seq_upper (n+1))).
    split. exists (n+1)%N. auto.
    auto.
  Qed.

  Lemma interval_limit_inside_lower : forall n,
    cut_lt (seq_lower n) interval_limit.
  Proof.
    repeat intro. hnf.
    destruct (seq_lower_inside n (n+1)) as [u' [l' [?[??]]]].
    zify. omega.
    exists u'. exists l'. intuition.
    unfold interval_limit. simpl.
    unfold limit_upper.
    apply union_axiom.
    exists (cut_lower (seq_lower (n+1))).
    split. exists (n+1)%N. auto.
    auto.
  Qed.

  Lemma interval_limit_least_defined lim :
    (forall n, cut_lt lim (seq_upper n)) ->
    (forall n, cut_lt (seq_lower n) lim) ->
    interval_limit ≤ lim.
  Proof.
    repeat intro. split; hnf; simpl; intros.

    unfold limit_upper in H1.
    apply union_axiom in H1.
    destruct H1 as [X [??]].
    destruct H1 as [n ?].
    destruct (H n) as [u [l [?[??]]]].
    rewrite H1 in H2.
    apply cut_is_upper with u; auto.
    apply Qle_trans with l; intuition.
    apply cut_proper with (seq_upper n); auto.
    
    unfold limit_lower in H1.
    apply union_axiom in H1.
    destruct H1 as [X [??]].
    destruct H1 as [n ?].
    destruct (H0 n) as [u [l [?[??]]]].
    rewrite H1 in H2.
    apply cut_is_lower with l; auto.
    apply Qle_trans with u; intuition.
    apply cut_proper with (seq_lower n); auto.
  Qed.

  Hypothesis seq_converges : forall ε, 0 < ε ->
     exists n a b,
       a ∈ cut_upper (seq_upper n) /\
       b ∈ cut_lower (seq_lower n) /\
       a - b <= ε.
       
  Lemma interval_limit_located : located interval_limit.
  Proof.
    red; intros.
    destruct (seq_converges ε H) as [n [a [b [?[??]]]]].
    exists a. exists b. intuition.
    simpl. unfold limit_upper.
    apply union_axiom. exists (cut_upper (seq_upper n)).
    split; auto. exists n. auto.
    apply union_axiom. exists (cut_lower (seq_lower n)).
    split; auto. exists n. auto.
  Qed.
End limit.
End interval_limit_cuts.


Module cauchy_limit_cuts.

Definition pow2 (n:N) : positive :=
 match n with
 | N0     => 1%positive
 | Npos p => shift_pos p 1
 end.

Lemma pow2_commute n1 n2 :
  (pow2 n1 * pow2 n2 = pow2 (n1+n2))%positive.
Proof.
  unfold pow2.
  destruct n1; simpl; auto.
  destruct n2; simpl; auto.
  apply Pos.mul_1_r.
  unfold shift_pos.
  rewrite Pos.iter_add.
  induction p using Pos.peano_ind; simpl; auto.
  rewrite Pos.iter_succ. simpl.
  rewrite IHp.
  rewrite Pos.iter_succ. auto.
Qed.

Lemma pow2_div_eq (a b:N) :
  (a <= b)%N -> (pow2 (b - a) * pow2 a = pow2 b)%positive.
Proof.
  intros.
  rewrite pow2_commute.
  replace (b - a + a)%N with b; auto.
  assert (0 <= a)%N.
  hnf. simpl. destruct a; discriminate.
  symmetry. apply N.sub_add; auto.
Qed. 

Definition oneOver2n (n:N) : Q := (1 # pow2 n)%Q.

Lemma oneOver2n_pos n : 0 < oneOver2n n.
Proof.
  unfold oneOver2n. intuition.
Qed.

Lemma oneOver2n_commute n1 n2 :
  (oneOver2n n1 * oneOver2n n2 == oneOver2n (n1+n2))%Q.
Proof.
  unfold oneOver2n.
  red. simpl. symmetry.
  f_equal. apply pow2_commute.
Qed.

Lemma oneOver2n_div_eq a b  :
  (a <= b)%N -> (oneOver2n (b - a) * oneOver2n a == oneOver2n b)%Q.
Proof.
  intro.
  unfold oneOver2n.
  red. simpl. symmetry.
  f_equal. apply pow2_div_eq. auto.
Qed.

Program Definition widen_cut (n:N) (x:cut) : cut :=
  Cut (image (Preord.Hom _ _ (Qplus (oneOver2n n)) _) (cut_upper x))
      (image (Preord.Hom _ _ (Qplus (- oneOver2n n)) _) (cut_lower x))
      _ _ _ _.
Next Obligation.
  intros. red in H. simpl in H.
  red. simpl. rewrite H. reflexivity.
Qed.
Next Obligation.
  intros. red in H. simpl in H.
  red. simpl. rewrite H. reflexivity.
Qed.
Next Obligation.
  simpl; intros.
  apply image_axiom2 in H.
  apply image_axiom2 in H0.
  destruct H as [q1 [??]].
  destruct H0 as [q2 [??]].
  simpl in *.
  destruct H1. red in H1. simpl in H1.
  destruct H2. red in H2. simpl in H2.
  rewrite H2. rewrite H1.
  apply Qle_trans with (0 + q2)%Q.
  apply Qplus_le_compat.
  rewrite <- (Qplus_le_l _ _ (oneOver2n n)).
  ring_simplify.
  apply Qlt_le_weak.
  apply oneOver2n_pos.
  apply Qle_refl.
  apply Qle_trans with (0 + q1)%Q.
  apply Qplus_le_compat; auto.
  apply Qle_refl.
  apply cut_proper with x; auto.
  apply Qplus_le_compat.
  apply Qlt_le_weak.
  apply oneOver2n_pos.
  apply Qle_refl.
Qed.
Next Obligation.
  intros.
  apply image_axiom2 in H0.
  destruct H0 as [y [??]]. simpl in *.
  apply image_axiom1'.
  exists (q1 + oneOver2n n)%Q.
  split. simpl.
  split; red; simpl; ring.
  eapply cut_is_lower; eauto.
  destruct H1. red in H1. simpl in H1.
  rewrite <- (Qplus_le_l _ _ (-oneOver2n n)).
  ring_simplify.
  apply Qle_trans with q2; auto.
  rewrite H1.
  ring_simplify. apply Qle_refl.
Qed.
Next Obligation.
  intros.
  apply image_axiom2 in H0.
  destruct H0 as [y [??]]. simpl in *.
  apply image_axiom1'.
  exists (q2 - oneOver2n n)%Q.
  split. simpl.
  split; red; simpl; ring.
  eapply cut_is_upper; eauto.
  destruct H1. red in H1. simpl in H1.
  rewrite <- (Qplus_le_l _ _ (oneOver2n n)).
  ring_simplify.
  apply Qle_trans with q1; auto.
  rewrite H1.
  ring_simplify. apply Qle_refl.
Qed.
Next Obligation.
  intros. split; intros [q ?].
  apply image_axiom2 in H.
  destruct H as [y [??]]; simpl in *.
  destruct (cut_nonextended x).
  destruct H1 as [z ?]; eauto.
  exists (- oneOver2n n + z)%Q.
  apply image_axiom1'. exists z. split; auto.
  apply image_axiom2 in H.
  destruct H as [y [??]]; simpl in *.
  destruct (cut_nonextended x).
  destruct H2 as [z ?]; eauto.
  exists (oneOver2n n + z)%Q.
  apply image_axiom1'. exists z. split; auto.
Qed.



Fixpoint pos_log2 (p:positive) : N :=
  match p with
    | xH => 1%N
    | xO p' => N.succ (pos_log2 p')
    | xI p' => N.succ (pos_log2 p')
  end.

Lemma pow2_succ (n:N) : (pow2 (N.succ n) = (pow2 n)~0)%positive.
Proof.
  destruct n.
  compute. auto.
  simpl.
  unfold shift_pos. simpl.
  rewrite Pos.iter_succ.
  auto.
Qed.    

Lemma pow2_pos_log2 (p:positive) : (p < pow2 (pos_log2 p))%positive.
Proof.
  red. unfold Pos.compare.
  generalize Eq.
  induction p.
  simpl; intros.
  rewrite pow2_succ.
  simpl. apply IHp.
  simpl; intros.
  rewrite pow2_succ.
  simpl. apply IHp.
  simpl. auto.
Qed.    

Lemma oneOver2n_small : forall ε:Q, 0 < ε -> exists n, oneOver2n n <= ε.
Proof.
  intros.
  exists (pos_log2 (Qden ε)).
  destruct ε.
  red in H. simpl in H.
  ring_simplify in H.
  simpl.
  red; simpl.
  apply Z.le_trans with (1 * 'Qden)%Z.
  simpl. reflexivity.
  apply Zmult_le_compat.
  omega.
  cut ( Qden <  pow2 (pos_log2 Qden))%positive.
  zify. omega.
  apply pow2_pos_log2.
  omega.
  compute. discriminate.
Qed.

Definition near ε (x y:cut) :=
  (exists u l, u ∈ cut_upper x /\ l ∈ cut_lower y /\ u - l <= ε) /\
  (exists u l, u ∈ cut_upper y /\ l ∈ cut_lower x /\ u - l <= ε).

Definition is_limit (seq:N -> cut) (c:cut) :=
  forall ε:Q, ε > 0 ->
    exists m:N, forall (n:N), (m <= n)%N -> near ε (seq n) c.

Lemma is_limit_located seq lim : is_limit seq lim -> located lim.
Proof.
  red; intros.
  destruct (H (ε/(2#1))); auto.
  apply Qlt_shift_div_l.
  compute. auto.
  ring_simplify. auto.
  destruct (H1 x). reflexivity.
  destruct H2 as [u1 [l1 [?[??]]]].
  destruct H3 as [u2 [l2 [?[??]]]].
  exists u2. exists l1.
  split; auto. split; auto.
  rewrite <- (Qplus_le_l _ _ l1).
  rewrite <- (Qplus_le_l _ _ (-l2)).
  ring_simplify.
  apply Qle_trans with (ε/(2#1)).
  ring_simplify in H7; auto.
  rewrite <- (Qplus_le_l _ _ u1).
  rewrite <- (Qplus_le_l _ _ (-l1)).
  ring_simplify.
  apply Qle_trans with (ε/(2#1) + ε/(2#1) )%Q.
  rewrite <- Qplus_assoc.
  apply Qplus_le_compat. apply Qle_refl.
  ring_simplify in H5. auto.
  rewrite <- (Qplus_le_l _ _ l2).
  ring_simplify.
  field_simplify.
  cut (ε + l2 <= ε + u1).
  intros. field_simplify in H8. auto.
  apply Qplus_le_compat.
  apply Qle_refl.
  eapply cut_proper; eauto.
Qed.

Definition cauchy_sequence (seq:N -> cut) :=
  forall n m o,
     (o <= m)%N -> (o <= n)%N ->
        exists u, u ∈ cut_upper (seq m) /\
        exists l, l ∈ cut_lower (seq n) /\
        u - l <= oneOver2n o.

Section cut_cauchy_limit.
  Variable seq : N -> cut.
  Hypothesis seq_cauchy : cauchy_sequence seq.

  Program Definition limit_uppers (n:N) : eset Qpreord :=
    image (Preord.Hom _ _ (Qplus (oneOver2n n)) _) (cut_upper (seq n)).
  Next Obligation.
    intros. red; simpl.
    red in H. simpl in H. rewrite H. reflexivity.
  Qed.

  Program Definition limit_lowers (n:N) : eset Qpreord :=
    image (Preord.Hom _ _ (Qplus (-oneOver2n n)) _) (cut_lower (seq n)).
  Next Obligation.
    intros. red; simpl.
    red in H. simpl in H. rewrite H. reflexivity.
  Qed.
 
  Definition limit_upper : eset Qpreord :=
    union ( (fun n => Some (limit_uppers n)) : eset (eset Qpreord)).

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
    unfold limit_lowers in H2.
    apply image_axiom2 in H2.
    destruct H2 as [y' [??]].
    simpl in *.
    destruct H2 as [? _]. red in H2. simpl in H2. rewrite H2.
    destruct (seq_cauchy n m (N.min n m)) as [u' [? [l' [??]]]].
    apply N.le_min_r.
    apply N.le_min_l.
    assert (y' <= u'). eapply cut_proper; eauto.
    assert (l' <= y). eapply cut_proper; eauto.
    rewrite <- (Qplus_le_l _ _ (oneOver2n m)).
    ring_simplify. 
    apply Qle_trans with u'; auto.
    rewrite <- (Qplus_le_l _ _ (-l')).
    apply Qle_trans with (oneOver2n (N.min n m)).
    ring_simplify in H5. ring_simplify. auto.
    rewrite <- (Qplus_le_l _ _ (l')). ring_simplify.
    apply Qplus_le_compat; auto.
    apply N.min_case.
    rewrite <- (Qplus_le_l _ _ (-oneOver2n n)). ring_simplify.
    apply Qlt_le_weak. apply oneOver2n_pos.
    rewrite <- (Qplus_le_l _ _ (-oneOver2n m)). ring_simplify.
    apply Qlt_le_weak. apply oneOver2n_pos.
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
    exists (q1 + oneOver2n n)%Q.
    split.
    split; red; simpl; ring.
    apply cut_is_lower with q; auto.
    apply Qle_trans with (q2 + oneOver2n n)%Q.
    apply Qplus_le_compat; auto. apply Qle_refl.
    destruct H2. red in H2; simpl in H2. rewrite H2.
    ring_simplify. apply Qle_refl.
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
    exists (q2 - oneOver2n n)%Q.
    split.
    split; red; simpl; ring.
    apply cut_is_upper with q; auto.
    apply Qle_trans with (q1 - oneOver2n n)%Q.
    destruct H2. red in H2; simpl in H2. rewrite H2.
    ring_simplify. apply Qle_refl.
    apply Qplus_le_compat; auto. apply Qle_refl.
  Qed.
  Next Obligation.
    unfold limit_upper, limit_lower.
    destruct (seq_cauchy 0 0 0)%N as [u [? [l [??]]]]. 
    reflexivity.
    reflexivity.
    split; intros.
    exists (-oneOver2n 0 + l)%Q.
    apply union_axiom.
    exists (limit_lowers 0).
    split. exists 0%N. auto.
    unfold limit_lowers.
    apply image_axiom1'.
    simpl.
    exists l. split; auto.
    exists (oneOver2n 0 + u)%Q.
    apply union_axiom.
    exists (limit_uppers 0).
    split. exists 0%N. auto.
    unfold limit_lowers.
    apply image_axiom1'.
    simpl.
    exists u. split; auto.
  Qed.    


  Lemma limit_correct : is_limit seq limit.
  Proof.
    red; intros.
    destruct (oneOver2n_small ε) as [m ?]; auto.
    exists (m+1)%N. intros.
    split.
    destruct (seq_cauchy (m+1) n (m+1))%N as [u [? [l [??]]]]; auto.
    reflexivity.
    exists u. exists (-oneOver2n (m+1) + l)%Q. split; auto. split.
    simpl.
    unfold limit_lower.
    apply union_axiom.
    exists (limit_lowers (m+1)).
    split. exists (m+1)%N. auto.
    unfold limit_lowers.
    apply image_axiom1'; simpl.
    exists l. split; auto.
    rewrite <- (Qplus_le_l _ _ (-oneOver2n (m+1))).
    ring_simplify.
    apply Qle_trans with (oneOver2n (m+1)).
    ring_simplify in H4. auto.
    rewrite <- (Qplus_le_l _ _ (oneOver2n (m+1))).
    ring_simplify.
    rewrite <- oneOver2n_commute.
    unfold oneOver2n at 2. simpl.
    unfold shift_pos. simpl.
    field_simplify.
    field_simplify in H0. auto.
            
    destruct (seq_cauchy n (m+1) (m+1))%N as [u [? [l [??]]]]; auto.
    reflexivity.
    exists (oneOver2n (m+1) + u)%Q. exists l. split; auto. 
    simpl.
    unfold limit_upper.
    apply union_axiom.
    exists (limit_uppers (m+1)).
    split. exists (m+1)%N. auto.
    unfold limit_uppers.
    apply image_axiom1'; simpl.
    exists u. split; auto.
    split; auto.
    rewrite <- (Qplus_le_l _ _ (-oneOver2n (m+1))).
    ring_simplify.
    apply Qle_trans with (oneOver2n (m+1)).
    ring_simplify in H4. auto.
    rewrite <- (Qplus_le_l _ _ (oneOver2n (m+1))).
    ring_simplify.
    rewrite <- oneOver2n_commute.
    unfold oneOver2n at 2. simpl.
    unfold shift_pos. simpl.
    field_simplify.
    field_simplify in H0. auto.
  Qed.

  Lemma located_limit : located limit.
  Proof.
    eapply is_limit_located. apply limit_correct.
  Qed.
End cut_cauchy_limit.

End cauchy_limit_cuts.

