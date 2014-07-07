(* Copyright (c) 2014, Robert Dockins *)

Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import cpo.
Require Import algebraic.

Require Import directed.
Require Import plotkin.
Require Import effective.

Section ideal_completion.
  Variable hf:bool.
  Let CL := directed_hf_cl hf.

  Variable Ktype:Type.
  Variable Kmixin:Preord.mixin_of Ktype.
  Let K := Preord.Pack Ktype Kmixin.

  Variable Kdec : forall x y:K, {x ≤ y}+{x ≰ y}.
  Variable Kenum : eset K.
  Variable Kenum_complete : forall k:K, k ∈ Kenum.

  Program Definition enum_lowerset (k:K) : cl_eset CL K :=
    esubset_dec K (fun k' => k' ≤ k) (fun k' => Kdec k' k) Kenum .
  Next Obligation.
    simpl. intros.
    apply prove_directed.
    destruct hf; auto.
    exists k. apply esubset_dec_elem.
    intros. rewrite <- H; auto.
    split; auto.
    simpl; intros.
    rewrite esubset_dec_elem in H.
    rewrite esubset_dec_elem in H0.
    exists k. intuition.
    rewrite esubset_dec_elem. split; auto.
    intros. rewrite <- H0; auto.
    intros. rewrite <- H1; auto.
    intros. rewrite <- H1; auto.
  Qed.

  Lemma enum_complete : forall k x, 
    x ≤ k <-> x ∈ (enum_lowerset k).
  Proof.
    simpl. intros. split; intros.
    unfold enum_lowerset. simpl.
    apply esubset_dec_elem; intuition.
    rewrite <- H0; auto.
    red in H. simpl in H.
    apply esubset_dec_elem in H. destruct H; auto.
    intros. rewrite <- H0; auto.
  Qed.
  
  Lemma enum_is_lowerset : forall k, lower_set (enum_lowerset k).
  Proof.
    intros. red. intros.
    apply enum_complete.
    apply enum_complete in H0.
    eauto.
  Qed.

  Definition ideal_type := { X:cl_eset CL K | lower_set X }.

  Program Definition ideal_mixin : Preord.mixin_of ideal_type :=
    Preord.Mixin
    ideal_type 
    (fun X Y => proj1_sig X ⊆ proj1_sig Y) _ _.
  Next Obligation.
    intros. hnf; auto.
  Qed.
  Next Obligation.
    intros. hnf; auto.
  Qed.

  Canonical Structure ideal : preord := Preord.Pack ideal_type ideal_mixin.

  Program Definition ideal_forget : ideal → cl_eset CL K :=
    Preord.Hom ideal (cl_eset CL K) (@proj1_sig _ _) _.
  Next Obligation.
    auto.
  Qed.

  Program Definition principal_ideal : K → ideal :=
    Preord.Hom K ideal
      (fun k => exist lower_set (enum_lowerset k) (enum_is_lowerset k))
      _.
  Next Obligation.
    intros.
    red. simpl.
    red. intros k Hk.
    apply enum_complete in Hk.
    apply enum_complete.
    eauto.
  Qed.


  Program Definition ideal_sup (D:cl_eset CL ideal) : ideal :=
    ∪ (image ideal_forget D).
  Next Obligation.
    intros. apply color_union; auto.
    apply color_image. apply proj2_sig.
    intros.
    apply image_axiom2 in H.
    destruct H as [Y [??]].
    eapply color_eq. symmetry. apply H0.
    destruct Y as [Y HY].
    apply HY.
  Qed.
  Next Obligation.
    intros.
    red; simpl; intros.
    unfold set.member. simpl.
    unfold set.member in H0. simpl in H0.
    apply union_axiom in H0.
    apply union_axiom.
    destruct H0 as [X [??]].
    exists X. split; auto.
    apply image_axiom2 in H0.
    destruct H0 as [Y [??]].
    apply image_axiom2 in H0.
    destruct H0 as [Y' [??]].
    destruct H2.
    apply H4.
    simpl.
    destruct H3.
    apply H5.
    destruct Y' as [Y' HY].
    simpl.
    apply HY with b; auto.
    simpl in *.
    apply H3. apply H2. auto.
  Qed.
    

  Lemma ideal_way_below : forall (k:K) (I J:ideal),
    I ≤ principal_ideal k -> principal_ideal k ≤ J ->
    way_below CL I J.
  Proof.
    intros. red. intros.
    red in H; simpl in H.
    red in H0. simpl in H0.
    red in H2. simpl in H2.
    set (z := ideal_sup D).
    destruct H1.
    assert (lub ≤ z).
    apply H3.
    red. intros.
    unfold z.
    red. simpl. red. simpl.
    intros.
    unfold set.member. simpl.
    apply union_axiom.
    exists (colored_sets.forget_color _ _ _ (ideal_forget x)).
    split; auto.
    apply image_axiom1.
    apply image_axiom1. auto.
    assert (k ∈ proj1_sig z).
    apply H4.
    apply H2.
    apply  H0.
    apply enum_complete.
    auto.
    assert (z ≤ lub).
    red. red. simpl. red. intros.
    unfold set.member in H6.
    simpl in H6.
    apply union_axiom in H6.
    destruct H6 as [X [??]].
    apply image_axiom2 in H6.
    destruct H6 as [Y [??]].
    apply image_axiom2 in H6.
    destruct H6 as [Y' [??]].
    red in H1.
    apply (H1 Y'); auto.
    destruct H9. apply H9.
    destruct H8. apply H8; auto.

    unfold z in H5.
    unfold ideal_sup in H5.
    simpl in H5.
    unfold set.member in H5.
    simpl in H5.
    apply union_axiom in H5.
    destruct H5 as [d [??]].
    apply image_axiom2 in H5.
    destruct H5 as [d' [??]].
    apply image_axiom2 in H5.
    destruct H5 as [d'' [??]].
    exists d''.
    split; auto.
    red. simpl.
    red. intros.
    apply H in H10.
    apply enum_complete in H10.
    destruct d'' as [d'' ?].
    simpl.
    apply l with k; auto.
    destruct H9.
    apply H9.
    destruct H8.
    apply H8. auto.
  Qed.    

  Lemma ideal_sup_upper_bound : forall X, upper_bound (ideal_sup X) X.
  Proof.
    intros. red. intros.
    red. simpl; intros.
    red. simpl; intros.
    apply union_axiom.
    exists (colored_sets.forget_color _ _ _  (ideal_forget x)). split; auto.
    apply image_axiom1. 
    apply image_axiom1. 
    auto.
  Qed.

  Lemma ideal_sup_least_bound : forall X ub,
    upper_bound ub X -> ideal_sup X ≤ ub.
  Proof.
    intros.
    hnf. intros.
    unfold ideal_sup in H0.
    red in H0. simpl in H0.
    apply union_axiom in H0.
    destruct H0 as [Q [??]].
    apply image_axiom2 in H0.
    destruct H0 as [Y [??]].
    apply image_axiom2 in H0.
    destruct H0 as [Y' [??]].
    hnf in H.
    assert (Y' ≤ ub).
    apply H; auto.
    red in H4.
    simpl in H4.
    apply H4.
    destruct H3.
    apply H3.
    destruct H2.
    apply H2. auto.
  Qed.    

  Lemma ideal_sup_least_upper_bound : forall X,
    least_upper_bound (ideal_sup X) X.
  Proof.
    intros; split.
    apply ideal_sup_upper_bound.
    apply ideal_sup_least_bound.
  Qed.

  Lemma ideal_reimage1 : forall I:ideal,
    I ≤ ideal_sup (image principal_ideal (ideal_forget#I)).
  Proof.
    repeat intro.
    simpl. red; simpl.
    apply union_axiom.
    exists (colored_sets.forget_color _ _ _(ideal_forget (principal_ideal a))).
    split.
    apply image_axiom1.
    apply image_axiom1.
    apply image_axiom1.
    auto.
    simpl.
    apply enum_complete. auto.
  Qed.

  Lemma ideal_reimage2 : forall I:ideal,
    ideal_sup (image principal_ideal (ideal_forget#I)) ≤ I.
  Proof.
    repeat intro.
    simpl in H.
    red in H. simpl in H.
    apply union_axiom in H.
    destruct H as [X [??]].
    apply image_axiom2 in H.
    destruct H as [Y [??]].
    apply image_axiom2 in H.
    destruct H as [Z [??]].
    apply image_axiom2 in H.
    destruct H as [k [??]].
    assert (a ∈ proj1_sig (principal_ideal k)).
    destruct H3. apply H3.
    destruct H2. apply H2.
    destruct H1. apply H1.
    auto.
    simpl in H4.
    apply enum_complete in H4.
    destruct I as [I HI].
    simpl.
    apply HI with k; auto.
  Qed.

  Lemma ideal_reimage : forall I:ideal,
    I ≈ ideal_sup (image principal_ideal (ideal_forget I)).
  Proof.
    intros; split.
    apply ideal_reimage1. apply ideal_reimage2.
  Qed.

  Lemma way_below_ideal : forall (I J:ideal),
    way_below CL I J -> exists k:K,
      I ≤ principal_ideal k /\ principal_ideal k ≤ J.
  Proof.
    intros. red in H.
    set (D := image principal_ideal (ideal_forget#J)).
    destruct (H D (ideal_sup D)) as [Z [??]].
    apply ideal_sup_least_upper_bound.
    unfold D.    
    apply ideal_reimage1.
    unfold D in H0.
    apply image_axiom2 in H0.
    destruct H0 as [k [??]].
    exists k. split; auto.
    destruct H2.
    eauto.
    red. simpl.
    red. simpl. intros.
    apply enum_complete in H3.
    destruct J.
    apply l with k; auto.
  Qed.

  Lemma principal_ideals_compact : forall k,
    compact CL (principal_ideal k).
  Proof.
    intros. red. apply ideal_way_below with k; auto.
  Qed.    

  Definition ideal_cpo_mixin
    : CPO.mixin_of CL ideal
    := CPO.Mixin CL ideal ideal_sup ideal_sup_upper_bound ideal_sup_least_bound.

  Program Definition ideal_algebraic_mixin
    : algebraic.mixin_of CL ideal K :=
    algebraic.Mixin CL ideal K
      principal_ideal
      Kdec
      Kenum
      Kenum_complete
      _
      principal_ideals_compact
      (fun (x:ideal) => proj1_sig x)
      _ _.
  Next Obligation.
    simpl; intros.
    red in H. simpl in H.
    apply enum_complete.
    apply H.
    apply enum_complete.
    auto.
  Qed.
  Next Obligation.
    intros. split.
    intro.
    apply (ideal_way_below k); auto.
    hnf; simpl; intros.
    destruct x as [x Hx]; simpl in *.
    eapply Hx. 2: apply H.
    rewrite <- enum_complete in H0. auto.

    intros.
    apply way_below_ideal in H.
    destruct H as [k' [??]].
    hnf in H0. simpl in H0.
    apply H0.
    rewrite <- enum_complete.
    hnf in H; simpl in H.
    rewrite enum_complete. apply H.
    rewrite <- enum_complete. auto.
  Qed.
  Next Obligation.
    simpl; intros.
    destruct x as [x ?]. simpl.
    split.
    red; simpl; intros.
    apply image_axiom2 in H. destruct H as [k [??]].
    rewrite H0. simpl.
    hnf; simpl; intros.
    rewrite <- enum_complete in H1.
    apply l with k; auto.
    simpl; intros.
    hnf; simpl; intros.
    hnf in H.
    apply H with (principal_ideal a).
    apply image_axiom1'.
    exists a; split; auto.
    simpl.
    rewrite <- enum_complete. auto.
  Qed.
End ideal_completion.



Module bifinite.
  Record class_of hf (A:preord) (K:preord) :=
    Class
    { cpo_mixin : CPO.mixin_of (directed_hf_cl hf) A
    ; alg_mixin : algebraic.mixin_of (directed_hf_cl hf) A K
    ; plt_mixin : plotkin_order hf K
    }. 

  Record type (hf:bool) :=
    Pack
    { carrier :> Type
    ; base_carrier : Type
    ; carrier_ord : Preord.mixin_of carrier
    ; base_ord : Preord.mixin_of base_carrier
    ; base := Preord.Pack base_carrier base_ord 
    ; ord := Preord.Pack carrier carrier_ord
    ; class : class_of hf ord base
    }.

  Canonical Structure tocpo hf (T:type hf) : CPO.type _ :=
    CPO.Pack _ (carrier _ T) (carrier_ord _ T) (cpo_mixin _ _ _ (class hf T)).

  Canonical Structure toalg hf (T:type hf) : algebraic.type _ :=
    algebraic.Pack _ (carrier hf T) (base hf T) (carrier_ord hf T) (base_ord hf T)
      (alg_mixin _ _ _ (class hf T)).
End bifinite.

Canonical Structure bifinite.tocpo.
Canonical Structure bifinite.toalg.
Coercion bifinite.tocpo : bifinite.type >-> CPO.type.
Coercion bifinite.toalg : bifinite.type >-> algebraic.type.

Require Import profinite.
Require Import effective.

Section plt_to_bifinite.
  Variable hf:bool.
  Variable A:PLT.PLT hf.

  Definition plt2bif_class :=
    bifinite.Class hf
      (ideal hf _ (Preord.mixin (PLT.ord A)))
      (PLT.ord A)
      (ideal_cpo_mixin hf _ (Preord.mixin (PLT.ord A)))
      (ideal_algebraic_mixin hf _ (Preord.mixin (PLT.ord A))
          (PLT.dec A)
          (eff_enum _ (PLT.effective A))
          (eff_complete _ (PLT.effective A)))
      (PLT.cls_plotkin hf _ (PLT.class hf A)).

  Definition plt2bif :=
    bifinite.Pack hf _ _
      (Preord.mixin (ideal hf _ (Preord.mixin (PLT.ord A))))
      (Preord.mixin (PLT.ord A))
      plt2bif_class.

End plt_to_bifinite.
