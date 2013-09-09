Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import cpo.
Require Import algebraic.

Section ideal_completion.
  Variable CL:color.
  Variable Ktype:Type.
  Variable Kmixin:Preord.mixin_of Ktype.
  Let K := Preord.Pack Ktype Kmixin.

  Variable Kdec : forall x y:K, {x ≤ y}+{x ≰ y}.

  Variable enum_lowerset : K -> cl_eset CL K.
  Hypothesis enum_complete : forall k x, 
    x ≤ k <-> x ∈ (enum_lowerset k).
  
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

(*
  Program Definition basis_inj : K ↣ ideal :=
    Monomorphism PREORD K ideal principal_ideal _.
  Next Obligation.
    intros.
    intro x; split.
    destruct (H x).
    red in H0. simpl in H0.
    red in H1. simpl in H1.
    red.
    red in H0. red in H1.
    assert (g#x ∈ enum_lowerset (Preord.map X K h x)).
    apply H0.
    rewrite <- enum_complete; auto.
    rewrite <- enum_complete in H2.
    auto.

    destruct (H x).
    red in H0. simpl in H0.
    red in H1. simpl in H1.
    red.
    red in H0. red in H1.
    assert (h#x ∈ enum_lowerset (Preord.map X K g x)).
    apply H1.
    rewrite <- enum_complete; auto.
    rewrite <- enum_complete in H2.
    auto.
  Qed.    
*)

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
    I ≤ principal_ideal#k -> principal_ideal#k ≤ J ->
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
    exists (colored_sets.forget_color _ _ _ #ideal_forget#x).
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
    exists (colored_sets.forget_color _ _ _ #ideal_forget#x). split; auto.
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
    exists (colored_sets.forget_color _ _ _#ideal_forget#principal_ideal#a).
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
    assert (a ∈ proj1_sig (principal_ideal#k)).
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
    I ≈ ideal_sup (image principal_ideal (ideal_forget#I)).
  Proof.
    intros; split.
    apply ideal_reimage1. apply ideal_reimage2.
  Qed.

  Lemma way_below_ideal : forall (I J:ideal),
    way_below CL I J -> exists k:K,
      I ≤ principal_ideal#k /\ principal_ideal#k ≤ J.
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
    compact CL (principal_ideal#k).
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
      (fun (x:ideal) => proj1_sig x)
      _
      principal_ideals_compact
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
    red. simpl. intros.
    unfold set.member in H. simpl in H.
    apply image_axiom2 in H.
    destruct H as [y [??]].
    destruct H0.
    rewrite H0.
    red; simpl. red; simpl; intros.
    apply enum_complete in H2.
    destruct x as [x ?].
    simpl.
    apply (l a y); auto.
    intros.
    red. simpl. red. intros.
    fold ideal in *.
    generalize (H (principal_ideal#a)).
    intros.
    assert (principal_ideal#a ≤ b).
    apply H1.
    apply image_axiom1. auto.
    red in H2.
    simpl in H2.
    apply H2.
    apply enum_complete. auto.
  Qed.    
  Next Obligation.
    simpl; intros.
    destruct x as [x ?]. simpl.
    split. intros.
    red. simpl.
    red; simpl; intros.
    apply enum_complete in H0.
    apply l with k; auto.
    simpl; intros.
    red in H; simpl in H.
    apply (H k).
    apply enum_complete. auto.
  Qed.
End ideal_completion.

Record abstract_basis (CL:color) :=
  AbstractBasis
  { ab_carrier :> Type
  ; ab_ord_mixin : Preord.mixin_of ab_carrier
  ; ab_ord := Preord.Pack ab_carrier ab_ord_mixin
  ; ab_dec : forall x y:ab_ord, {x ≤ y}+{x ≰ y}
  ; ab_enum : ab_ord -> cl_eset CL ab_ord
  ; ab_enum_complete : forall k x, x ≤ k <-> x ∈ (ab_enum k)
  }.

Module alg_cpo.
  Record class_of CL (A:preord) (K:preord) :=
    Class
    { cpo_mixin : CPO.mixin_of CL A
    ; alg_mixin : algebraic.mixin_of CL A K
    }.

  Record type CL :=
    Pack
    { carrier :> Type
    ; base : Type
    ; carrier_ord : Preord.mixin_of carrier
    ; base_ord : Preord.mixin_of base
    ; ord := Preord.Pack carrier carrier_ord
    ; basis := Preord.Pack base base_ord
    ; class : class_of CL ord basis
    }.

  Canonical Structure tocpo CL (T:type CL) : cpo CL :=
    CPO.Pack CL (carrier CL T) (carrier_ord CL T) (cpo_mixin _ _ _ (class CL T)).

  Canonical Structure toalg CL (T:type CL) : algebraic.type CL :=
    algebraic.Pack CL (carrier CL T) (base CL T) (carrier_ord CL T) (base_ord CL T)
      (alg_mixin _ _ _ (class CL T)).
End alg_cpo.
Canonical Structure alg_cpo.tocpo.
Canonical Structure alg_cpo.toalg.
Coercion alg_cpo.tocpo : alg_cpo.type >-> CPO.type.
Coercion alg_cpo.toalg : alg_cpo.type >-> algebraic.type.

Canonical Structure ab_ord.
Coercion ab_ord : abstract_basis >-> preord.

Program Definition algebraic_basis CL (T:algebraic.type CL) : abstract_basis CL :=
  AbstractBasis CL
    (algebraic.base CL T)
    (algebraic.base_ord CL T)
    (algebraic.algebraic.basis_dec _ _ _ (algebraic.mixin CL T))
    (fun k => algebraic.decomp _ _ _ (algebraic.mixin CL T)
       (algebraic.basis_inj _ _ _ (algebraic.mixin CL T)#k))
    _.
Next Obligation.
  simpl; intros.
  split; intros.
  apply algebraic.decomp_complete.
  apply Preord.axiom. auto.
  apply algebraic.decomp_complete in H.
  apply algebraic.basis_inj_reflects in H. auto.
Qed.  

Canonical Structure ideal_alg_cpo CL (B:abstract_basis CL) : alg_cpo.type CL :=
  alg_cpo.Pack CL
     (ideal_type CL (ab_carrier CL B) (ab_ord_mixin CL B))
     (ab_carrier CL B)
     (ideal_mixin CL (ab_carrier CL B) (ab_ord_mixin CL B))
     (ab_ord_mixin CL B)
     (alg_cpo.Class _ _ _
       (ideal_cpo_mixin CL (ab_carrier CL B) (ab_ord_mixin CL B))
       (ideal_algebraic_mixin CL
        (ab_carrier CL B)
        (ab_ord_mixin CL B)
        (ab_dec CL B)
        (ab_enum CL B)
        (ab_enum_complete CL B))).
 
(*Canonical Structure ideal_algebraic CL (B:abstract_basis CL) : algebraic.type CL :=
   algebraic.Pack CL
     (ideal_type CL (ab_carrier CL B) (ab_ord_mixin CL B))
     (ab_carrier CL B)
     (ideal_mixin CL (ab_carrier CL B) (ab_ord_mixin CL B))
     (ab_ord_mixin CL B)
     (ideal_algebraic_mixin CL
       (ab_carrier CL B)
       (ab_ord_mixin CL B)
       (ab_dec CL B)
       (ab_enum CL B)
       (ab_enum_complete CL B)).

Canonical Structure ideal_cpo CL (B:abstract_basis CL) : CPO.type CL :=
   CPO.Pack CL
     (ideal_type CL (ab_carrier CL B) (ab_ord_mixin CL B))
     (ideal_mixin CL (ab_carrier CL B) (ab_ord_mixin CL B))
     (ideal_cpo_mixin CL (ab_carrier CL B) (ab_ord_mixin CL B)).
*)

Record approx_rel CL (X Y:abstract_basis CL) :=
  ApproxRel
  { apx_rel :> ab_ord CL X → ideal CL _ (ab_ord_mixin CL Y)
  }.

Program Definition cont_func_approx_rel CL (X Y:alg_cpo.type CL)
  (f:CPO.hom CL X Y) 
  : approx_rel CL (algebraic_basis CL X) (algebraic_basis CL Y)

  := ApproxRel CL _ _
       (Preord.Hom _ _ 
         (fun x => 
           algebraic.decomp _ _ _ (algebraic.mixin _ Y)
             (CPO.map f (algebraic.basis_inj _ _ _ (algebraic.mixin _ X)#x))) _).
Next Obligation.           
  simpl; intros. apply proj2_sig.
Qed.
Next Obligation.
  simpl; intros.
  red; intros.
  red in H0. simpl in H0.
  apply (algebraic.decomp_complete CL (algebraic.ord CL Y) 
               (algebraic.basis CL Y)
               (alg_cpo.alg_mixin CL (alg_cpo.ord CL Y) 
                  (alg_cpo.basis CL Y) (alg_cpo.class CL Y))).
  transitivity (algebraic.basis_inj CL (algebraic.ord CL Y) (algebraic.basis CL Y)
     (alg_cpo.alg_mixin CL (alg_cpo.ord CL Y) (alg_cpo.basis CL Y)
        (alg_cpo.class CL Y)) # b).
  apply Preord.axiom. auto.
  apply (algebraic.decomp_complete CL (algebraic.ord CL Y) 
               (algebraic.basis CL Y)
               (alg_cpo.alg_mixin CL (alg_cpo.ord CL Y) 
                  (alg_cpo.basis CL Y) (alg_cpo.class CL Y))).
  auto.
Qed.
Next Obligation.
  repeat intro. simpl in *.
  red in H0. red. simpl in *.
  apply (algebraic.decomp_complete CL (algebraic.ord CL Y) 
               (algebraic.basis CL Y)
               (alg_cpo.alg_mixin CL (alg_cpo.ord CL Y) 
                  (alg_cpo.basis CL Y) (alg_cpo.class CL Y))).
  transitivity
    (CPO.map f
       (Preord.map (algebraic.basis CL X) X
          (algebraic.basis_inj CL X (algebraic.basis CL X)
             (alg_cpo.alg_mixin CL (alg_cpo.ord CL X) 
                (alg_cpo.basis CL X) (alg_cpo.class CL X))) a)).
  apply (algebraic.decomp_complete CL (algebraic.ord CL Y) 
               (algebraic.basis CL Y)
               (alg_cpo.alg_mixin CL (alg_cpo.ord CL Y) 
                  (alg_cpo.basis CL Y) (alg_cpo.class CL Y))); auto.
  apply (CPO.mono f).
  apply Preord.axiom.
  auto.
Qed.

Program Definition approx_rel_cont_func CL (X Y:abstract_basis CL) 
  (R:approx_rel CL X Y) 
  : CPO.hom CL (ideal_alg_cpo CL X) (ideal_alg_cpo CL Y) :=

  CPO.Hom CL (ideal_alg_cpo CL X) (ideal_alg_cpo CL Y)
    (fun x => @CPO.sup_op CL (ideal_alg_cpo CL Y) 
                (image R (proj1_sig x))) _ _.
Next Obligation.
  intros.  
  apply CPO.sup_is_least.
  red; intros.
  apply image_axiom2 in H0.
  destruct H0 as [y[??]].
  apply CPO.sup_is_ub.
  rewrite H1.
  apply image_axiom1.
  apply H. auto.
Qed.
Next Obligation.
  intros.
  apply CPO.sup_is_least.
  red; intros.
  apply image_axiom2 in H.
  destruct H as [y [??]].
  red in H. simpl in H.
  apply union_axiom in H.
  destruct H as [Q [??]].
  apply image_axiom2 in H.
  destruct H as [Z [??]].
  apply image_axiom2 in H.
  destruct H as [W[??]].
  simpl in H2.
  simpl in H3.
  match goal with [ |- x ≤ ∐(image ?Q X0) ] => set (f := Q) end.
  set (piX := principal_ideal CL (ab_carrier CL X) (ab_ord_mixin CL X) (ab_enum CL X) (ab_enum_complete CL X)).
  transitivity (f#(piX#y)).
  simpl.
  apply CPO.sup_is_ub.
  rewrite H0.
  apply image_axiom1.
  apply ab_enum_complete. auto.
  transitivity (f#W).
  apply Preord.axiom.
  unfold piX. simpl.
  red; simpl.
  red; simpl; intros.
  apply ab_enum_complete in H4.
  destruct W; simpl.
  apply l with y; auto.
  simpl in *.
  destruct H3. apply H3.
  destruct H2.
  apply H2. auto.
  apply CPO.sup_is_ub.
  apply image_axiom1.
  auto.
Qed.  


Program Definition lift_abstract_basis
  (AB:abstract_basis semidirected)
  : abstract_basis directed :=
  AbstractBasis directed
    (option (ab_carrier _ AB))
    (lift_mixin (ab_ord _ AB))
    _
    (fun x => match x with
              | None => single (@None (ab_ord _ AB))
              | Some x' => union2 
                            (single None)
                            (image (liftup _) (ab_enum _ AB x'))
              end)
    _.
Next Obligation.
  simpl. intros.
  destruct x.
  destruct y.
  destruct (ab_dec _ AB a a0).
  left; auto.
  right; auto.
  right. intro. apply H.
  left. hnf; auto.
Defined.
Next Obligation.
  simpl; intros. intuition. subst x.
  exists None.
  apply union2_elem.
  left. apply single_axiom. auto.
  apply union2_elem in H.
  apply union2_elem in H0.
  intuition.
  apply single_axiom in H.
  apply single_axiom in H1.
  exists None.
  split.
  apply union2_elem. left. apply single_axiom. auto.
  split; auto.
  apply single_axiom in H1.
  exists b. split; auto.
  apply union2_elem. right; auto.
  split; auto.
  transitivity (@None (ab_ord _ AB)).
  destruct H1; auto. hnf. auto.
  apply single_axiom in H.
  exists a.
  split. apply union2_elem. right; auto.
  split; auto.
  transitivity (@None (ab_ord _ AB)).
  destruct H; auto.
  hnf; auto.
  apply image_axiom2 in H.
  apply image_axiom2 in H1.
  destruct H as [y1 [??]].
  destruct H1 as [y2 [??]].
  assert (color_prop semidirected (ab_enum _ AB x')).
  destruct (ab_enum semidirected AB x'); auto.
  destruct (H3 y1 y2) as [y3 [?[??]]]; auto.
  exists (liftup (ab_ord _ AB)#y3).
  split.
  apply union2_elem. right.
  apply image_axiom1. auto.
  split.
  transitivity (liftup _#y2).
  destruct H2; auto.
  apply Preord.axiom. auto.
  transitivity (liftup _#y1).
  destruct H0; auto.
  apply Preord.axiom. auto.
Qed.
Next Obligation.
  simpl. intuition.
  destruct k; simpl.
  red; simpl.
  apply union2_elem.
  destruct x. red in H. simpl in H.
  right.
  apply (image_axiom1 _ _ _ (liftup _) (proj1_sig (ab_enum _ AB a))).
  apply ab_enum_complete. auto.
  left. apply single_axiom; auto.
  destruct x. elim H.
  apply single_axiom. auto.

  destruct k; simpl in *.
  destruct x; simpl; auto.
  2: hnf; auto.
  red; simpl.
  red in H.
  simpl in H.
  apply union2_elem in H.
  destruct H.
  apply single_axiom in H.
  destruct H. elim H.
  apply (image_axiom2) in H.
  destruct H as [y [??]].
  destruct H0.
  simpl in H0.
  red in H0. simpl in H0.
  assert (y ≤ a).
  apply ab_enum_complete; auto.
  eauto.
  apply single_axiom in H.
  destruct H; auto.
Qed.
