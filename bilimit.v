Require Import Setoid.
Require Import List.

Require Import basics.
Require Import categories.
Require Import preord.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import plotkin.
Require Import profinite.
Require Import directed.
Require Import cpo.

Record directed_system (I:directed_preord) (C:category) :=
  DirSys
  { ds_F    : I -> ob C
  ; ds_hom : forall i j:I, i ≤ j -> ds_F i → ds_F j
  ; ds_ident : forall i (Hii:i≤i), ds_hom i i Hii ≈ id
  ; ds_compose : forall i j k (Hij:i≤j) (Hjk:j≤k) (Hik:i≤k),
                       ds_hom j k Hjk ∘ ds_hom i j Hij ≈ ds_hom i k Hik
  }.
Arguments ds_F [I] [C] _ _.
Arguments ds_hom [I] [C] _ _ _ _.
Arguments ds_ident [I] [C] _ _ _.
Arguments ds_compose [I] [C] _ _ _ _ _ _ _.

Record cocone (I:directed_preord) C (DS:directed_system I C) :=
  Cocone
  { cocone_point :> ob C
  ; cocone_spoke : forall i, ds_F DS i → cocone_point
  ; cocone_commute : forall i j (Hij:i≤j),
       cocone_spoke i ≈ cocone_spoke j ∘ ds_hom DS i j Hij
  }.
Arguments cocone [I] [C] DS.
Arguments Cocone [I] [C] DS _ _ _.
Arguments cocone_point [I] [C] [DS] _.
Arguments cocone_spoke [I] [C] [DS] _ _.
Arguments cocone_commute [I] [C] [DS] _ _ _ _.

Record directed_colimit (I:directed_preord) C (DS:directed_system I C) 
  (XC:cocone DS) :=
  DirectedColimit
  { colim_univ : forall (YC:cocone DS), XC → YC
  ; colim_commute : forall (YC:cocone DS) i,
       cocone_spoke YC i ≈ colim_univ YC ∘ cocone_spoke XC i
  ; colim_uniq : forall (YC:cocone DS) (f:XC → YC),
       (forall i, cocone_spoke YC i ≈ f ∘ cocone_spoke XC i) ->
       f ≈ colim_univ YC
  }.
Arguments directed_colimit [I] [C] DS XC.
Arguments DirectedColimit [I] [C] DS XC _ _ _.
Arguments colim_univ [I] [C] [DS] [XC] _ YC.
Arguments colim_commute [I] [C] [DS] [XC] _ _ _.
Arguments colim_uniq [I] [C] [DS] [XC] _ YC f _.

Program Definition dir_sys_app I C D
  (DS:directed_system I C) (F:functor C D)
  : directed_system I D:=

  DirSys I D
    (fun i => F (ds_F DS i))
    (fun i j Hij => F@(ds_hom DS i j Hij))
    _ _.
Next Obligation.
  intros.
  apply Functor.ident.
  apply ds_ident.
Qed.
Next Obligation.
  intros.
  rewrite <- Functor.compose.
  reflexivity.
  symmetry; apply ds_compose.
Qed.  
Arguments dir_sys_app [I] [C] [D] DS F.

Program Definition cocone_app I C D (DS:directed_system I C)
  (CC:cocone DS) (F:functor C D)
  : cocone (dir_sys_app DS F) :=

  Cocone (dir_sys_app DS F) (F CC) (fun i => F@cocone_spoke CC i) _.
Next Obligation.
  simpl; intros.
  rewrite <- (Functor.compose F). 2: reflexivity.
  rewrite <- (cocone_commute CC i j Hij).
  auto.
Qed.
Arguments cocone_app [I] [C] [D] [DS] CC F.

Definition continuous_functor (C D:category) (F:functor C D) :=
  forall I (DS:directed_system I C) (CC:cocone DS),
    directed_colimit DS CC ->
    directed_colimit (dir_sys_app DS F) (cocone_app CC F).
Arguments continuous_functor [C] [D] F.

Section bilimit.
  Variable hf:bool.
  Variable I:directed_preord.
  Variable DS:directed_system I (EMBED hf).

(*
  Lemma choose_ub_set (M:finset I) (HM:inh hf M) : { k:I | upper_bound k M }.
  Proof.
    set (M' := esubset_dec I (fun x => upper_bound x M)
            (upper_bound_dec I (ds_Ieff hf I DS) M)
            (eff_enum I (ds_Ieff hf I DS))).
    assert (einhabited M').
    apply member_inhabited.
    destruct (ds_Idir hf I DS M) as [k [??]]; auto.
    hnf; intros. apply eff_complete.
    exists k.
    unfold M'.
    apply esubset_dec_elem.
    apply upper_bound_ok.
    split; auto.
    destruct (find_inhabitant I M' H) as [k ?].
    exists k.
    destruct s as [n [??]].
    assert (k ∈ M').
    exists n. rewrite H0. auto.
    unfold M' in H2.
    apply esubset_dec_elem in H2.
    destruct H2; auto.
    apply upper_bound_ok.
  Qed.

  Lemma choose_ub (i j:I) : { k:I | i ≤ k /\ j ≤ k }.
  Proof.
    destruct (choose_ub_set (i::j::nil)%list).
    destruct hf; simpl; auto.
    exists i. apply cons_elem. auto.
    exists x.
    split; apply u.
    apply cons_elem; auto.
    apply cons_elem; right.
    apply cons_elem; auto.
  Qed.
*)

  Record limset :=
    LimSet
    { idx : I
    ; elem : ds_F DS idx
    }.

  Definition limset_order (x y:limset) :=
    exists k (Hxk : idx x ≤ k) (Hyk : idx y ≤ k),
      ds_hom DS (idx x) k Hxk (elem x) 
      ≤ ds_hom DS (idx y) k Hyk (elem y).

  Lemma limset_order_exists_forall x y :
    limset_order x y <->
    forall k (Hxk : idx x ≤ k) (Hyk : idx y ≤ k),
      ds_hom DS (idx x) k Hxk (elem x) 
      ≤ ds_hom DS (idx y) k Hyk (elem y).
  Proof.
    split; intros.
    destruct H as [k' [Hxk' [Hyk' ?]]].
    destruct (choose_ub I k k') as [q [??]].
    assert (Hxq : idx x ≤ q).
    transitivity k; auto.
    assert (Hyq : idx y ≤ q).
    transitivity k; auto.
    assert (ds_hom DS (idx x) q Hxq (elem x) ≤
            ds_hom DS (idx y) q Hyq (elem y)).
    rewrite <- (ds_compose DS (idx x) k' q Hxk' H1 Hxq).
    rewrite <- (ds_compose DS (idx y) k' q Hyk' H1 Hyq).
    simpl. apply embed_mono. auto.
    rewrite <- (ds_compose DS (idx x) k q Hxk H0 Hxq) in H2.
    rewrite <- (ds_compose DS (idx y) k q Hyk H0 Hyq) in H2.
    simpl in H2.

    (* FIXME? This might be the only actual use of this property,
       and this lemma is used only in the decidability proof below.
        
       Can we get rid of it by being a little more clever?
     *)
    apply embed_reflects in H2. auto.

    destruct (choose_ub I (idx x) (idx y)) as [k [??]].
    exists k, H0, H1.
    apply H.    
  Qed.

  Lemma limset_order_refl (x:limset) : limset_order x x.
  Proof.
    exists (idx x). exists (ord_refl _ _).  exists (ord_refl _ _). auto.
  Qed.

  Lemma limset_order_trans (x y z:limset) : 
    limset_order x y -> limset_order y z -> limset_order x z.
  Proof.
    intros [k1 [Hxk1 [Hyk1 ?]]].
    intros [k2 [Hyk2 [Hzk2 ?]]].
    destruct (choose_ub I k1 k2) as [k [??]].
    assert (Hxk : idx x ≤ k). transitivity k1; auto.
    assert (Hyk : idx y ≤ k). transitivity k1; auto.
    assert (Hzk : idx z ≤ k). transitivity k2; auto.
    exists k. exists Hxk. exists Hzk.
    transitivity (ds_hom DS (idx y) k Hyk (elem y)).
    rewrite <- (ds_compose DS (idx x) k1 k Hxk1 H1 Hxk).
    rewrite <- (ds_compose DS (idx y) k1 k Hyk1 H1 Hyk).
    simpl. apply embed_mono. auto.
    rewrite <- (ds_compose DS (idx y) k2 k Hyk2 H2 Hyk).
    rewrite <- (ds_compose DS (idx z) k2 k Hzk2 H2 Hzk).
    simpl. apply embed_mono. auto.
  Qed.

  Definition limord_mixin :=
    Preord.Mixin limset limset_order limset_order_refl limset_order_trans.

  Canonical Structure limord := Preord.Pack limset limord_mixin.

  Lemma limset_order_dec (x y:limset) :
    { limset_order x y } + { ~limset_order x y }.
  Proof.
    destruct (choose_ub I (idx x) (idx y)) as [k [??]].
    destruct (eff_ord_dec _ (PLT.effective (ds_F DS k))
                (ds_hom DS (idx x) k H (elem x))
                (ds_hom DS (idx y) k H0 (elem y))).
    left.
    exists k. exists H. exists H0. auto.
    right. intro.
    rewrite limset_order_exists_forall in H1.
    apply n. apply H1.
  Qed.

  Definition limset_enum : eset limord :=
    fun n => let (p,q) := pairing.unpairing n in
         match eff_enum _ (dir_effective I) p with
         | Some i =>
              match eff_enum _ (PLT.effective (ds_F DS i)) q with
              | Some x => Some (LimSet i x)
              | None => None
              end
         | None => None
         end.

  Program Definition limord_effective : effective_order limord :=
    EffectiveOrder limord limset_order_dec limset_enum _.
  Next Obligation.
    intros [i x].
    generalize (eff_complete _ (dir_effective I) i).
    intros [p ?].
    case_eq (eff_enum I (dir_effective I) p); intros.
    2: rewrite H0 in H; elim H.
    rewrite H0 in H.
    destruct H.
    set (x' := ds_hom DS i c H x).
    assert (x' ∈ eff_enum _ (PLT.effective (ds_F DS c))).
    apply eff_complete.
    destruct H2 as [q ?].
    case_eq (eff_enum _ (PLT.effective (ds_F DS c)) q); intros.
    2: rewrite H3 in H2; elim H2.
    rewrite H3 in H2.
    exists (pairing.pairing (p,q)).
    unfold limset_enum.
    rewrite pairing.unpairing_pairing.
    rewrite H0. rewrite H3.
    split.
    exists c. simpl. exists H. exists (ord_refl _ _).
    rewrite (ds_ident DS c (ord_refl _ _)). simpl. auto.
    exists c. simpl. exists (ord_refl _ _). exists H.
    rewrite (ds_ident DS c (ord_refl _ _)). simpl. auto.
  Qed.

  Lemma limord_has_normals : has_normals limord limord_effective hf.
  Proof.
    hnf. intros.
    destruct (choose_ub_set I (map idx X)) as [k ?].
    
    assert { M | X ≈ map (LimSet k) M }.
    clear Hinh.
    induction X.
    exists nil. simpl; auto.
    destruct IHX as [M ?].
    hnf; intros. apply u.
    simpl. apply cons_elem; auto.
    assert (Hak : idx a ≤ k).
    apply u. simpl. apply cons_elem; auto.
    exists (ds_hom DS (idx a) k Hak (elem a) :: M).
    split. hnf; simpl; intros.
    apply cons_elem in H.
    destruct H. rewrite H.
    apply cons_elem. left.
    split.
    exists k; simpl. exists Hak. exists (ord_refl _ _).
    rewrite (ds_ident DS k (ord_refl _ _)).
    simpl. auto.
    exists k; simpl. exists (ord_refl _ _). exists Hak.
    rewrite (ds_ident DS k (ord_refl _ _)).
    simpl. auto.
    apply cons_elem. right.
    rewrite <- e; auto.
    hnf; intros.
    simpl in H.
    apply cons_elem in H.
    destruct H.
    rewrite H.
    apply cons_elem. left.
    split.
    exists k; simpl. exists (ord_refl _ _). exists Hak.
    rewrite (ds_ident DS k (ord_refl _ _)).
    simpl. auto.
    exists k; simpl. exists Hak. exists (ord_refl _ _).
    rewrite (ds_ident DS k (ord_refl _ _)).
    simpl. auto.
    apply cons_elem. right.
    rewrite e; auto.
    
    destruct X0 as [M HM].
    exists (map (LimSet k) (mub_closure (PLT.plotkin (ds_F DS k)) M)).
    split.
    hnf; intros.
    rewrite HM in H.
    destruct H as [q [??]].
    apply in_map_iff in H.
    destruct H as [q' [??]].
    subst q.
    assert (q' ∈ mub_closure (PLT.plotkin (ds_F DS k)) M).
    apply mub_clos_incl. exists q'; auto.
    destruct H as [x [??]].
    rewrite H0.
    exists (LimSet k x).
    split.
    apply in_map. auto.
    split.
    exists k; simpl.
    exists (ord_refl _ _ ).
    exists (ord_refl _ _ ).
    apply embed_mono; auto.
    exists k; simpl.
    exists (ord_refl _ _ ).
    exists (ord_refl _ _ ).
    apply embed_mono; auto.
    split.
    revert Hinh. 
    unfold inh.
    pattern hf at 1 2. case hf; auto.
    intros [x ?].
    rewrite HM in H.
    destruct H as [x' [??]].
    apply in_map_iff in H.
    destruct H as [q [??]].
    subst x'.
    assert (q ∈ mub_closure (PLT.plotkin (ds_F DS k)) M).
    apply mub_clos_incl. exists q; split; auto.
    destruct H as [q' [??]].
    exists (LimSet k q').
    exists (LimSet k q').
    split; auto.
    apply in_map. auto.

    intros.
    apply prove_directed.
    generalize (refl_equal hf).
    pattern hf at 2. case hf; intros. 
    pattern hf at 1. rewrite H; auto.
    pattern hf at 1. rewrite H.
    destruct (choose_ub I (idx z) k) as [k' [Hzk' Hkk']].
    generalize (embed_directed0 (ds_hom DS k k' Hkk')
        (ds_hom DS (idx z) k' Hzk' (elem z))).
    rewrite H at 1.
    intros [q ?].
    destruct (mub_complete (PLT.plotkin (ds_F DS k)) nil q) as [q' [??]].
    hnf. pattern hf at 1. rewrite H. auto.
    hnf; simpl; intros. apply nil_elem in H1. elim H1.
    assert (q' ∈ mub_closure (PLT.plotkin (ds_F DS k)) M).
    apply mub_clos_mub with nil; auto.
    hnf. pattern hf at 1. rewrite H. auto.
    hnf. pattern hf at 1. rewrite H. auto.
    hnf; intros. apply nil_elem in H3; elim H3.
    destruct H3 as [q'' [??]].
    exists (LimSet k q'').
    apply finsubset_elem.
    intros. rewrite <- H5; auto.
    split.
    exists (LimSet k q'').
    split; auto.
    apply in_map. auto.
    exists k'. simpl. exists Hkk'. exists Hzk'.
    transitivity (ds_hom DS k k' Hkk' q); auto.
    apply embed_mono.
    rewrite <- H4; auto.

    intros.
    apply finsubset_elem in H.
    apply finsubset_elem in H0.
    destruct H. destruct H0.
    destruct H as [x' [??]].
    destruct H0 as [y' [??]].
    apply in_map_iff in H.
    destruct H as [x'' [??]].
    apply in_map_iff in H0.
    destruct H0 as [y'' [??]].
    subst x' y'.
    rewrite H3 in H1. rewrite H4 in H2.
    destruct H1 as [k' [Hkk' [Hzk' ?]]]. simpl in *.

    destruct H2 as [l [Hl1 [Hl2 ?]]]. simpl in *.
    destruct (choose_ub I k' l) as [m [Hm1 Hm2]].
    assert (Hkm : k ≤ m). 
    transitivity k'; auto.
    assert (Hzm : idx z ≤ m).
    transitivity k'; auto.

    destruct (embed_directed2 (ds_hom DS k m Hkm)
      (ds_hom DS (idx z) m Hzm (elem z)))
      with x'' y'' as [c [?[??]]]; auto.
    rewrite <- (ds_compose DS k k' m Hkk' Hm1 Hkm).
    rewrite <- (ds_compose DS (idx z) k' m Hzk' Hm1 Hzm).
    simpl. apply embed_mono. auto.
    rewrite <- (ds_compose DS k l m Hl1 Hm2 Hkm).
    rewrite <- (ds_compose DS (idx z) l m Hl2 Hm2 Hzm).
    simpl. apply embed_mono. auto.

    destruct (mub_complete (PLT.plotkin (ds_F DS k))
      (x''::y''::nil) c) as [c' [??]].
    apply elem_inh with x''. apply cons_elem; auto.
    hnf; simpl; intros.
    apply cons_elem in H8. destruct H8.
    rewrite H8; auto.
    apply cons_elem in H8. destruct H8.
    rewrite H8; auto.
    apply nil_elem in H8. elim H8.
    assert (c' ∈ mub_closure (PLT.plotkin (ds_F DS k)) M).
    apply mub_clos_mub with (x''::y''::nil); auto.

    clear -Hinh HM.
      revert Hinh.
      unfold inh. simpl.
      pattern hf at 1 2. case hf; auto.
      intros [x ?].
      rewrite HM in H.
      destruct H as [x' [??]].
      apply in_map_iff in H.
      destruct H as [q [??]].
      exists q. exists q. split; auto.

    apply elem_inh with x''. apply cons_elem; auto.
    hnf; simpl; intros.
    apply cons_elem in H10. destruct H10.
    rewrite H10; auto.
    exists x''; split; auto.
    apply cons_elem in H10. destruct H10.
    rewrite H10; auto.
    exists y''; split; auto.
    apply nil_elem in H10. elim H10.
    destruct H10 as [c'' [??]].
    exists (LimSet k c'').
    split.
    rewrite H3.
    exists k'. simpl. exists Hkk'. exists Hkk'.
    apply embed_mono; auto.
    rewrite <- H11.
    destruct H8.
    apply H8. apply cons_elem; auto.
    split.
    rewrite H4.
    exists k'. simpl. exists Hkk'. exists Hkk'.
    apply embed_mono; auto.
    rewrite <- H11.
    destruct H8.
    apply H8.
    apply cons_elem. right.
    apply cons_elem. auto.
    apply finsubset_elem.
    intros. rewrite <- H12; auto.
    split; auto.
    exists (LimSet k c'').
    split; auto.
    apply in_map. auto.
    exists m. simpl.
    exists Hkm. exists Hzm.
    transitivity (ds_hom DS k m Hkm c); auto.
    apply embed_mono.
    rewrite <- H11; auto.
    intros. rewrite <- H1. auto.
    intros. rewrite <- H1. auto.
  Qed.

  Definition limord_plotkin : plotkin_order hf limord :=
    norm_plt limord limord_effective hf limord_has_normals.

  Definition bilimit : PLT.ob hf :=
    PLT.Ob hf limset (PLT.Class _ _ limord_mixin limord_effective limord_plotkin).
  
  Program Definition limset_spoke (i:I) : hom (EMBED hf) (ds_F DS i) bilimit
    := Embedding hf (ds_F DS i : ob (EMBED hf)) bilimit
    (fun x => LimSet i x) _ _ _ _.
  Next Obligation.
    intros. hnf. simpl. exists i. exists (ord_refl _ _). exists (ord_refl _ _).
    rewrite (ds_ident DS i (ord_refl I i)). simpl. auto.
  Qed.
  Next Obligation.
    intros. 
    destruct H as [k [Hki [Hki' ?]]]. simpl in *.
    rewrite <- (ds_compose DS i k k Hki' (ord_refl I k) Hki) in H.
    rewrite (ds_ident DS k (ord_refl I k)) in H.
    simpl in H.
    apply embed_reflects in H. auto.
  Qed.
  Next Obligation.
    intros.
    destruct (choose_ub I i (idx y)) as [k [??]].
    generalize (refl_equal hf). pattern hf at 2. case hf.
    intros. pattern hf at 1. rewrite H1. auto.
    intros. pattern hf at 1. rewrite H1.
    generalize (embed_directed0 (ds_hom DS i k H) 
      (ds_hom DS (idx y) k H0 (elem y))).
    pattern hf at 1. rewrite H1.
    intros [q ?].
    exists q.
    hnf; simpl.
    exists k. exists H. exists H0.
    auto.
  Qed.
  Next Obligation.
    simpl; intros.
    destruct H as [k1 [Hik1 [Hyk1 ?]]]. simpl in *.
    destruct H0 as [k2 [Hik2 [Hyk2 ?]]]. simpl in *.
    destruct (choose_ub I k1 k2) as [k [??]].
    assert (i ≤ k). transitivity k1; auto.
    assert (idx y ≤ k). transitivity k1; auto.
    destruct (embed_directed2 (ds_hom DS i k H3)
      (ds_hom DS (idx y) k H4 (elem y)) a b) as [q [?[??]]].
    rewrite <- (ds_compose DS i k1 k Hik1 H1 H3).
    rewrite <- (ds_compose DS (idx y) k1 k Hyk1 H1 H4).
    simpl. apply embed_mono. auto.
    rewrite <- (ds_compose DS i k2 k Hik2 H2 H3).
    rewrite <- (ds_compose DS (idx y) k2 k Hyk2 H2 H4).
    simpl. apply embed_mono. auto.
    exists q. split; auto.
    exists k. simpl.
    exists H3. exists H4. auto.
  Qed.

  Lemma limset_spoke_commute : forall i j (Hij:i≤j),
     limset_spoke i ≈ limset_spoke j ∘ ds_hom DS i j Hij.
  Proof.
    intros; split; hnf; simpl; intros.
    exists j. simpl. exists Hij. exists (ord_refl _ _).
    rewrite (ds_ident DS j (ord_refl _ _)). simpl; auto.
    exists j. simpl. exists (ord_refl _ _). exists Hij.
    rewrite (ds_ident DS j (ord_refl _ _)). simpl; auto.
  Qed.

  Definition bilimit_cocone : cocone DS :=
    Cocone DS bilimit limset_spoke limset_spoke_commute.

  Section bilimit_univ.
    Variable YC:cocone DS.

    Program Definition limord_univ : bilimit ⇀ YC :=
      Embedding hf bilimit (YC : ob (EMBED hf))
        (fun x => let (i,x') := x in cocone_spoke YC i x')
        _ _ _ _.
    Next Obligation.
      simpl; intros.
      destruct a as [i a].
      destruct a' as [i' a'].
      hnf in H. simpl in H.
      destruct H as [k [Hk1 [Hk2 ?]]].
      generalize (cocone_commute YC i k Hk1); intros.
      rewrite H0; clear H0.
      generalize (cocone_commute YC i' k Hk2); intros.
      rewrite H0. simpl.
      apply embed_mono. auto.
    Qed.
    Next Obligation.
      simpl; intros.
      destruct a as [i a].
      destruct a' as [i' a'].
      destruct (choose_ub I i i') as [k [Hk1 Hk2]].
      exists k. simpl. exists Hk1. exists Hk2.
      apply (embed_reflects (cocone_spoke YC k)).
      apply (use_ord H).
      destruct (cocone_commute YC i k Hk1); intros.
      apply H1; auto.
      destruct (cocone_commute YC i' k Hk2); intros.
      apply H0; auto.
    Qed.
    Next Obligation.      
      intro.
      generalize (refl_equal hf).
      pattern hf at 2.  case hf; intros.
      pattern hf at 1. rewrite H. auto.
      pattern hf at 1. rewrite H.
      destruct (choose_ub_set I nil) as [i _].
      generalize (embed_directed0 (cocone_spoke YC i) y).
      pattern hf at 1. rewrite H.
      intros [x ?].
      exists (LimSet i x). auto.
    Qed.
    Next Obligation.
      intros.
      destruct a as [i a].
      destruct b as [j b].
      destruct (choose_ub I i j) as [k [Hk1 Hk2]].
      rewrite (cocone_commute YC i k Hk1) in H.
      rewrite (cocone_commute YC j k Hk2) in H0.
      destruct (embed_directed2 (cocone_spoke YC k) y
        (ds_hom DS i k Hk1 a)
        (ds_hom DS j k Hk2 b)) as [c [?[??]]]; auto.
      exists (LimSet k c).
      split; auto.
      split.
      exists k. simpl.
      exists Hk1. exists (ord_refl _ _).
      rewrite (ds_ident DS k (ord_refl _ _)).
      simpl. auto.
      exists k. simpl.
      exists Hk2. exists (ord_refl _ _).
      rewrite (ds_ident DS k (ord_refl _ _)).
      simpl. auto.
    Qed.

    Lemma limord_univ_commute i :
      cocone_spoke YC i ≈ limord_univ ∘ limset_spoke i.
    Proof.
      cut (forall x,
        cocone_spoke YC i x ≈ limord_univ (limset_spoke i x)).
      intros. split; intro x; destruct (H x); auto.
      simpl; intros; auto.
    Qed.

    Lemma limord_univ_uniq (f:bilimit ⇀ YC) :
      (forall i, cocone_spoke YC i ≈ f ∘ limset_spoke i) ->
      f ≈ limord_univ.
    Proof.
      intros.
      cut (forall x, f x ≈ limord_univ x).
      intros. split; intro x; destruct (H0 x); auto.
      simpl. intros.
      destruct x as [i x].
      rewrite H. simpl. auto.
    Qed.
  End bilimit_univ.

  Definition bilimit_construction : directed_colimit DS bilimit_cocone :=
    DirectedColimit DS bilimit_cocone
      limord_univ
      limord_univ_commute
      limord_univ_uniq.

  Program Definition ep_set : dir_preord I → (PLT.hom_ord hf bilimit bilimit) :=
    Preord.Hom _ _ 
        (fun i => embed (embed_ep_pair (limset_spoke i)) ∘
                  project (embed_ep_pair (limset_spoke i))) 
        _.
  Next Obligation.
    hnf; simpl; intros.
    hnf; simpl; intros.
    destruct a0 as [x y].
    apply approx_rels.compose_elem in H0 as [z [??]].
    apply approx_rels.compose_elem.
    apply (PLT.hom_order _ _ _ 
      (project_hom hf (ds_F DS b) bilimit (limset_spoke b))).
    2: apply (PLT.hom_order _ _ _ 
      (project_hom hf (ds_F DS a) bilimit (limset_spoke a))).
    exists (ds_hom DS a b H z).
    split; simpl.
    apply project_rel_elem.
    apply project_rel_elem in H0.
    rewrite <- H0.
    generalize (limset_spoke_commute a b H).
    intro. 
    destruct H2. apply H3.
    apply embed_rel_elem.
    apply embed_rel_elem in H1.
    rewrite H1.
    generalize (limset_spoke_commute a b H).
    intros [??]. apply H2.
  Qed.

  Program Definition Iset : Preord.carrier (cl_eset (directed_hf_cl hf) I)
    := exist _ (eff_enum I (dir_effective I)) _.
  Next Obligation.
    hnf. simpl; intros.
    destruct (choose_ub_set I M). exists x. split; auto.
    apply eff_complete.
  Qed.

  Lemma bilimit_cpo_colimit : forall x y:bilimit,
    y ≤ x ->
    exists i a, 
      y ≤ limset_spoke i a /\
      limset_spoke i a ≤ x.
  Proof.
    intros. destruct H as [k [Hk1 [Hk2 ?]]].
    exists k. exists (ds_hom DS (idx x) k Hk2 (elem x)).
    split.
    exists k. simpl. exists Hk1. exists (ord_refl _ _). 
    rewrite (ds_ident DS k (ord_refl _ _)); simpl; auto.
    exists k. simpl. exists (ord_refl _ _). exists Hk2.
    rewrite (ds_ident DS k (ord_refl _ _)); simpl; auto.
  Qed.

  Lemma bilimit_cpo_colimit1 :
    id(bilimit) ≤ ∐(image ep_set Iset).
  Proof.
    hnf. intros [x y] ?.
    simpl in H.
    apply approx_rels.ident_elem in H.
    simpl.
    apply union_axiom.
    destruct (bilimit_cpo_colimit x y) as [i [a [??]]]; auto.
    exists (PLT.hom_rel (ep_set#i)).
    split.
    apply image_axiom1'.
    exists (ep_set#i).
    split; auto.
    apply image_axiom1'.
    exists i. split; auto.
    apply eff_complete.
    simpl.
    apply approx_rels.compose_elem.
    apply (PLT.hom_order _ _ _ 
      (project_hom hf (ds_F DS i) bilimit (limset_spoke i))).
    exists a. split.
    apply project_rel_elem. auto.
    apply embed_rel_elem. auto.
  Qed.

  Lemma bilimit_cpo_colimit2 :
    id(bilimit) ≈ ∐(image ep_set Iset).
  Proof.
    split. apply bilimit_cpo_colimit1.
    apply CPO.sup_is_least.
    hnf. simpl; intros.
    apply image_axiom2 in H. destruct H as [i [??]].
    rewrite H0.
    unfold ep_set. simpl.
    apply (ep_ident hf _ _ _ _ 
      (embed_func_is_ep_pair hf _ _ (limset_spoke i))).
  Qed.

End bilimit.

(* FIXME Move to bilimit ? *)
Section colimit_decompose.
  Variable hf:bool.
  Variable I:directed_preord.
  Variable DS : directed_system I (EMBED hf).
  Variable CC : cocone DS.
  Variable Hcolimit : directed_colimit DS CC.

  Lemma colimit_decompose : forall x:cocone_point CC,
    { i:I & { a:ds_F DS i | cocone_spoke CC i a ≈ x }}.
  Proof.
    intros.
    set (y := colim_univ Hcolimit (bilimit_cocone hf I DS) x).
    exists (idx _ _ _ y).    
    exists (elem _ _ _ y).
    split.
    apply (embed_reflects 
      (colim_univ Hcolimit (bilimit_cocone hf I DS))).
    generalize (colim_commute Hcolimit (bilimit_cocone hf I DS) (idx _ _ _ y)).
    simpl. intros.
    transitivity (limset_spoke hf I DS (idx _ _ _ y) (elem hf I DS y)).
    rewrite H. auto.
    transitivity y; auto.
    destruct y; simpl; auto.
    apply (embed_reflects 
      (colim_univ Hcolimit (bilimit_cocone hf I DS))).
    generalize (colim_commute Hcolimit (bilimit_cocone hf I DS) (idx _ _ _ y)).
    simpl. intros.
    transitivity (limset_spoke hf I DS (idx _ _ _ y) (elem hf I DS y)).
    transitivity y; auto.
    destruct y; simpl; auto.
    rewrite H; auto.
  Qed.
End colimit_decompose.

Section colimit_decompose2.
  Variable hf:bool.
  Variable I:directed_preord.
  Variable DS : directed_system I (EMBED hf).
  Variable CC : cocone DS.
  Hypothesis decompose : forall x:cocone_point CC,
    { i:I & { a:ds_F DS i | cocone_spoke CC i a ≈ x }}.

  Definition decompose_univ_func (YC:cocone DS) (x:cocone_point CC) :=
    cocone_spoke YC 
       (projT1 (decompose x))
       (projT1 (projT2 (decompose x))).

  Program Definition decompose_univ (YC:cocone DS) : CC ⇀ YC :=
    Embedding hf (cocone_point CC: ob (EMBED hf)) 
                 (cocone_point YC : ob (EMBED hf))
                 (decompose_univ_func YC) _ _ _ _.
  Next Obligation.
    unfold decompose_univ_func. intros.
    destruct (decompose a) as [i [q ?]]. simpl.
    destruct (decompose a') as [j [q' ?]]. simpl.
    destruct (choose_ub I i j) as [k [??]].
    rewrite (cocone_commute YC i k H0).
    rewrite (cocone_commute YC j k H1).
    simpl.
    apply embed_mono.
    apply (embed_reflects (cocone_spoke CC k)).
    apply (use_ord H).
    rewrite <- e.
    rewrite (cocone_commute CC i k H0). auto.
    rewrite <- e0.
    rewrite (cocone_commute CC j k H1). auto.
  Qed.
  Next Obligation.
    unfold decompose_univ_func. intros.
    destruct (decompose a) as [i [q ?]]. simpl in *.
    destruct (decompose a') as [j [q' ?]]. simpl in *.
    destruct (choose_ub I i j) as [k [??]].
    rewrite (cocone_commute YC i k H0) in H.
    rewrite (cocone_commute YC j k H1) in H.
    simpl in H.
    apply embed_reflects in H.
    rewrite <- e.
    rewrite <- e0.
    rewrite (cocone_commute CC i k H0).
    rewrite (cocone_commute CC j k H1).
    simpl. apply embed_mono; auto.
  Qed.
  Next Obligation.
    intros.
    unfold decompose_univ_func.
    destruct hf; simpl; auto.
    destruct (choose_ub_set I nil) as [i ?].
    destruct (embed_directed0 (cocone_spoke YC i) y).
    exists (cocone_spoke CC i x).
    destruct (decompose (cocone_spoke CC i x)) as [m [z' ?]]. simpl.
    rewrite <- H.    
    destruct (choose_ub I m i) as [k [??]].
    rewrite (cocone_commute YC m k H0).
    rewrite (cocone_commute YC i k H1).
    simpl. apply embed_mono.
    rewrite (cocone_commute CC m k H0) in e.
    rewrite (cocone_commute CC i k H1) in e.
    simpl in e. 
    destruct e.
    apply (embed_reflects (cocone_spoke CC k)) in H2. auto.
  Qed.
  Next Obligation.
    unfold decompose_univ_func. intros.
    destruct (decompose a) as [i [q ?]]. simpl in *.
    destruct (decompose b) as [j [q' ?]]. simpl in *.
    destruct (choose_ub I i j) as [k [??]].
    rewrite (cocone_commute YC i k H1) in H.
    rewrite (cocone_commute YC j k H2) in H0.
    simpl in H, H0.
    destruct (embed_directed2 (cocone_spoke YC k) y
      (ds_hom DS i k H1 q)
      (ds_hom DS j k H2 q')) as [z [?[??]]]; auto.
    exists (cocone_spoke CC k z).
    split.
    destruct (decompose (cocone_spoke CC k z)) as [m [z' ?]]. simpl.
    rewrite <- H3.

    destruct (choose_ub I m k) as [k' [??]].
    rewrite (cocone_commute YC m k' H6).
    rewrite (cocone_commute YC k k' H7).
    simpl. apply embed_mono.
    destruct e1.
    rewrite (cocone_commute CC m k' H6) in H8.
    rewrite (cocone_commute CC k k' H7) in H8.
    simpl in H8.
    apply (embed_reflects (cocone_spoke CC k')) in H8. auto.

    split.
    rewrite <- e.
    rewrite (cocone_commute CC i k H1).
    simpl. apply embed_mono. auto.
    rewrite <- e0.
    rewrite (cocone_commute CC j k H2).
    simpl. apply embed_mono. auto.
  Qed.

  Program Definition decompose_is_colimit : directed_colimit DS CC :=
    DirectedColimit DS CC decompose_univ _ _.
  Next Obligation.
    intros. apply embed_lift'. simpl.
    unfold decompose_univ_func. simpl. intro x.
    destruct (decompose (cocone_spoke CC i x)) as [j [x' ?]]. simpl.
    destruct (choose_ub I i j) as [k [??]].
    rewrite (cocone_commute YC i k H).
    rewrite (cocone_commute YC j k H0).
    rewrite (cocone_commute CC i k H) in e.
    rewrite (cocone_commute CC j k H0) in e.
    simpl in e. 
    destruct e; split; simpl.
    apply embed_reflects in H2. apply embed_mono; auto.
    apply embed_reflects in H1. apply embed_mono; auto.
  Qed.    
  Next Obligation.
    simpl; intros.
    intros. apply embed_lift'. simpl.
    unfold decompose_univ_func. simpl. intro x.
    destruct (decompose x) as [i [x' ?]]. simpl.
    rewrite <- e.
    rewrite (H i).
    simpl; auto.
  Qed.
End colimit_decompose2.



Require Import Arith.
Require Import NArith.

Program Definition nat_ord := Preord.Pack nat (Preord.Mixin nat le _ _).
Solve Obligations using eauto with arith.
  
Program Definition nat_eff : effective_order nat_ord :=
  EffectiveOrder nat_ord le_dec (fun x => Some (N.to_nat x)) _.
Next Obligation.
  intros. exists (N.of_nat x).
  rewrite Nat2N.id. auto.
Qed.

Program Definition nat_dirord : directed_preord :=
  DirPreord nat_ord nat_eff _.
Next Obligation.  
  induction M.
  exists 0. hnf; intros. apply nil_elem in H. elim H.
  destruct IHM as [k ?].
  exists (max a k).
  hnf; intros.
  apply cons_elem in H. destruct H.
  rewrite H.
  red; simpl.
  apply Max.le_max_l.
  transitivity k.
  apply u. auto.
  red; simpl.
  apply Max.le_max_r.
Qed.

Section fixpoint.
  Variable F:functor (EMBED true) (EMBED true).

  Fixpoint iterF (x:nat) : ob (EMBED true) :=
    match x with
    | O => empty_plt true
    | S x' => F (iterF x')
    end.

  Lemma HSle0 j (Hij: S j <= O) : False.
  Proof.
    inversion Hij.
  Qed.

  Fixpoint iter_hom (i:nat) : forall (j:nat) (Hij:i <= j), iterF i ⇀ iterF j :=
    match i as i' return forall (j:nat) (Hij:i' <= j), iterF i' ⇀ iterF j with
    | O => fun j Hij => empty_bang _
    | S i' => fun j =>
        match j as j' return forall (Hij:S i' <= j'), iterF (S i') ⇀ iterF j' with
        | O => fun Hij => False_rect _ (HSle0 i' Hij)
        | S j' => fun Hij => F@(iter_hom i' j' (gt_S_le i' j' Hij))
        end
    end.

  Lemma iter_hom_proof_irr i : forall j H1 H2,
    iter_hom i j H1 ≈ iter_hom i j H2.
  Proof.
    induction i; simpl; intros; auto.
    destruct j.
    elimtype False. inversion H1.
    apply Functor.respects.
    apply IHi.
  Qed.

  Program Definition kleene_chain : directed_system nat_dirord (EMBED true) :=
    DirSys nat_dirord (EMBED true) iterF iter_hom _ _.
  Next Obligation.      
    induction i; simpl; intros.
    apply embed_lift'. intro x; elim x.
    apply Functor.ident; auto.
  Qed.
  Next Obligation.
    induction i. simpl; intros.
    apply embed_lift'. intro x; elim x.
    intros. destruct j.
    elimtype False. inversion Hij.
    destruct k.
    elimtype False. inversion Hjk.
    simpl.
    rewrite <- (Functor.compose F _ _ _ (iter_hom j k (gt_S_le j k Hjk))).
    reflexivity. auto.
  Qed.

  Definition fixpoint := bilimit true nat_dirord kleene_chain.

  Hypothesis Fcontinuous : continuous_functor F.
  
  Let BL := Fcontinuous nat_dirord kleene_chain
      (bilimit_cocone true nat_dirord kleene_chain)
      (bilimit_construction true nat_dirord kleene_chain).

  Program Definition cocone_plus1 : 
    cocone (dir_sys_app kleene_chain F)
    := Cocone _
      fixpoint
      (fun i => limset_spoke _ _ kleene_chain (S i)) _.
  Next Obligation.
    simpl; intros.
    apply embed_lift'.
    simpl; intros.
    split; hnf; simpl.
    exists (S j).
    exists (le_n_S _ _ Hij). exists (ord_refl _ _).
    change ((F @ iter_hom i j (gt_S_le i j (le_n_S i j Hij))) x
      ≤ ((F @ iter_hom j j (gt_S_le j j (ord_refl nat_ord (S j)))) ∘
        (F @ iter_hom i j Hij)) x).
    apply embed_unlift.
    rewrite <- (Functor.compose F). 2: reflexivity.
    rewrite (kleene_chain_obligation_2 i j j
      Hij
      (gt_S_le j j (ord_refl nat_ord (S j)))
      (gt_S_le i j (le_n_S i j Hij))); auto.
    exists (S j).
    exists (ord_refl _ _).  exists (le_n_S _ _ Hij). 
    change (
      ((F @ iter_hom j j (gt_S_le j j (ord_refl nat_ord (S j)))) ∘
        (F @ iter_hom i j Hij)) x
      ≤
      (F @ iter_hom i j (gt_S_le i j (le_n_S i j Hij))) x).
    apply embed_unlift.
    rewrite <- (Functor.compose F). 2: reflexivity.
    rewrite (kleene_chain_obligation_2 i j j
      Hij
      (gt_S_le j j (ord_refl nat_ord (S j)))
      (gt_S_le i j (le_n_S i j Hij))); auto.
  Qed.

  Definition fixpoint_alg : alg (EMBED true) F
    := @Alg _ F fixpoint (colim_univ BL cocone_plus1).

  Section cata.
    Variable AG : alg (EMBED true) F.
  
    Fixpoint cata_hom' (i:nat) : iterF i ⇀ AG :=
      match i as i' return iterF i' ⇀ AG with
      | O => empty_bang AG
      | S i' => Alg.iota AG ∘ F@(cata_hom' i')
      end.

    Lemma cata_hom_iter_hom : forall (i j:nat_ord) (Hij:i≤j),
      cata_hom' i ≈ cata_hom' j ∘ (iter_hom i j Hij).
    Proof.
      induction i; intros.
      apply embed_lift'. intro x; elim x.
      destruct j. inversion Hij.
      simpl.
      rewrite <- (cat_assoc (Alg.iota AG)).
      apply cat_respects; auto.
      rewrite <- (Functor.compose F).
      2: reflexivity.
      rewrite IHi; eauto.
    Qed.      

    Program Definition cata_hom : fixpoint ⇀ AG :=
      Embedding _ _ _ 
      (fun x => let (i,x') := x in cata_hom' i x')
      _ _ _ _.
    Next Obligation.
      intros. 
      destruct a as [i a].
      destruct a' as [i' a'].
      destruct H as [k [Hk1 [Hk2 ?]]]. simpl in *.
      transitivity (cata_hom' k (iter_hom i k Hk1 a)).
      destruct (cata_hom_iter_hom i k Hk1).
      apply H0.
      transitivity (cata_hom' k (iter_hom i' k Hk2 a')).
      apply embed_mono. auto.
      destruct (cata_hom_iter_hom i' k Hk2).
      apply H1.
    Qed.      
    Next Obligation.
      intros.
      destruct a as [i a].
      destruct a' as [i' a'].
      hnf. simpl.
      exists (max i i').
      exists (Max.le_max_l i i').
      exists (Max.le_max_r i i').
      apply (embed_reflects (cata_hom' (max i i'))).
      apply (use_ord H).
      
      rewrite (cata_hom_iter_hom i (max i i') (Max.le_max_l i i')). auto.
      rewrite (cata_hom_iter_hom i' (max i i') (Max.le_max_r i i')). auto.
    Qed.
    Next Obligation.
      auto.
    Qed.
    Next Obligation.
      intros. 
      destruct a as [i a].
      destruct b as [i' b].
      simpl in *.
      rewrite (cata_hom_iter_hom i (max i i') (Max.le_max_l i i')) in H.
      rewrite (cata_hom_iter_hom i' (max i i') (Max.le_max_r i i')) in H0.
      destruct (embed_directed2 (cata_hom' (max i i')) y) with
        (iter_hom i (max i i') (Max.le_max_l i i') a)
        (iter_hom i' (max i i') (Max.le_max_r i i') b)
        as [c [?[??]]]; auto.
      exists (LimSet _ _ kleene_chain (max i i') c).
      split; auto.
      split; exists (max i i'); simpl.
      exists (Max.le_max_l i i').
      exists (ord_refl _ _).
      generalize (kleene_chain_obligation_1 (max i i') (ord_refl _ _)).
      intros. rewrite H4. simpl.
      auto.
      exists (Max.le_max_r i i').
      exists (ord_refl _ _).
      generalize (kleene_chain_obligation_1 (max i i') (ord_refl _ _)).
      intros. rewrite H4. simpl.
      auto.
    Qed.      

    Program Definition AG_cocone :
      cocone (dir_sys_app kleene_chain F) :=
        Cocone _ _ (fun i => cata_hom' (S i)) _.
    Next Obligation.
      simpl; intros.
      rewrite (cata_hom_iter_hom i j Hij).
      rewrite Functor.compose.
      2: reflexivity.
      apply cat_assoc.
    Qed.

    Program Definition cata_alg_hom : Alg.alg_hom fixpoint_alg AG :=
      Alg.Alg_hom cata_hom _.
    Next Obligation.
      simpl.
      generalize (colim_uniq BL AG_cocone).
      intros.
      rewrite (H (cata_hom ∘ colim_univ BL cocone_plus1)).
      symmetry. apply H.

      intros. simpl.
      rewrite <- (cat_assoc (Alg.iota AG)).
      rewrite <- (Functor.compose F). 2: reflexivity.
      apply cat_respects; auto.
      apply Functor.respects.
      split; hnf; simpl; auto.

      intros.
      rewrite <- (cat_assoc cata_hom).
      rewrite <- (colim_commute BL cocone_plus1).
      split; hnf; simpl; auto.
    Qed.
  End cata.

  Program Definition fixpoint_initial : Alg.initial_alg (EMBED true) F :=
    Alg.Initial_alg fixpoint_alg cata_alg_hom _.
  Next Obligation.
    simpl; intros.
    apply embed_lift'.
    simpl; intro x.
    destruct x as [i x].
    cut (Alg.hom_map h ∘ limset_spoke _ _ kleene_chain i ≈ cata_hom' M i).
    intros.
    destruct H; split; auto.
    apply (H x). apply (H0 x).
    clear x. induction i.
    split; hnf; intro x; elim x.
    simpl.
    rewrite <- IHi.
    destruct h as [h Hh]. simpl in *.
    rewrite Functor.compose. 2: reflexivity.
    rewrite (cat_assoc (Alg.iota M)).
    rewrite <- Hh.
    generalize (Alg.hom_axiom (cata_alg_hom M)).
    simpl.
    intros.
    cut (limset_spoke true nat_dirord kleene_chain (S i)
      ≈ colim_univ BL cocone_plus1 ∘ F @ limset_spoke true nat_dirord kleene_chain i).
    intros.
    split; hnf; intros; simpl; apply (embed_mono h).
    destruct H0. apply (H0 x).
    destruct H0. apply (H1 x).
    apply (colim_commute BL cocone_plus1).
  Qed.

  Program Definition fixpoint_iso :
    F fixpoint ↔ fixpoint :=

    Isomorphism (EMBED true) (F fixpoint) fixpoint 
      (colim_univ BL cocone_plus1)
      (Alg.out _ F fixpoint_initial)
      (Alg.out_in _ F fixpoint_initial)
      (Alg.in_out _ F fixpoint_initial).

End fixpoint.
