(* Copyright (c) 2014, Robert Dockins *)

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
Require Import embed.
Require Import directed.
Require Import cont_functors.
Require Import cpo.


(**  * Bilimits and fixpoints of continuous functors.

       Here we construct the colimit of directed systems.
       The carrier of the bilimit is the disjoint union
       of the directed system.  The order on the bilimit
       elements holds if there exists some larger poset
       into which both elements can be embedded where
       the ordering holds.
  *)
Section bilimit.
  Variable hf:bool.
  Variable I:directed_preord.
  Variable DS:directed_system I (EMBED hf).


  Record limset :=
    LimSet
    { idx : I
    ; elem : ds_F DS idx
    }.

  Definition limset_order (x y:limset) :=
    exists k (Hxk : idx x ≤ k) (Hyk : idx y ≤ k),
      ds_hom DS (idx x) k Hxk (elem x) 
      ≤ ds_hom DS (idx y) k Hyk (elem y).


  (**  This lemma shows that if two elements compare in any larger poset,
       the compare in _every_ larger poset.
    *)
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

  (**  The order is decidable.
    *)
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

  (**  Furthermore, all the elements can be enumerated.
    *)
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

  (** Thus, the bilimit is an effective order. *)
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

  (**  Moreover, the bilimit has normal sets.
    *)
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
    intros. rewrite <- H2. auto.
    intros. rewrite <- H2. auto.
  Qed.

  (**  Altogether, this makes the bilimit a plotkin order.
    *)
  Definition limord_plotkin : plotkin_order hf limord :=
    norm_plt limord limord_effective hf limord_has_normals.

  Definition bilimit : PLT.ob hf :=
    PLT.Ob hf limset (PLT.Class _ _ limord_mixin limord_effective limord_plotkin).
  

  (**  Here we define the spokes of the colimit cocone.
    *)
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
    apply PLT.compose_hom_rel in H0 as [z [??]].
    apply PLT.compose_hom_rel.
    exists (ds_hom DS a b H z).
    split; simpl.
    simpl in *.
    apply project_rel_elem.
    apply project_rel_elem in H0.
    rewrite <- H0.
    generalize (limset_spoke_commute a b H).
    intro. 
    destruct H2. apply H3.
    apply embed_rel_elem.
    simpl in H1.
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
    apply PLT.compose_hom_rel.
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


(**  The following two constructions show that a cocone is a colimit
     in EMBED iff every element can be factored through a spoke of the cocone.

     Passing thorough these constructions is generally the easiest way to
     demonstrate that an embedding functor is continuous.
  *)
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
       (proj1_sig (projT2 (decompose x))).

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
    intros. apply embed_lift'.
    intro x.
    simpl. unfold decompose_univ_func.
    destruct (decompose x) as [i [x' ?]]. simpl.
    (* FIXME, why can I not just rewrite using <- e here? *)
    transitivity (f (cocone_spoke CC i x')).
    apply embed_map_eq_morphism; auto.
    rewrite (H i).
    simpl; auto.
  Qed.
End colimit_decompose2.

(** With the bilimit in hand, we can construct the least
    fixpoint of continuous functors in the embeddings
    over the category of partial plotkin orders by appeal
    to the general fixpoint construction for continuous functors.
 *)
Section fixpoint.
  Variable F:functor (EMBED true) (EMBED true).
  Hypothesis Fcontinuous : continuous_functor F.

  Definition fixpoint : ob (EMBED true) :=
    cont_functors.fixpoint
           PPLT_EMBED_initialized
           F 
           (bilimit_cocone true).

  Definition fixpoint_initial : Alg.initial_alg (EMBED true) F :=
    cont_functors.fixpoint_initial
           PPLT_EMBED_initialized
           F 
           (bilimit_cocone true)
           (bilimit_construction true)
           Fcontinuous.

  Definition fixpoint_iso : F fixpoint ↔ fixpoint :=
    cont_functors.fixpoint_iso
           PPLT_EMBED_initialized
           F 
           (bilimit_cocone true)
           (bilimit_construction true)
           Fcontinuous.
End fixpoint.


Require Import Arith.

(** We can also build fixpoints in the category of total
    Plotkin orders by requiring a little more data.
    This proof is a modification of Theorem 79 from
    Carl Gunter's PhD thesis (CMU, 1985).
 *)
Section total_fixpoint.
  Variable F:functor (EMBED false) (EMBED false).
  Hypothesis Fcontinuous : continuous_functor F.

  Variable A:ob PLT.
  Variable h:A ⇀ F A.

  Fixpoint iterF (x:nat) : ob PLT :=
    match x with
    | O => A
    | S x' => F (iterF x')
    end.

  Fixpoint injectA (j:nat) : A ⇀ iterF j :=
    match j as j' return A ⇀ iterF j' with
    | 0 => id
    | S n => F·(injectA n) ∘ h
    end.

  Fixpoint iter_hom (i:nat) : forall (j:nat) (Hij:i <= j), iterF i ⇀ iterF j :=
    match i as i' return forall (j:nat) (Hij:i' <= j), iterF i' ⇀ iterF j with
    | O => fun j Hij => injectA j
    | S i' => fun j =>
        match j as j' return forall (Hij:S i' <= j'), iterF (S i') ⇀ iterF j' with
        | O => fun Hij => False_rect _ (HSle0 i' Hij) (* impossible case *)
        | S j' => fun Hij => F·(iter_hom i' j' (gt_S_le i' j' Hij))
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

  Program Definition kleene_chain_alt : directed_system nat_dirord (EMBED false) :=
    DirSys nat_dirord _ iterF iter_hom _ _.
  Next Obligation.      
    induction i; simpl; intros.
    auto.
    apply Functor.ident; auto.
  Qed.
  Next Obligation.
    induction i. simpl; intros.
    clear Hij Hik.
    revert k Hjk; induction j; simpl; intros.
    apply cat_ident1.
    destruct k.
    elimtype False. inversion Hjk.
    simpl.
    rewrite (@cat_assoc (EMBED false)).
    apply cat_respects; auto.
    symmetry. apply Functor.compose.
    symmetry. apply IHj.
    
    intros. destruct j.
    elimtype False. inversion Hij.
    destruct k.
    elimtype False. inversion Hjk.
    simpl.
    rewrite <- (Functor.compose F _ _ _ (iter_hom j k (gt_S_le j k Hjk))).
    reflexivity. auto.
  Qed.

  Definition fixpoint_alt : ob PLT := bilimit false nat_dirord kleene_chain_alt.
  
  Let BL := Fcontinuous
               nat_dirord kleene_chain_alt
               (bilimit_cocone false nat_dirord kleene_chain_alt)
               (bilimit_construction false nat_dirord kleene_chain_alt).

  Program Definition cocone_plus1 : cocone (dir_sys_app kleene_chain_alt F)
    := Cocone (dir_sys_app kleene_chain_alt F) fixpoint_alt
      (fun i => cocone_spoke (bilimit_cocone false nat_dirord kleene_chain_alt) (S i)) _.
  Next Obligation.
    simpl; intros.
    assert (Hij' : S i <= S j). auto with arith.
    rewrite (cocone_commute (bilimit_cocone false nat_dirord kleene_chain_alt) (S i) (S j) Hij').
    simpl. apply cat_respects; auto.
    apply Functor.respects.
    apply iter_hom_proof_irr.
  Qed.

  Program Definition cocone_minus1 : cocone kleene_chain_alt
    := Cocone kleene_chain_alt (F fixpoint_alt) 
           (fun i => 
              F·(cocone_spoke (bilimit_cocone false nat_dirord kleene_chain_alt) i) ∘
              iter_hom i (S i) (le_S i i (le_refl i)))
           _.
  Next Obligation.
    simpl. intros.
    assert (i <= S j). auto with arith.
    rewrite <- (@cat_assoc (EMBED false)).
    rewrite (kleene_chain_alt_obligation_2 i j (S j) Hij (le_S j j (le_refl j)) H).
    destruct i. simpl.

    rewrite Functor.ident; auto.
    rewrite (@cat_ident2 (EMBED false)).
    rewrite (@cat_assoc (EMBED false)).
    apply cat_respects; auto.
    apply Functor.compose.
    rewrite (limset_spoke_commute false nat_dirord kleene_chain_alt 0%nat j Hij).
    simpl. auto.

    simpl.
    etransitivity.
    symmetry.
    apply (Functor.compose F) with 
      (f:=limset_spoke false nat_dirord kleene_chain_alt (S i))
      (g:=iter_hom i (S i) (gt_S_le i (S i) (le_S (S i) (S i) (le_refl (S i)))))
      (h:=limset_spoke false nat_dirord kleene_chain_alt j ∘
          iter_hom i j (gt_S_le i j H)).
    2: apply (Functor.compose F); auto.
    assert (i <= j) by auto with arith.
    rewrite <- (limset_spoke_commute false nat_dirord kleene_chain_alt i j).
    rewrite <- (limset_spoke_commute false nat_dirord kleene_chain_alt i (S i)).
    auto.
  Qed.

  Definition fixpoint_alt_in : F fixpoint_alt ⇀ fixpoint_alt :=
    colim_univ BL cocone_plus1.
  Definition fixpoint_alt_out : fixpoint_alt ⇀ F fixpoint_alt :=
    limord_univ false nat_dirord kleene_chain_alt cocone_minus1.

  Lemma fixpoint_alt_in_out : fixpoint_alt_in ∘ fixpoint_alt_out ≈ id.
  Proof.
    transitivity (limord_univ false nat_dirord kleene_chain_alt 
      (bilimit_cocone false nat_dirord kleene_chain_alt)).
    apply (limord_univ_uniq false nat_dirord kleene_chain_alt
      (bilimit_cocone false nat_dirord kleene_chain_alt)).
    simpl; intros. unfold fixpoint_alt_in. unfold fixpoint_alt_out.
    rewrite <- (@cat_assoc (EMBED false)).
    rewrite <- (limord_univ_commute false nat_dirord kleene_chain_alt cocone_minus1 i).
    simpl.
    generalize (colim_commute BL cocone_plus1 i). simpl. intros.
    transitivity (limset_spoke false nat_dirord kleene_chain_alt (S i)
      ∘ iter_hom i (S i) (le_S i i (le_refl i))).
    apply (limset_spoke_commute false nat_dirord kleene_chain_alt i (S i)).
    rewrite (@cat_assoc (EMBED false)).
    apply cat_respects; auto.
    symmetry.
    apply (limord_univ_uniq false nat_dirord kleene_chain_alt
      (bilimit_cocone false nat_dirord kleene_chain_alt)).
    simpl; intros.  
    symmetry. apply cat_ident2.
  Qed.

  Lemma fixpoint_alt_out_in : fixpoint_alt_out ∘ fixpoint_alt_in ≈ id.
  Proof.
    transitivity (colim_univ BL 
        (cocone_app (bilimit_cocone false nat_dirord kleene_chain_alt) F)).
    apply (colim_uniq BL (cocone_app (bilimit_cocone false nat_dirord kleene_chain_alt) F)).
    simpl. unfold fixpoint_alt_out. unfold fixpoint_alt_in.
    intros.
    generalize (colim_commute BL cocone_plus1 i).
    simpl. intros. 
    rewrite <- (@cat_assoc (EMBED false)).
    rewrite <- H.
    generalize (limord_univ_commute false nat_dirord kleene_chain_alt
      cocone_minus1 (S i)). simpl. intros.
    rewrite <- H0.
    apply Functor.compose.
    apply (limset_spoke_commute false nat_dirord kleene_chain_alt i (S i)).
    symmetry. 
    apply (colim_uniq BL (cocone_app (bilimit_cocone false nat_dirord kleene_chain_alt) F)).
    simpl; intros.
    symmetry. apply cat_ident2.
  Qed.

  Definition fixpoint_embed : A ⇀ fixpoint_alt :=
    limset_spoke false nat_dirord kleene_chain_alt 0%nat.
  
  Definition fixpoint_alt_iso : F fixpoint_alt ↔ fixpoint_alt :=
    Isomorphism (EMBED false) (F fixpoint_alt) fixpoint_alt
       fixpoint_alt_in
       fixpoint_alt_out
       fixpoint_alt_out_in
       fixpoint_alt_in_out.

End total_fixpoint.
