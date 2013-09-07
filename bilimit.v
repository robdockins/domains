Require Import Setoid.
Require Import NArith.
Require Import List.

Require Import basics.
Require Import categories.
Require Import preord.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import plotkin.

Record embedding (hf:bool) (A B:preord) :=
  Embedding
  { embed :> A -> B
  ; embed_mono : forall a a', a ≤ a' -> embed a ≤ embed a'
  ; embed_reflects : forall a a', embed a ≤ embed a' -> a ≤ a'
  ; embed_directed0 : forall y,
      if hf then True else exists x, embed x ≤ y
  ; embed_directed2 : forall y a b,
      embed a ≤ y ->
      embed b ≤ y ->
      exists c, embed c ≤ y /\ a ≤ c /\ b ≤ c
  }.
Arguments embed [hf] [A] [B] e a.
Arguments embed_mono [hf] [A] [B] e _ _ _.
Arguments embed_reflects [hf] [A] [B] e _ _ _.
Arguments embed_directed0 [hf] [A] [B] e _.
Arguments embed_directed2 [hf] [A] [B] e _ _ _ _ _.

Program Definition embed_ident (hf:bool) (A:preord) : embedding hf A A :=
  Embedding hf A A (fun x => x) _ _ _ _.
Solve Obligations using (intros; auto).
Next Obligation.
  intros. destruct hf; auto. exists y; auto.
Qed.
Next Obligation.
  intros. exists y. intuition.
Qed.

Program Definition embed_compose (hf:bool) (A B C:preord)
  (g:embedding hf B C) (f:embedding hf A B) : embedding hf A C :=
  Embedding hf A C (fun x => embed g (embed f x)) _ _ _ _.
Next Obligation.  
  intros. apply embed_mono. apply embed_mono. auto.
Qed.
Next Obligation.
  intros. apply (embed_reflects f). apply (embed_reflects g); auto.
Qed.
Next Obligation.
  intros. 
  generalize (refl_equal hf).
  pattern hf at 2. case hf; intros.
  pattern hf at 1. rewrite H. auto.
  pattern hf at 1. rewrite H.
  generalize (embed_directed0 g y).
  rewrite H at 1.
  intros [q ?].
  generalize (embed_directed0 f q).
  rewrite H at 1.
  intros [q' ?].
  exists q'.
  transitivity (embed g q); auto.
  apply embed_mono. auto.
Qed.
Next Obligation.
  intros.
  destruct (embed_directed2 g y (embed f a) (embed f b)) as [c [?[??]]]; auto.
  destruct (embed_directed2 f c a b) as [q [?[??]]]; auto.
  exists q. split; auto.
  transitivity (embed g c); auto.
  apply embed_mono; auto.
Qed.
  
Definition embed_order hf A B (E G:embedding hf A B) :=
  forall x, embed E x ≤ embed G x.

Program Definition embed_order_mixin hf A B : Preord.mixin_of (embedding hf A B) :=
  Preord.Mixin (embedding hf A B) (embed_order hf A B) _ _ .
Solve Obligations using (unfold embed_order; intros; eauto).

Canonical Structure embed_ord hf A B :=
  Preord.Pack (embedding hf A B) (embed_order_mixin hf A B).

Definition embed_comp_mixin hf :=
    (Comp.Mixin _ _ (embed_ident hf) (embed_compose hf)).

Canonical Structure embed_comp hf :=
  Comp.Pack preord (embedding hf) (embed_comp_mixin hf).

Program Definition embed_func {hf A B} (E:embedding hf A B) : A → B :=
  Preord.Hom A B (embed E) (embed_mono E).
Coercion embed_func : embedding >-> hom.

Program Definition embed_cat_class hf :
  Category.class_of preord (embedding hf) :=
  Category.Class _ _
    (fun A B => (Preord.ord_eq (embed_ord hf A B)))
    (embed_comp_mixin hf) _.
Next Obligation.
  intros. constructor.

  intros. split; hnf; simpl; intros; auto.
  intros. split; hnf; simpl; intros; auto.
  intros. split; hnf; simpl; intros; auto.
  intros. split; hnf; simpl; intros.
  transitivity (embed f' (embed g x)).
  destruct H. apply H.
  apply embed_mono.  
  destruct H0. apply H0.
  transitivity (embed f' (embed g x)).
  apply embed_mono.
  destruct H0. apply H1.
  destruct H. apply H1.
Qed.

Definition EMBED hf :=
  Category preord (embedding hf) (embed_cat_class hf).

Add Parametric Morphism hf A B :
  (@embed hf A B) with signature
        (@Preord.ord_op (embed_ord hf A B)) ==>
        (@Preord.ord_op A) ==>
        (@Preord.ord_op B)
    as embed_morphism.
Proof.
  intros.
  transitivity (y x0).
  apply H. apply embed_mono. auto.
Qed.

Add Parametric Morphism hf A B :
  (@embed hf A B) with signature
        (@eq_op (CAT_EQ (EMBED hf) A B)) ==>
        (@eq_op (Preord_Eq A)) ==>
        (@eq_op (Preord_Eq B))
    as embed_eq_morphism.
Proof.
  intros. split; apply embed_morphism; auto.
Qed.

Record directed_system (hf:bool) (I:preord) :=
  DirSys
  { ds_Ieff : effective_order I
  ; ds_Idir : directed hf (eff_enum I ds_Ieff)
  ; ds_F    : I -> preord
  ; ds_eff  : forall i, effective_order (ds_F i)
  ; ds_plt  : forall i, plotkin_order hf (ds_F i)
  ; ds_hom : forall i j:I, i ≤ j -> hom (EMBED hf) (ds_F i) (ds_F j)
  ; ds_ident : forall i (Hii:i≤i), ds_hom i i Hii ≈ id
  ; ds_compose : forall i j k (Hij:i≤j) (Hjk:j≤k) (Hik:i≤k),
                       ds_hom j k Hjk ∘ ds_hom i j Hij ≈ ds_hom i k Hik
  }.
Arguments ds_F [hf] [I] _ _.
Arguments ds_hom [hf] [I] _ _ _ _.

Record bilimit (hf:bool) (I:preord) :=
  Bilimit
  { bilim_DS : directed_system hf I
  ; bilim_point : preord
  ; bilim_eff   : effective_order bilim_point
  ; bilim_plt   : plotkin_order hf bilim_point
  ; bilim_spoke : forall i, hom (EMBED hf) (ds_F bilim_DS i) bilim_point
  ; bilim_commute : forall i j (Hij:i≤j),
       bilim_spoke i ≈ bilim_spoke j ∘ ds_hom bilim_DS i j Hij
  ; bilim_complete : forall y:bilim_point,
                       exists i x, bilim_spoke i x ≈ y
  }.

Section bilimit.
  Variable hf:bool.
  Variable I:preord.
  Variable DS:directed_system hf I.

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
    destruct (choose_ub k k') as [q [??]].
    assert (Hxq : idx x ≤ q).
    transitivity k; auto.
    assert (Hyq : idx y ≤ q).
    transitivity k; auto.
    assert (ds_hom DS (idx x) q Hxq (elem x) ≤
            ds_hom DS (idx y) q Hyq (elem y)).
    rewrite <- (ds_compose hf I DS (idx x) k' q Hxk' H1 Hxq).
    rewrite <- (ds_compose hf I DS (idx y) k' q Hyk' H1 Hyq).
    simpl. apply embed_mono. auto.
    rewrite <- (ds_compose hf I DS (idx x) k q Hxk H0 Hxq) in H2.
    rewrite <- (ds_compose hf I DS (idx y) k q Hyk H0 Hyq) in H2.
    simpl in H2.
    apply embed_reflects in H2. auto.

    destruct (choose_ub (idx x) (idx y)) as [k [??]].
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
    destruct (choose_ub k1 k2) as [k [??]].
    assert (Hxk : idx x ≤ k). transitivity k1; auto.
    assert (Hyk : idx y ≤ k). transitivity k1; auto.
    assert (Hzk : idx z ≤ k). transitivity k2; auto.
    exists k. exists Hxk. exists Hzk.
    transitivity (ds_hom DS (idx y) k Hyk (elem y)).
    rewrite <- (ds_compose hf I DS (idx x) k1 k Hxk1 H1 Hxk).
    rewrite <- (ds_compose hf I DS (idx y) k1 k Hyk1 H1 Hyk).
    simpl. apply embed_mono. auto.
    rewrite <- (ds_compose hf I DS (idx y) k2 k Hyk2 H2 Hyk).
    rewrite <- (ds_compose hf I DS (idx z) k2 k Hzk2 H2 Hzk).
    simpl. apply embed_mono. auto.
  Qed.

  Definition limord_mixin :=
    Preord.Mixin limset limset_order limset_order_refl limset_order_trans.

  Canonical Structure limord := Preord.Pack limset limord_mixin.

  Lemma limset_order_dec (x y:limset) :
    { limset_order x y } + { ~limset_order x y }.
  Proof.
    destruct (choose_ub (idx x) (idx y)) as [k [??]].
    destruct (eff_ord_dec _ (ds_eff hf I DS k)
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
         match eff_enum _ (ds_Ieff hf I DS) p with
         | Some i =>
              match eff_enum _ (ds_eff hf I DS i) q with
              | Some x => Some (LimSet i x)
              | None => None
              end
         | None => None
         end.

  Program Definition limord_effective : effective_order limord :=
    EffectiveOrder limord limset_order_dec limset_enum _.
  Next Obligation.
    intros [i x].
    generalize (eff_complete _ (ds_Ieff hf I DS) i).
    intros [p ?].
    case_eq (eff_enum I (ds_Ieff hf I DS) p); intros.
    2: rewrite H0 in H; elim H.
    rewrite H0 in H.
    destruct H.
    set (x' := ds_hom DS i c H x).
    assert (x' ∈ eff_enum _ (ds_eff hf I DS c)).
    apply eff_complete.
    destruct H2 as [q ?].
    case_eq (eff_enum _ (ds_eff hf I DS c) q); intros.
    2: rewrite H3 in H2; elim H2.
    rewrite H3 in H2.
    exists (pairing.pairing (p,q)).
    unfold limset_enum.
    rewrite pairing.unpairing_pairing.
    rewrite H0. rewrite H3.
    split.
    exists c. simpl. exists H. exists (ord_refl _ _).
    rewrite (ds_ident hf I DS c (ord_refl _ _)). simpl. auto.
    exists c. simpl. exists (ord_refl _ _). exists H.
    rewrite (ds_ident hf I DS c (ord_refl _ _)). simpl. auto.
  Qed.

  Lemma limord_has_normals : has_normals limord limord_effective hf.
  Proof.
    hnf. intros.
    destruct (choose_ub_set (map idx X)) as [k ?].
    revert Hinh.
    case hf; auto.
    intros [q ?].
    destruct H as [z [??]].
    exists (idx z).
    exists (idx z). split; auto.
    apply in_map. auto.
    
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
    rewrite (ds_ident hf I DS k (ord_refl _ _)).
    simpl. auto.
    exists k; simpl. exists (ord_refl _ _). exists Hak.
    rewrite (ds_ident hf I DS k (ord_refl _ _)).
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
    rewrite (ds_ident hf I DS k (ord_refl _ _)).
    simpl. auto.
    exists k; simpl. exists Hak. exists (ord_refl _ _).
    rewrite (ds_ident hf I DS k (ord_refl _ _)).
    simpl. auto.
    apply cons_elem. right.
    rewrite e; auto.
    
    destruct X0 as [M HM].
    exists (map (LimSet k) (mub_closure (ds_plt hf I DS k) M)).
    split.
    hnf; intros.
    rewrite HM in H.
    destruct H as [q [??]].
    apply in_map_iff in H.
    destruct H as [q' [??]].
    subst q.
    assert (q' ∈ mub_closure (ds_plt hf I DS k) M).
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
    assert (q ∈ mub_closure (ds_plt hf I DS k) M).
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
    destruct (choose_ub (idx z) k) as [k' [Hzk' Hkk']].
    generalize (embed_directed0 (ds_hom DS k k' Hkk')
        (ds_hom DS (idx z) k' Hzk' (elem z))).
    rewrite H at 1.
    intros [q ?].
    destruct (mub_complete (ds_plt hf I DS k) nil q) as [q' [??]].
    hnf. pattern hf at 1. rewrite H. auto.
    hnf; simpl; intros. apply nil_elem in H1. elim H1.
    assert (q' ∈ mub_closure (ds_plt hf I DS k) M).
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
    rewrite limset_order_exists_forall in H2.
    simpl in *.
    generalize (H2 k' Hkk' Hzk'). intros.
    destruct (embed_directed2 (ds_hom DS k k' Hkk')
      (ds_hom DS (idx z) k' Hzk' (elem z)))
      with x'' y'' as [c [?[??]]]; auto.
    destruct (mub_complete (ds_plt hf I DS k)
      (x''::y''::nil) c) as [c' [??]].
    apply elem_inh with x''. apply cons_elem; auto.
    hnf; simpl; intros.
    apply cons_elem in H9. destruct H9.
    rewrite H9; auto.
    apply cons_elem in H9. destruct H9.
    rewrite H9; auto.
    apply nil_elem in H9. elim H9.
    assert (c' ∈ mub_closure (ds_plt hf I DS k) M).
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
    apply cons_elem in H11. destruct H11.
    rewrite H11; auto.
    exists x''; split; auto.
    apply cons_elem in H11. destruct H11.
    rewrite H11; auto.
    exists y''; split; auto.
    apply nil_elem in H11. elim H11.
    destruct H11 as [c'' [??]].
    exists (LimSet k c'').
    split.
    rewrite H3.
    exists k'. simpl. exists Hkk'. exists Hkk'.
    apply embed_mono; auto.
    rewrite <- H12.
    destruct H9.
    apply H9. apply cons_elem; auto.
    split.
    rewrite H4.
    exists k'. simpl. exists Hkk'. exists Hkk'.
    apply embed_mono; auto.
    rewrite <- H12.
    destruct H9.
    apply H9.
    apply cons_elem. right.
    apply cons_elem. auto.
    apply finsubset_elem.
    intros. rewrite <- H13; auto.
    split; auto.
    exists (LimSet k c'').
    split; auto.
    apply in_map. auto.
    exists k'. simpl.
    exists Hkk'. exists Hzk'.
    transitivity (ds_hom DS k k' Hkk' c); auto.
    apply embed_mono.
    rewrite <- H12; auto.
    intros. rewrite <- H1. auto.
    intros. rewrite <- H1. auto.
  Qed.

  Definition limset_plotkin : plotkin_order hf limord :=
    norm_plt limord limord_effective hf limord_has_normals.

  Program Definition limset_spoke (i:I) : hom (EMBED hf) (ds_F DS i) limord
    := Embedding hf (ds_F DS i) limord (fun x => LimSet i x) _ _ _ _.
  Next Obligation.
    intros. hnf. simpl. exists i. exists (ord_refl _ _). exists (ord_refl _ _).
    rewrite (ds_ident hf I DS i (ord_refl I i)). simpl. auto.
  Qed.
  Next Obligation.
    intros. 
    destruct H as [k [Hki [Hki' ?]]]. simpl in *.
    rewrite <- (ds_compose hf I DS i k k Hki' (ord_refl I k) Hki) in H.
    rewrite (ds_ident hf I DS k (ord_refl I k)) in H.
    simpl in H.
    apply embed_reflects in H. auto.
  Qed.
  Next Obligation.
    intros.
    destruct (choose_ub i (idx y)) as [k [??]].
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
    destruct (choose_ub k1 k2) as [k [??]].
    assert (i ≤ k). transitivity k1; auto.
    assert (idx y ≤ k). transitivity k1; auto.
    destruct (embed_directed2 (ds_hom DS i k H3)
      (ds_hom DS (idx y) k H4 (elem y)) a b) as [q [?[??]]].
    rewrite <- (ds_compose hf I DS i k1 k Hik1 H1 H3).
    rewrite <- (ds_compose hf I DS (idx y) k1 k Hyk1 H1 H4).
    simpl. apply embed_mono. auto.
    rewrite <- (ds_compose hf I DS i k2 k Hik2 H2 H3).
    rewrite <- (ds_compose hf I DS (idx y) k2 k Hyk2 H2 H4).
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
    rewrite (ds_ident hf I DS j (ord_refl _ _)). simpl; auto.
    exists j. simpl. exists (ord_refl _ _). exists Hij.
    rewrite (ds_ident hf I DS j (ord_refl _ _)). simpl; auto.
  Qed.

  Lemma limset_complete : forall y:limord, exists i x, limset_spoke i x ≈ y.
  Proof.
    intros. exists (idx y). exists (elem y).
    simpl.
    destruct y. simpl; auto.
  Qed.

  Canonical Structure bilimit_construction : bilimit hf I :=
    Bilimit hf I DS
      limord
      limord_effective
      limset_plotkin
      limset_spoke
      limset_spoke_commute
      limset_complete.
End bilimit.
