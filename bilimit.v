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

Module PLT.
  Record class_of hf (A:Type) :=
    Class
    { cls_preord : Preord.mixin_of A
    ; cls_ord := Preord.Pack A cls_preord
    ; cls_effective : effective_order cls_ord
    ; cls_plotkin : plotkin_order hf cls_ord
    }.

  Record ob hf := Ob { carrier :> Type; class : class_of hf carrier }.

  Definition effective hf (X:ob hf) := cls_effective _ _ (class hf X).
  Definition plotkin hf (X:ob hf)   := cls_plotkin _ _ (class hf X).
  Definition ord hf (X:ob hf)       := cls_ord _ _ (class hf X).

  Arguments effective [hf] X.
  Arguments plotkin [hf] X.
  Arguments ord [hf] X.

  Canonical Structure ord.
  Canonical Structure dec hf (X:ob hf) := eff_to_ord_dec (ord X) (effective X).

  Arguments dec [hf] X.
End PLT.
Canonical Structure PLT.ord.
Canonical Structure PLT.dec.
Coercion PLT.ord : PLT.ob >-> preord.

Program Definition empty_eff : effective_order emptypo :=
  EffectiveOrder _ _ (fun x => None) _.
Next Obligation.
  intros. elim x.
Qed.
Next Obligation.
  intros. elim x.
Qed.

Program Definition empty_plotkin hf : plotkin_order hf emptypo :=
  PlotkinOrder hf emptypo _ (fun _ => nil) _ _ _.
Next Obligation.
  repeat intro. elim x.
Qed.
Next Obligation.
  repeat intro. elim a.
Qed.
Next Obligation.  
  repeat intro. elim x.
Qed.
Next Obligation.
  repeat intro. elim a.
Qed.

Definition empty_plt hf : PLT.ob hf :=
  PLT.Ob hf False (PLT.Class _ _ (Preord.mixin emptypo) empty_eff (empty_plotkin hf)).

Record embedding (hf:bool) (A B:PLT.ob hf) :=
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

Program Definition embed_ident (hf:bool) (A:PLT.ob hf) : embedding hf A A :=
  Embedding hf A A (fun x => x) _ _ _ _.
Solve Obligations using (intros; auto).
Next Obligation.
  intros. destruct hf; auto. exists y; auto.
Qed.
Next Obligation.
  intros. exists y. intuition.
Qed.

Program Definition embed_compose (hf:bool) A B C
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
  Comp.Pack (PLT.ob hf) (embedding hf) (embed_comp_mixin hf).

Program Definition embed_func {hf A B} (E:embedding hf A B) : PLT.ord A → PLT.ord B :=
  Preord.Hom A B (embed E) (embed_mono E).
Coercion embed_func : embedding >-> hom.

Program Definition embed_cat_class hf :
  Category.class_of (PLT.ob hf) (embedding hf) :=
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
  Category (PLT.ob hf) (embedding hf) (embed_cat_class hf).

Notation "A ⇀ B" := (hom (EMBED _) A B) (at level 70, no associativity).

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
  ; ds_F    : I -> PLT.ob hf
  ; ds_hom : forall i j:I, i ≤ j -> ds_F i ⇀ ds_F j
  ; ds_ident : forall i (Hii:i≤i), ds_hom i i Hii ≈ id
  ; ds_compose : forall i j k (Hij:i≤j) (Hjk:j≤k) (Hik:i≤k),
                       ds_hom j k Hjk ∘ ds_hom i j Hij ≈ ds_hom i k Hik
  }.
Arguments ds_F [hf] [I] _ _.
Arguments ds_hom [hf] [I] _ _ _ _.

Record cocone (hf:bool) (I:preord) (DS:directed_system hf I) :=
  Cocone
  { cocone_point :> PLT.ob hf
  ; cocone_spoke : forall i, ds_F DS i ⇀ cocone_point
  ; cocone_commute : forall i j (Hij:i≤j),
       cocone_spoke i ≈ cocone_spoke j ∘ ds_hom DS i j Hij
  }.
Arguments cocone_point [hf] [I] [DS] _.
Arguments cocone_spoke [hf] [I] [DS] _ _.
Arguments cocone_commute [hf] [I] [DS] _ _ _ _.

Record bilimit (hf:bool) (I:preord) (DS:directed_system hf I) 
  (XC:cocone hf I DS) :=
  Bilimit
  { bilim_univ : forall (YC:cocone hf I DS), XC ⇀ YC
  ; bilim_commute : forall (YC:cocone hf I DS) i,
       cocone_spoke YC i ≈ bilim_univ YC ∘ cocone_spoke XC i
  ; bilim_uniq : forall (YC:cocone hf I DS) (f:XC ⇀ YC),
       (forall i, cocone_spoke YC i ≈ f ∘ cocone_spoke XC i) ->
       f ≈ bilim_univ YC
  }.
Arguments bilim_univ [hf] [I] [DS] [XC] b YC.
Arguments bilim_commute [hf] [I] [DS] [XC] b YC i.
Arguments bilim_uniq [hf] [I] [DS] [XC] b YC f _.

Lemma embed_unlift hf (A B:PLT.ob hf) (f g:A ⇀ B) x :
  f ≤ g -> f x ≤ g x.
Proof.
  intros. apply H; auto.
Qed.

Lemma use_ord (A:preord) (a b c d:A) :
  b ≤ c -> a ≤ b -> c ≤ d -> a ≤ d.
Proof.
  intros.
  transitivity b; auto.
  transitivity c; auto.
Qed.
Arguments use_ord [A] [a] [b] [c] [d] _ _ _.


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
         match eff_enum _ (ds_Ieff hf I DS) p with
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
    generalize (eff_complete _ (ds_Ieff hf I DS) i).
    intros [p ?].
    case_eq (eff_enum I (ds_Ieff hf I DS) p); intros.
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
    destruct (choose_ub (idx z) k) as [k' [Hzk' Hkk']].
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
    rewrite limset_order_exists_forall in H2.
    simpl in *.
    generalize (H2 k' Hkk' Hzk'). intros.
    destruct (embed_directed2 (ds_hom DS k k' Hkk')
      (ds_hom DS (idx z) k' Hzk' (elem z)))
      with x'' y'' as [c [?[??]]]; auto.
    destruct (mub_complete (PLT.plotkin (ds_F DS k))
      (x''::y''::nil) c) as [c' [??]].
    apply elem_inh with x''. apply cons_elem; auto.
    hnf; simpl; intros.
    apply cons_elem in H9. destruct H9.
    rewrite H9; auto.
    apply cons_elem in H9. destruct H9.
    rewrite H9; auto.
    apply nil_elem in H9. elim H9.
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

  Definition bilim : PLT.ob hf :=
    PLT.Ob hf limset (PLT.Class _ _ limord_mixin limord_effective limset_plotkin).
  
  Program Definition limset_spoke (i:I) : hom (EMBED hf) (ds_F DS i) bilim
    := Embedding hf (ds_F DS i) bilim (fun x => LimSet i x) _ _ _ _.
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

  Definition bilimit_cocone : cocone hf I DS :=
    Cocone hf I DS bilim limset_spoke limset_spoke_commute.

  Section bilimit_univ.
    Variable YC:cocone hf I DS.

    Program Definition limord_univ : bilim ⇀ YC :=
      Embedding hf bilim YC
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
      destruct (choose_ub i i') as [k [Hk1 Hk2]].
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
      destruct (choose_ub_set nil) as [i _].
      rewrite H. hnf. auto.
      generalize (embed_directed0 (cocone_spoke YC i) y).
      pattern hf at 1. rewrite H.
      intros [x ?].
      exists (LimSet i x). auto.
    Qed.
    Next Obligation.
      intros.
      destruct a as [i a].
      destruct b as [j b].
      destruct (choose_ub i j) as [k [Hk1 Hk2]].
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
      rewrite (ds_ident _ _ DS k (ord_refl _ _)).
      simpl. auto.
      exists k. simpl.
      exists Hk2. exists (ord_refl _ _).
      rewrite (ds_ident _ _ DS k (ord_refl _ _)).
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

    Lemma limord_univ_uniq (f:bilim ⇀ YC) :
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

  Definition bilimit_construction : bilimit hf I DS bilimit_cocone :=
    Bilimit hf I DS
      bilimit_cocone
      limord_univ
      limord_univ_commute
      limord_univ_uniq.
End bilimit.

Program Definition dir_sys_app hf I
  (DS:directed_system hf I) 
  (F:functor (EMBED hf) (EMBED hf))
  :  directed_system hf I :=
  DirSys hf I 
    (ds_Ieff hf I DS)
    (ds_Idir hf I DS)
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

Arguments dir_sys_app [hf] [I] DS F.

Program Definition cocone_app hf I (DS:directed_system hf I)
  (CC:cocone hf I DS) (F:functor (EMBED hf) (EMBED hf))
  : cocone hf I (dir_sys_app DS F) :=
  Cocone hf I (dir_sys_app DS F) (F CC) (fun i => F@cocone_spoke CC i) _.
Next Obligation.
  simpl; intros.
  rewrite <- (Functor.compose F). 2: reflexivity.
  rewrite <- (cocone_commute CC i j Hij).
  auto.
Qed.
Arguments cocone_app [hf] [I] [DS] CC F.

Definition continuous_functor hf (F:functor (EMBED hf) (EMBED hf)) :=
  forall I (DS:directed_system hf I) CC,
    bilimit hf I DS CC ->
    bilimit hf I (dir_sys_app DS F) (cocone_app CC F).
Arguments continuous_functor [hf] F.

Require Import Arith.
Require Import NArith.
Section fixpoint.
  Variable F:functor (EMBED true) (EMBED true).

  Program Definition nat_ord := Preord.Pack nat (Preord.Mixin nat le _ _).
  Solve Obligations using eauto with arith.
  
  Program Definition nat_eff : effective_order nat_ord :=
    EffectiveOrder nat_ord le_dec (fun x => Some (N.to_nat x)) _.
  Next Obligation.
    intros. exists (N.of_nat x).
    rewrite Nat2N.id. auto.
  Qed.

  Lemma nat_dir hf : directed hf (eff_enum nat_ord nat_eff).
  Proof.
    apply prove_directed.
    destruct hf. auto.
    exists 0. apply eff_complete.
    intros.
    exists (max x y).
    split. simpl. apply Max.le_max_l.
    split. simpl. apply Max.le_max_r.
    apply eff_complete.
  Qed.

  Fixpoint iterF (x:nat) : PLT.ob true :=
    match x with
    | O => empty_plt true
    | S x' => F (iterF x')
    end.

  Lemma HSle0 j (Hij: S j <= O) : False.
  Proof.
    inversion Hij.
  Qed.

  Program Definition empty_bang X : empty_plt true ⇀ X :=
    Embedding true (empty_plt true) X (fun x => False_rect _ x) _ _ _ _.
  Next Obligation.
    intros. elim a.
  Qed.
  Next Obligation.
    intros. elim a.
  Qed.
  Next Obligation.
    intros. auto.
  Qed.
  Next Obligation.
    intros. elim a.
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

  Program Definition kleene_chain : directed_system true nat_ord :=
    DirSys true nat_ord nat_eff (nat_dir true) iterF iter_hom _ _.
  Next Obligation.      
    induction i; simpl; intros.
    split; hnf; intros.
    elim x. elim x.
    apply Functor.ident; auto.
  Qed.
  Next Obligation.
    induction i. simpl; intros.
    split; hnf; intro x; elim x.
    intros. destruct j.
    elimtype False. inversion Hij.
    destruct k.
    elimtype False. inversion Hjk.
    simpl.
    rewrite <- (Functor.compose F _ _ _ (iter_hom j k (gt_S_le j k Hjk))).
    reflexivity. auto.
  Qed.

  Definition fixpoint := bilim true nat_ord kleene_chain.

  Hypothesis Fcontinuous : continuous_functor F.
  
  Let BL := Fcontinuous nat_ord kleene_chain
      (bilimit_cocone true nat_ord kleene_chain)
      (bilimit_construction true nat_ord kleene_chain).

  Program Definition cocone_up : 
    cocone true nat_ord (dir_sys_app kleene_chain F)
    := Cocone _ _ _ _
      (fun i => limset_spoke _ _ kleene_chain (S i)) _.
  Next Obligation.
    simpl; intros.
    cut (forall x,
      limset_spoke true nat_ord kleene_chain (S i) x
      ≈ limset_spoke true nat_ord kleene_chain (S j) ((F @ iter_hom i j Hij) x)).
    intro H. split; intro x; destruct (H x); auto.
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

  Definition fixpoint_roll : F fixpoint ⇀ fixpoint := bilim_univ BL cocone_up.


  Definition fixpoint_alg : alg (EMBED true) F
    := Alg (fixpoint : ob (EMBED true)) fixpoint_roll.

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
      split; hnf; intros x; elim x.
      destruct j. inversion Hij.
      simpl.
      split; hnf; intro.
      simpl. apply embed_mono.
      change ((F@cata_hom' i) x ≤
        (F @ cata_hom' j ∘ F @ iter_hom i j (gt_S_le i j Hij)) x).
      apply embed_unlift.
      rewrite <- (Functor.compose F).
      2: reflexivity.
      rewrite IHi; eauto.
      simpl. apply embed_mono.
      change ((F @ cata_hom' j ∘ F @ iter_hom i j (gt_S_le i j Hij)) x
        ≤ (F@cata_hom' i) x).
      apply embed_unlift.
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
      clear i' a' Hk2 H.
      revert k Hk1.
      induction i. elim a.
      intros.
      destruct k. inversion Hk1.
      simpl.
      apply embed_mono.
      rewrite (cata_hom_iter_hom i k  (gt_S_le i k Hk1)).
      rewrite Functor.compose. 2: reflexivity.
      auto.

      transitivity (cata_hom' k (iter_hom i' k Hk2 a')).
      apply embed_mono. auto.
      
      clear i a Hk1 H.
      revert k Hk2.
      induction i'. elim a'.
      intros.
      destruct k. inversion Hk2.
      simpl.
      apply embed_mono.
      change (((F@cata_hom' k ∘ F@iter_hom i' k (gt_S_le i' k Hk2)) a')
        ≤ (F@cata_hom' i') a').
      apply embed_unlift.
      rewrite <- (Functor.compose F).
      2: reflexivity.
      rewrite (cata_hom_iter_hom i' k  (gt_S_le i' k Hk2)).
      auto.
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
      cocone true nat_ord (dir_sys_app kleene_chain F) :=
      Cocone _ _ _ _ (fun i => cata_hom' (S i)) _.
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
      simpl. unfold fixpoint_roll.
      generalize (bilim_uniq BL AG_cocone).
      intros.
      rewrite (H (cata_hom ∘ bilim_univ BL cocone_up)).
      symmetry. apply H.

      intros. simpl.
      rewrite <- (cat_assoc (Alg.iota AG)).
      rewrite <- (Functor.compose F). 2: reflexivity.
      assert (cata_hom' i ≈ cata_hom ∘ limset_spoke _ _ kleene_chain i).
      split; hnf; simpl; auto.
      rewrite <- H0; auto.

      intros.
      rewrite <- (cat_assoc cata_hom).
      rewrite <- (bilim_commute BL cocone_up).
      split; hnf; simpl; auto.
    Qed.

  End cata.

  Program Definition fixpoint_initial : Alg.initial_alg (EMBED true) F :=
    Alg.Initial_alg fixpoint_alg cata_alg_hom _.
  Next Obligation.
    simpl; intros.
    cut (forall x, Alg.hom_map h x ≈ cata_hom M x).
    intro H. split; intro x; destruct (H x); auto.
    
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
    cut (limset_spoke true nat_ord kleene_chain (S i)
      ≈ fixpoint_roll ∘ F @ limset_spoke true nat_ord kleene_chain i).
    intros.
    split; hnf; intros; simpl; apply (embed_mono h).
    destruct H0. apply (H0 x).
    destruct H0. apply (H1 x).
    unfold fixpoint_roll.
    generalize (bilim_commute BL cocone_up). simpl; intros.
    apply (H0 i).
  Qed.
  
  Program Definition fixpoint_iso :
    F fixpoint ↔ fixpoint :=

    Isomorphism (EMBED true) (F fixpoint) fixpoint 
      fixpoint_roll (Alg.out _ F fixpoint_initial)
      (Alg.out_in _ F fixpoint_initial)
      (Alg.in_out _ F fixpoint_initial).

End fixpoint.

Check fixpoint.
Check fixpoint_iso.
