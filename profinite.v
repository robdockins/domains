Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import plotkin.
Require Import joinable.
Require Import approx_rels.
Require Import finord.

Module Type PLT_PARAM.
  Parameter hf:bool.
End PLT_PARAM.

Module XPLT (PARAM:PLT_PARAM).
Import PARAM.

  Record class_of (A:Type) :=
    Class
    { cls_preord : Preord.mixin_of A
    ; cls_ord := Preord.Pack A cls_preord
    ; cls_effective : effective_order cls_ord
    ; cls_plotkin : plotkin_order hf cls_ord
    }.

  Record ob := Ob { carrier :> Type; class : class_of carrier }.

  Definition effective (X:ob) := cls_effective _ (class X).
  Definition plotkin (X:ob)   := cls_plotkin _ (class X).
  Definition ord (X:ob)       := cls_ord _ (class X).

  Canonical Structure ord.
  Canonical Structure dec X := eff_to_ord_dec (ord X) (effective X).
  
  Record hom (A B:ob) :=
    Hom
    { hom_rel :> erel (ord A) (ord B)
    ; hom_order : forall x x' y y', x ≤ x' -> y' ≤ y ->
         (x,y) ∈ hom_rel -> (x',y') ∈ hom_rel
    ; hom_directed : directed_rel hf (ord A) (ord B) (effective A) hom_rel
    }.
  Arguments hom_rel [A] [B] h n.

  Program Definition hom_ord_mixin (A B:ob) : Preord.mixin_of (hom A B) :=
    Preord.Mixin (hom A B) (fun f g => hom_rel f ≤ hom_rel g) _ _.
  Solve Obligations of hom_ord_mixin using (intros; eauto).
  
  Canonical Structure hom_ord (A B:ob) := Preord.Pack (hom A B) (hom_ord_mixin A B).

  Definition hom_eq_mixin (A B:ob) := Preord.ord_eq (hom_ord A B).
  Canonical Structure hom_eq (A B:ob) := Eq.Pack (hom A B) (hom_eq_mixin A B).

  Definition ident (A:ob) : hom A A :=
    Hom A A (ident_rel (effective A))
            (ident_ordering (ord A) (effective A))
            (ident_image_dir hf (ord A) (effective A)).

  Program Definition compose (A B C:ob) (g:hom B C) (f:hom A B) : hom A C :=
    Hom A C (compose_rel (effective B) g f) _ _.
  Next Obligation.
    intros A B C g f. apply compose_ordering. apply hom_order. apply hom_order.
  Qed.
  Next Obligation.
    intros A B C g f. apply compose_directed. 
    apply hom_order. apply hom_order.
    apply hom_directed. apply hom_directed.
  Qed.

  Definition comp_mixin : Comp.mixin_of ob hom := Comp.Mixin ob hom ident compose.
  Canonical Structure comp : Comp.type := Comp.Pack ob hom comp_mixin.

  Lemma compose_mono (X Y Z:ob) (f f':hom X Y) (g g':hom Y Z) :
    f ≤ f' -> g ≤ g' -> g ∘ f ≤ g' ∘ f'.
  Proof.
    repeat intro; simpl in *.
    destruct a as [x z].
    apply compose_elem in H1.
    apply compose_elem.
    apply hom_order.
    destruct H1 as [y [??]].
    exists y. split.
    apply H; auto.
    apply H0; auto.
    apply hom_order.
  Qed.

  Lemma cat_axioms : Category.category_axioms ob hom hom_eq_mixin comp_mixin.
  Proof.
    constructor.

    intros. apply compose_ident_rel2. apply hom_order.
    intros. apply compose_ident_rel1. apply hom_order.
    intros. apply compose_assoc.
    intros. split; apply compose_mono; auto.
  Qed.

  Definition cat_class : Category.class_of ob hom :=
    Category.Class ob hom hom_eq_mixin comp_mixin cat_axioms.

  Definition prod (A B:ob) : ob :=
    Ob (carrier A * carrier B)
       (Class _ 
         (Preord.mixin (ord A × ord B))
         (effective_prod (effective A) (effective B))
         (plotkin_prod hf (ord A) (ord B) (effective A) (effective B) (plotkin A) (plotkin B))).
  Canonical Structure prod.
  
  Definition exp (A B:ob) : ob :=
    Ob (joinable_relation hf (ord A) (ord B))
       (Class _
         (joinable_rel_ord_mixin hf (ord A) (ord B))
         (joinable_rel_effective hf (ord A) (ord B) (effective A) (effective B) (plotkin A))
         (joinable_rel_plt hf (ord A) (ord B) (effective A) (plotkin A) (effective B) (plotkin B))).

  Definition app {A B} : hom (prod (exp A B) A) B :=
    Hom (prod (exp A B) A) B
      (apply_rel hf (ord A) (ord B) (effective A) (effective B) (plotkin A))
      (apply_rel_ordering hf (ord A) (ord B) (effective A) (effective B) (plotkin A))
      (apply_rel_dir hf (ord A) (ord B) (effective A) (effective B) (plotkin A)).
 
  Definition curry {C A B} (f:hom (prod C A) B) : hom C (exp A B) :=
    Hom C (exp A B)
      (curry_rel hf (ord A) (ord B) (ord C)
        (effective A) (effective B) (effective C) (plotkin A) 
        f (hom_order _ _ f))
      (curry_rel_ordering hf (ord A) (ord B) (ord C)
        (effective A) (effective B) (effective C) (plotkin A) 
        f (hom_order _ _ f))
      (curry_rel_dir hf (ord A) (ord B) (ord C)
        (effective A) (effective B) (effective C) (plotkin A) 
        f (hom_order _ _ f) (hom_directed _ _ f)
        (plotkin B)).

  Definition pair {C A B} (f:hom C A) (g:hom C B) : hom C (prod A B) :=
    Hom C (prod A B) 
      (pair_rel (effective C) f g)
      (pair_rel_ordering _ _ _ (effective C) f g (hom_order _ _ f) (hom_order _ _ g))
      (pair_rel_dir _ _ _ _ (effective C) f g 
        (hom_order _ _ f) (hom_order _ _ g)
        (hom_directed _ _ f) (hom_directed _ _ g)).

  Definition pi1 {A B} : hom (prod A B) A :=
    Hom (prod A B) A 
      (pi1_rel (effective A) (effective B))
      (pi1_rel_ordering _ _ (effective A) (effective B))
      (pi1_rel_dir _ _ _ (effective A) (effective B)).

  Definition pi2 {A B} : hom (prod A B) B :=
    Hom (prod A B) B 
      (pi2_rel (effective A) (effective B))
      (pi2_rel_ordering _ _ (effective A) (effective B))
      (pi2_rel_dir _ _ _ (effective A) (effective B)).

  Definition pair_map {A B C D} (f:hom A C) (g:hom B D) : hom (prod A B) (prod C D) :=
    pair (f ∘ pi1) (g ∘ pi2).

  Program Definition pair_map' {A B C D} (f:hom A C) (g:hom B D) : hom (prod A B) (prod C D) :=
    Hom (prod A B) (prod C D) (pair_rel' f g) _ _.
  Next Obligation.
    intros A B C D f g.
    apply pair_rel_order'; auto.
    apply hom_order.
    apply hom_order.
  Qed.    
  Next Obligation.
(* FIXME, move this proof into approx_rels.v *)

    repeat intro.
    destruct (hom_directed _ _ f (fst x) (image π₁ M)).
    apply inh_image; auto.
    red; intros. apply image_axiom2 in H0. destruct H0 as [y[??]].
    apply erel_image_elem.
    apply H in H0.
    apply erel_image_elem in H0.
    destruct x; destruct y.
    apply (pair_rel_elem' _ _ _ _ f g) in H0.
    simpl. destruct H0.
    apply member_eq with (c,c1); auto.
    simpl in H1.
    destruct H1; split; split; auto.
    apply hom_order.
    apply hom_order.
    destruct (hom_directed _ _ g (snd x) (image π₂ M)).
    apply inh_image; auto.
    red; intros. apply image_axiom2 in H1. destruct H1 as [y[??]].
    apply erel_image_elem.
    apply H in H1.
    apply erel_image_elem in H1.
    destruct x; destruct y.
    apply (pair_rel_elem' _ _ _ _ f g) in H1.
    simpl. destruct H1.
    apply member_eq with (c0,c2); auto.
    simpl in H2.
    destruct H2; split; split; auto.
    apply hom_order.
    apply hom_order.
    exists (x0,x1).
    destruct H0. destruct H1.
    split.
    red; intros.
    split.
    apply H0. apply image_axiom1'.
    exists x2. split; auto.
    apply H1. apply image_axiom1'.
    exists x2. split; auto.
    apply erel_image_elem.
    apply erel_image_elem in H2.
    apply erel_image_elem in H3.
    destruct x.
    apply (pair_rel_elem' _ _ _ _ f g).
    apply hom_order. apply hom_order.
    split; auto.
  Qed.

  Lemma pair_map_eq {A B C D} (f:hom A C) (g:hom B D) :
    pair_map f g ≈ pair_map' f g.
  Proof.
    red. simpl. symmetry.
    apply pair_rel_eq.
    apply hom_order.
    apply hom_order.
  Qed.

  Canonical Structure XPLT : category := Category ob hom cat_class.

  Record is_ep_pair (X Y:ob) (e:hom X Y) (p:hom Y X) :=
  IsEP
  { pe_ident : p ∘ e ≈ id
  ; ep_ident : e ∘ p ≤ id
  }.

  Record ep_pair (X Y:ob) :=
  EpPair
  { embed : hom X Y
  ; project : hom Y X
  ; ep_correct : is_ep_pair X Y embed project
  }.
  Arguments embed [X] [Y] e.
  Arguments project [X] [Y] e.

  Program Definition ep_id (X:ob) : ep_pair X X :=
    EpPair X X id id _.
  Next Obligation.
    intros. constructor.
    rewrite (cat_ident1 id(X)); auto.
    rewrite (cat_ident1 id(X)); auto.
  Qed.

  Program Definition ep_compose (X Y Z:ob) (g:ep_pair Y Z) (f:ep_pair X Y) :=
    EpPair X Z (embed g ∘ embed f) (project f ∘ project g) _.
  Next Obligation.
    intros.
    destruct g as [e' p' [??]].
    destruct f as [e p [??]]. simpl in *.
    constructor.
    rewrite <- (cat_assoc p).
    rewrite (cat_assoc p').
    rewrite pe_ident0.
    rewrite (cat_ident2 e).
    auto.
    rewrite <- (cat_assoc e').
    rewrite (cat_assoc e).
    transitivity (e' ∘ p'); auto.
    apply compose_mono; auto.
    transitivity (id ∘ p').
    apply compose_mono; auto.
    rewrite (cat_ident2 p').
    auto.
  Qed.    

  Lemma ep_pair_embed_eq_proj_eq : forall X Y e e' p p',
    is_ep_pair X Y e p -> 
    is_ep_pair X Y e' p' ->
    e ≈ e' -> p ≈ p'.
  Proof.
    intros.
    split.
    transitivity (id ∘ p).
    rewrite (cat_ident2 p). auto.
    destruct H0.
    rewrite <- pe_ident0.
    rewrite <- H1.
    rewrite <- (cat_assoc p').
    transitivity (p' ∘ id).
    apply compose_mono.
    destruct H. auto.
    auto.
    rewrite (cat_ident1 p'). auto.
    transitivity (id ∘ p').
    rewrite (cat_ident2 p'). auto.
    destruct H.
    rewrite <- pe_ident0.
    rewrite H1.
    rewrite <- (cat_assoc p).
    transitivity (p ∘ id).
    apply compose_mono.
    destruct H0. auto.
    auto.
    rewrite (cat_ident1 p). auto.
  Qed.    


  Program Definition ep_pair_eq_mixin X Y : Eq.mixin_of (ep_pair X Y) :=
    Eq.Mixin _ (fun f g => embed f ≈ embed g) _ _ _.
  Next Obligation.
    auto.
  Qed.
  Next Obligation.
    auto.
  Qed.
  Next Obligation.
    eauto.
  Qed.
    
  Definition ep_pair_comp_mixin : Comp.mixin_of ob ep_pair :=
    Comp.Mixin ob ep_pair ep_id ep_compose.

  Canonical Structure ep_pair_eq X Y := Eq.Pack (ep_pair X Y) (ep_pair_eq_mixin X Y).
  Canonical Structure ep_pair_comp := Comp.Pack ob ep_pair ep_pair_comp_mixin.

  Lemma ep_cat_axioms :
    Category.category_axioms ob ep_pair ep_pair_eq_mixin ep_pair_comp_mixin.
  Proof.  
    constructor; simpl; intros.
    red. simpl. apply (cat_ident1 (embed f)).
    red. simpl. apply (cat_ident2 (embed f)).
    red. simpl. apply (cat_assoc (embed f)).
    red. simpl. apply (cat_respects H H0).
  Qed.

  Definition ep_cat_class : Category.class_of ob ep_pair :=
    Category.Class ob ep_pair ep_pair_eq_mixin ep_pair_comp_mixin ep_cat_axioms.

  Canonical Structure XPLT_EP :=
    Category ob ep_pair ep_cat_class.

  Definition find_inhabitant' : forall A (P:eset A) (H:einhabited P),
    { a:A | a ∈ P }.
  Proof.
    intros. destruct (find_inhabitant A P H).
    exists x.
    destruct s as [n [??]].
    exists n. rewrite H0. auto.
  Qed.

  Definition choose' A P H := proj1_sig (find_inhabitant' A P H).

  Section ep_pair_embed_func.
    Variables X Y:ob.
    Variable e : hom X Y.
    Variable p : hom Y X.
    Variable Hep : is_ep_pair X Y e p.

    Section embed_func.
      Variable x:X.

      Lemma ep_semidec : semidec (fun y => (x,y) ∈ hom_rel e /\ (y,x) ∈ hom_rel p).
      Proof.
        apply semidec_conj.
        apply semidec_iff with (fun y => y ∈ erel_image (ord X) (ord Y) (dec X) 
          (hom_rel e) x).
        intros. apply erel_image_elem.
        apply semidec_in. apply dec.
        apply semidec_iff with (fun y => y ∈ erel_inv_image (ord Y) (ord X) (dec X) 
          (hom_rel p) x).
        intros. apply erel_inv_image_elem.
        apply semidec_in. apply dec.
      Qed.

      Definition embed_image :=
        esubset (fun y => (x,y) ∈ hom_rel e /\ (y,x) ∈ hom_rel p)
           ep_semidec 
           (eff_enum (ord Y) (effective Y)).

      Lemma embed_image_inhabited : einhabited embed_image.
      Proof.
        apply member_inhabited.
        destruct (pe_ident _ _ _ _ Hep).
        assert ((x,x) ∈ hom_rel (p ∘ e)).
        apply H0.
        apply ident_elem. auto.
        simpl in H1.
        apply compose_elem in H1.
        2: apply hom_order.
        destruct H1 as [y [??]].
        exists y. unfold embed_image.
        apply esubset_elem.
        split.
        apply eff_complete.
        split; auto.
      Qed.
    End embed_func.  
    
    Program Definition embed_func : Preord.hom (ord X) (ord Y) :=
      Preord.Hom (ord X) (ord Y)
        (fun x => choose' (ord Y) (embed_image x) (embed_image_inhabited x)) _.
    Next Obligation.
      intros.
      unfold choose'.
      destruct (find_inhabitant' (ord Y) (embed_image a) (embed_image_inhabited a))
        as [y ?]. simpl.
      destruct (find_inhabitant' (ord Y) (embed_image b) (embed_image_inhabited b))
        as [y' ?]. simpl.

      unfold embed_image in *.
      apply esubset_elem in m.
      apply esubset_elem in m0.
      destruct m as [_ [??]].
      destruct m0 as [_ [??]]. 
      destruct Hep.
      cut ((y',y) ∈ hom_rel id).
      intros. simpl in H4.
      apply ident_elem in H4. auto.
      apply ep_ident0.
      simpl.
      apply compose_elem; auto.
      apply hom_order.
      exists a. split; auto.
      apply hom_order with y' b; auto.
    Qed.

    Lemma embed_func_reflects : forall x x',
      embed_func#x ≤ embed_func#x' -> x ≤ x'.
    Proof.
      intros x x'. unfold embed_func. simpl. unfold choose'.
      destruct (find_inhabitant' (ord Y) (embed_image x) (embed_image_inhabited x))
        as [y ?]. simpl.
      destruct (find_inhabitant' (ord Y) (embed_image x') (embed_image_inhabited x'))
        as [y' ?]. simpl.
      intros.
      unfold embed_image in *.
      apply esubset_elem in m.
      apply esubset_elem in m0.
      destruct m. destruct m0.
      destruct Hep.
      cut ((x',x) ∈ hom_rel id).
      simpl; intros. apply ident_elem in H4. auto.
      apply pe_ident0.
      simpl. apply compose_elem.
      apply hom_order.
      exists y'. intuition.
      apply hom_order with y x; auto.
    Qed.    

    Lemma embed_func_directed0 : forall y,
      if hf then True else exists x, embed_func#x ≤ y.
    Proof.
      intros. case_eq hf; intros; auto.
      destruct (hom_directed _ _ p y nil).
      rewrite H. hnf. auto.
      hnf; intros. apply nil_elem in H0. elim H0.
      destruct H0.
      exists x. apply erel_image_elem in H1.
      unfold embed_func; simpl.
      unfold choose'.
      destruct (find_inhabitant' (ord Y) (embed_image x) (embed_image_inhabited x))
        as [y' ?]. simpl in *.
      unfold embed_image in m.
      apply esubset_elem in m.
      destruct m as [_ [??]].
      destruct Hep.
      cut ((y,y') ∈ hom_rel id).
      simpl; auto.
      intros. apply ident_elem in H4. auto.
      apply ep_ident0.
      simpl. apply compose_elem.
      apply hom_order.
      exists x; auto.
    Qed.

    Lemma embed_func_directed2 : forall y, forall a b,
      embed_func#a ≤ y ->
      embed_func#b ≤ y ->
      exists c, embed_func#c ≤ y /\ a ≤ c /\ b ≤ c.
    Proof.
      intro. intros.
      unfold embed_func in *. simpl in *.
      unfold choose' in *.
      destruct (find_inhabitant' (ord Y) (embed_image a) (embed_image_inhabited a))
        as [ya ?]. simpl in *.
      destruct (find_inhabitant' (ord Y) (embed_image b) (embed_image_inhabited b))
        as [yb ?]. simpl in *.
      unfold embed_image in m.
      unfold embed_image in m0.
      apply esubset_elem in m.
      apply esubset_elem in m0.
      destruct m as [_ [??]].
      destruct m0 as [_ [??]].
      assert ((y,a) ∈ hom_rel p).
      apply hom_order with ya a; auto.
      assert ((y,b) ∈ hom_rel p).
      apply hom_order with yb b; auto.
      destruct (hom_directed _ _ p y (a::b::nil)%list).
      destruct hf; hnf; auto.
      exists a. apply cons_elem; auto.
      hnf; simpl; intros.
      apply erel_image_elem.
      apply cons_elem in H7. destruct H7.
      apply hom_order with y a; auto.
      apply cons_elem in H7. destruct H7.
      apply hom_order with y b; auto.
      apply nil_elem in H7. elim H7.
      destruct H7.
      apply erel_image_elem in H8.
      rename x into q.
      exists q.
      split.
      destruct (find_inhabitant' (ord Y) (embed_image q) (embed_image_inhabited q))
        as [yq ?]. simpl in *.
      unfold embed_image in m.
      apply esubset_elem in m.
      destruct m as [_ [??]].
      destruct Hep.
      cut ((y,yq) ∈ hom_rel id).
      simpl; intros. apply ident_elem in H11. auto.
      apply ep_ident0.
      simpl.
      apply compose_elem.
      apply hom_order.
      exists q. split; auto.
      split; apply H7; auto.
      apply cons_elem; auto.
      apply cons_elem; right.
      apply cons_elem; auto.
    Qed.
  End ep_pair_embed_func.

  Section embed_func_ep_pair.
    Variables X Y:ob.
    Variable embed : (ord X) → (ord Y).
    Hypothesis embed_reflects : forall x x',
      embed#x ≤ embed#x' -> x ≤ x'.
    Hypothesis embed_func_directed0 : forall y,
      if hf then True else exists x, embed#x ≤ y.
    Hypothesis embed_directed2 : forall y, forall a b,
      embed#a ≤ y ->
      embed#b ≤ y ->
      exists c, embed#c ≤ y /\ a ≤ c /\ b ≤ c.

    Definition project_rel :=
      esubset_dec (ord Y×ord X)
         (fun yx => fst yx ≥ embed#(snd yx))
         (fun yx => eff_ord_dec (ord Y) (effective Y) (embed#(snd yx)) (fst yx))
         (eprod (eff_enum (ord Y) (effective Y)) (eff_enum (ord X) (effective X))).

    Lemma project_rel_elem : forall y x,
      embed#x ≤ y <-> (y,x) ∈ project_rel.
    Proof.
      intros. split; intros.
      unfold project_rel.
      apply esubset_dec_elem.
      intros.
      change (fst y0) with (π₁#y0).
      change (snd y0) with (π₂#y0).
      rewrite <- H0. auto.
      split; auto.
      apply elem_eprod; split; apply eff_complete; auto.
      unfold project_rel in H.
      apply esubset_dec_elem in H.
      destruct H; auto.
      intros.
      change (fst y0) with (π₁#y0).
      change (snd y0) with (π₂#y0).
      rewrite <- H0. auto.
    Qed.

    Program Definition project_hom : hom Y X :=
      Hom Y X project_rel _ _.
    Next Obligation.
      intros. 
      apply project_rel_elem in H1.
      apply project_rel_elem.
      transitivity x; auto.
      transitivity (embed#y); auto.
    Qed.
    Next Obligation.
      red. intro y.
      apply prove_directed.
      case_eq hf; simpl; intros; auto.
      rewrite H in embed_func_directed0.
      destruct (embed_func_directed0 y) as [x ?].
      exists x.
      apply erel_image_elem.
      apply project_rel_elem. auto.
      
      intros.
      apply erel_image_elem in H.
      apply erel_image_elem in H0.
      apply project_rel_elem in H.
      apply project_rel_elem in H0.
      destruct (embed_directed2 y x y0) as [z [?[??]]]; auto.
      exists z; split; auto. split; auto.
      apply erel_image_elem.
      apply project_rel_elem. auto.
    Qed.      

    Definition embed_rel :=
      esubset_dec (ord X×ord Y)
         (fun xy => embed#(fst xy) ≥ snd xy)
         (fun xy => eff_ord_dec (ord Y) (effective Y) (snd xy) (embed#(fst xy)))
         (eprod (eff_enum (ord X) (effective X)) (eff_enum (ord Y) (effective Y))).

    Lemma embed_rel_elem : forall y x,
      embed#x ≥ y <-> (x,y) ∈ embed_rel.
    Proof.
      intros; split; intros.
      unfold embed_rel.
      apply esubset_dec_elem.
      intros.
      change (fst y0) with (π₁#y0).
      change (snd y0) with (π₂#y0).
      rewrite <- H0. auto.
      split; auto.
      apply elem_eprod; split; apply eff_complete; auto.
      unfold embed_rel in H.
      apply esubset_dec_elem in H.
      destruct H; auto.
      intros.
      change (fst y0) with (π₁#y0).
      change (snd y0) with (π₂#y0).
      rewrite <- H0. auto.
    Qed.

    Program Definition embed_hom : hom X Y :=
      Hom X Y embed_rel _ _.
    Next Obligation.
      intros.
      apply embed_rel_elem in H1.
      apply embed_rel_elem.
      transitivity y; auto.
      transitivity (embed#x); auto.
    Qed.
    Next Obligation.      
      hnf. simpl; intros.
      hnf. simpl; intros.
      exists (embed#(x:ord X)).
      split.
      hnf; simpl; intros.
      apply H in H0.
      apply erel_image_elem in H0.
      apply embed_rel_elem in H0. auto.
      apply erel_image_elem.
      apply embed_rel_elem.
      auto.
    Qed.

    Lemma embed_func_is_ep_pair : is_ep_pair X Y embed_hom project_hom.
    Proof.
      constructor.
      split.
      hnf; simpl; intros.
      destruct a as [x x'].
      apply compose_elem in H.
      2: apply embed_hom_obligation_1.
      apply ident_elem.
      destruct H as [y [??]].
      apply embed_rel_elem in H.
      apply project_rel_elem in H0.
      apply embed_reflects.
      transitivity y; auto.
      hnf; simpl; intros.
      destruct a as [x x'].
      apply ident_elem in H.
      apply compose_elem.
      apply embed_hom_obligation_1.
      exists (embed#(x:ord X)).
      split.
      apply embed_rel_elem. auto.
      apply project_rel_elem. auto.

      hnf; simpl; intros.      
      destruct a as [y y'].
      apply compose_elem in H.
      2: apply project_hom_obligation_1.
      apply ident_elem.
      destruct H as [x [??]].
      apply project_rel_elem in H.
      apply embed_rel_elem in H0.
      transitivity (embed#x); auto.
    Qed.
  End embed_func_ep_pair.


  Record directed_system (I:preord) :=
  DirSys
  { ds_eff : effective_order I
  ; ds_dir : directed hf (eff_enum I ds_eff)
  ; ds_F   : I -> ob
  ; ds_hom : forall i j:I, i ≤ j -> ep_pair (ds_F i) (ds_F j)
  ; ds_compose : forall i j k (Hij:i≤j) (Hjk:j≤k) (Hik:i≤k),
                       ds_hom j k Hjk ∘ ds_hom i j Hij ≈ ds_hom i k Hik
  ; ds_ident : forall i (Hii:i≤i), ds_hom i i Hii ≈ ep_id (ds_F i)
  }.

  Record is_bilimit (I:preord) (DS:directed_system I) (V:ob) :=
  IsBilimit
  { bilimit_spoke : forall i:I, ep_pair (ds_F I DS i) V
  ; bilimit_commute : forall i j (Hij:i≤j),
           bilimit_spoke j ∘ ds_hom I DS i j Hij ≈ bilimit_spoke i
  ; bilimit_sup : forall x y:V, exists i,
          x ≥ y -> 
          (x,y) ∈ hom_rel (embed (bilimit_spoke i) ∘ project (bilimit_spoke i))
  }.

  Lemma ds_ident' I (Hds:directed_system I) :
    forall i (Hii:i≤i), project (ds_hom I Hds i i Hii) ≈ id.
  Proof.
    intros.
    generalize (ds_ident I Hds i Hii).
    intro.
    eapply ep_pair_embed_eq_proj_eq; eauto.
    apply ep_correct.
    constructor.
    destruct H. simpl in *.
    rewrite (cat_ident2 (embed (ds_hom I Hds i i Hii))).
    split; auto.
    rewrite (cat_ident1 (embed (ds_hom I Hds i i Hii))).
    destruct H; simpl in *; auto.
  Qed.

  Lemma ds_compose' I (Hds:directed_system I) :
    forall i j k (Hij:i≤j) (Hjk:j≤k) (Hik:i≤k),
      project (ds_hom I Hds i j Hij) ∘ project (ds_hom I Hds j k Hjk) ≈ project (ds_hom I Hds i k Hik).
  Proof.
    intros.
    generalize (ds_compose I Hds i j k Hij Hjk Hik). intros.
    red in H. simpl in H.
    change (project (ds_hom I Hds j k Hjk ∘ ds_hom I Hds i j Hij) ≈ project (ds_hom I Hds i k Hik)).
    eapply ep_pair_embed_eq_proj_eq; eauto.
    apply (ep_correct _ _ (ds_hom I Hds j k Hjk ∘ ds_hom I Hds i j Hij)).
    apply ep_correct.
  Qed.


  (* FIXME: move *)
  Canonical Structure Ndec := OrdDec N (eff_ord_dec _ effective_Nord).

  Section fds.
    Variable I:preord.
    Variable DS : directed_system I.

    Fixpoint clip_set (A:ob) (X:finset N) (Y:eset (ord A)) : finset (ord A) :=
      match X with
      | nil => nil
      | cons x xs =>
            match Y x with
            | Some a => cons a (clip_set A xs Y)
            | None   => clip_set A xs Y
            end
      end.

    Lemma clip_set_elem A X Y a :
      a ∈ clip_set A X Y <->
        exists n a', n ∈ X /\ Y n = Some a' /\ a ≈ a'.
    Proof.
      induction X; split; simpl; intuition.
      apply nil_elem in H. elim H.
      destruct H as [n [a' [?[??]]]].
      apply nil_elem in H. elim H.
      case_eq (Y a0); intros.
      rewrite H2 in H.
      apply cons_elem in H. destruct H.
      exists a0. exists c. split; simpl; auto.
      apply cons_elem; auto.
      destruct H0 as [n [a' [?[??]]]]; auto.
      exists n. exists a'. intuition.
      apply cons_elem; auto.
      rewrite H2 in H.
      destruct H0 as [n [a' [?[??]]]]; auto.
      exists n. exists a'. intuition.
      apply cons_elem; auto.

      case_eq (Y a0); intros.
      destruct H as [n [a' [?[??]]]].
      apply cons_elem in H.
      destruct H.
      destruct H. hnf in H. subst a0.
      rewrite H3 in H2. inversion H2. subst.
      apply cons_elem; auto.
      apply cons_elem. right. apply H1.
      exists n. exists a'. intuition.
      apply H1.
      destruct H as [n [a' [?[??]]]].
      apply cons_elem in H. destruct H.
      destruct H. hnf in H. subst a0.
      rewrite H3 in H2. discriminate.
      exists n. exists a'. intuition.
    Qed.


    Record reindex :=
      Reindex
      { idx : I
      ; natset : finset N
      ; natset_ok : forall m, 
           m ∈ natset ->
           eff_enum _ (effective (ds_F I DS idx)) m <> None
      ; natset_inh : inh hf natset
      ; reindex_mubclos : 
            mub_closed hf 
              (ord (ds_F I DS idx)) 
              (clip_set _ natset (eff_enum _ (effective (ds_F I DS idx))))
      }.

    Lemma mub_clos_normal (A:preord) hf 
      (Heff:effective_order A)
      (Hplt:plotkin_order hf A) X 
      (Hinh:inh hf X) :
      normal_set A Heff hf (mub_closure Hplt X).
    Proof.
      hnf; intros. split; auto.
      destruct hf; auto.
      destruct Hinh.
      exists x. apply mub_clos_incl. auto.
      repeat intro.
      destruct (mub_complete Hplt M z) as [z' [??]]; auto.
      hnf; intros.
      apply H in H0.
      apply finsubset_elem in H0. destruct H0; auto.
      intros. rewrite <- H1; auto.
      exists z'; split; auto.
      destruct H0; auto.
      apply finsubset_elem. intros. rewrite <- H2; auto.
      split; auto.
      apply (mub_clos_mub Hplt X) with M; auto.
      hnf; intros.
      apply H in H2.
      apply finsubset_elem in H2. destruct H2; auto.
      intros. rewrite <- H3. auto.
    Qed.

    Lemma reindex_properties_dec (i:I) (X:finset N) :
      {  (forall m, m ∈ X -> eff_enum _ (effective (ds_F I DS i)) m <> None)
      /\ inh hf X
      /\ mub_closed hf 
              (ord (ds_F I DS i)) 
              (clip_set _ X (eff_enum _ (effective (ds_F I DS i))))
      } + {
       ~( (forall m, m ∈ X -> eff_enum _ (effective (ds_F I DS i)) m <> None)
      /\ inh hf X
      /\ mub_closed hf 
              (ord (ds_F I DS i)) 
              (clip_set _ X (eff_enum _ (effective (ds_F I DS i)))))
      }.
    Proof.
      destruct (finset_find_dec N (fun m => 
        eff_enum (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
         (effective (ds_F I DS i)) m = None)) with X.
      intros. destruct H. hnf in H. subst y. auto.
      intro m.
      case_eq (eff_enum (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
         (effective (ds_F I DS i)) m). intros.
      right. discriminate.
      intros. left. auto.
      destruct s as [z [??]].
      right. intros [?[??]]. apply (H1 z); auto.
      destruct (inh_dec _ hf X).
      assert (Hclip: inh hf
        (clip_set (ds_F I DS i) X
          (eff_enum (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
            (effective (ds_F I DS i))))).
      destruct hf; simpl; auto.
      destruct i0 as [x ?].
      generalize H; intros.
      apply n in H.      
      case_eq (eff_enum (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
        (effective (ds_F I DS i)) x).
      intros.
      exists c.
      apply clip_set_elem.
      exists x. exists c. intuition.
      intros. rewrite H1 in H. elim H; auto.

      destruct (normal_sub_mub_closed_dec 
         (ord (ds_F I DS i))
         (effective (ds_F I DS i))
         hf
         (mub_closure (plotkin (ds_F I DS i)) 
             (clip_set (ds_F I DS i) X
               (eff_enum (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
                 (effective (ds_F I DS i)))))
         ) with
      (clip_set (ds_F I DS i) X
               (eff_enum (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
                 (effective (ds_F I DS i)))); auto.
      apply mub_clos_normal; auto.
      hnf. intros. apply mub_clos_incl. auto.

      right. intros [?[??]]. elim n0; auto.
      right. intros [?[??]]. auto.
    Qed.

    Definition embed_func' (i j:I) (Hij : i ≤ j) :=
      embed_func (ds_F I DS i) (ds_F I DS j) 
         (embed (ds_hom I DS i j Hij))
         (project (ds_hom I DS i j Hij))
         (ep_correct _ _ (ds_hom I DS i j Hij)).

    Definition reindex_ord (x y:reindex) :=
      exists (Hxy : idx x ≤ idx y),
        forall m, m ∈ natset x -> exists n, n ∈ natset y /\
            exists a b,
              eff_enum _ (effective (ds_F I DS (idx x))) m = Some a /\
              eff_enum _ (effective (ds_F I DS (idx y))) n = Some b /\
              embed_func' _ _ Hxy#a ≈ b.

    Lemma reindex_ord_refl (x:reindex) : reindex_ord x x.
    Proof.
      hnf. exists (ord_refl _ _).
      intros. exists m. split; auto.
      generalize (natset_ok x m).
      destruct (eff_enum _ (effective (ds_F I DS (idx x))) m).
      intros. exists c. exists c. intuition.
      simpl. unfold choose'.
      match goal with [ |- appcontext[find_inhabitant' ?A ?X ?Y] ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      unfold embed_image in m0.
      apply esubset_elem in m0.
      intuition.
      split.
      generalize (ds_ident I DS (idx x) (ord_refl _ _)).
      intros [??].
      apply H2 in H3. simpl in H3.
      apply ident_elem in H3. auto.
      generalize (ds_ident' I DS (idx x) (ord_refl _ _)).
      intros. destruct H2.
      apply H2 in H4. simpl in H4.
      apply ident_elem in H4. auto.

      intro. elim H0. auto.
      auto.
    Qed.

    Lemma reindex_ord_trans (x y z:reindex) : 
      reindex_ord x y -> reindex_ord y z -> reindex_ord x z.
    Proof.
      unfold reindex_ord. intros.
      destruct H as [Hxy Hxy'].
      destruct H0 as [Hyz Hyz'].
      assert (Hxz : idx x ≤ idx z).
      transitivity (idx y); auto.
      exists Hxz.
      intros.
      destruct (Hxy' m) as [m' [??]]; auto.
      destruct (Hyz' m') as [m'' [??]]; auto.
      exists m''. split; auto.
      destruct H1 as [a [b [?[??]]]].
      destruct H3 as [b' [c [?[??]]]].
      assert( b=b' ) by congruence. subst b'. clear H3.
      exists a. exists c. intuition.
      clear Hxy' Hyz'. simpl in *.
      unfold choose' in *.
      match goal with [ |- appcontext[find_inhabitant' ?A ?X ?Y] ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      match goal with [ _ : appcontext[find_inhabitant' ?A ?X ?Y] |- _ ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      match goal with [ _ : appcontext[find_inhabitant' ?A ?X ?Y] |- _ ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      unfold embed_image in *.
      rewrite esubset_elem in m0.
      rewrite esubset_elem in m1.
      rewrite esubset_elem in m2.
      intuition.
      rewrite <- H7.
      split.
      cut ((x1,x0) ∈ hom_rel id).
      simpl; intros. apply ident_elem in H12. auto.
      generalize (ep_correct _ _ (ds_hom I DS _ _ Hxz)).
      intros [??]. apply ep_ident0. clear pe_ident0 ep_ident0.
      simpl. apply compose_elem. apply hom_order.
      exists a. split; auto.
      generalize (ds_compose' I DS _ _ _ Hxy Hyz Hxz).
      intros [??]. apply H12. clear H12 H17.
      simpl. apply compose_elem. apply hom_order.
      exists b. split; auto.
      apply hom_order with x2 a; auto.
      cut ((x0,x1) ∈ hom_rel id).
      simpl; intros. apply ident_elem in H12. auto.
      generalize (ep_correct _ _ (ds_hom I DS _ _ Hxz)).
      intros [??]. apply ep_ident0. clear pe_ident0 ep_ident0.
      simpl. apply compose_elem. apply hom_order.
      exists a. split; auto.
      generalize (ds_compose I DS _ _ _ Hxy Hyz Hxz).
      intros [??]. apply H12. clear H12 H17.
      simpl. apply compose_elem. apply hom_order.
      exists x2. split; auto.
      apply hom_order with b x1; auto.
    Qed.
    
    Definition reindex_ord_mixin : Preord.mixin_of reindex :=
      Preord.Mixin reindex reindex_ord reindex_ord_refl reindex_ord_trans.

    Canonical Structure reindex' : preord := 
      Preord.Pack reindex reindex_ord_mixin.

    Lemma reindex_dec (x y:reindex) : { x ≤ y } + { x ≰ y }.
    Proof.
      destruct (eff_ord_dec _ (ds_eff I DS) (idx x) (idx y)).
      destruct  (finset_find_dec' N
        (fun m => exists n, n ∈ natset y /\
            exists a b,
              eff_enum _ (effective (ds_F I DS (idx x))) m = Some a /\
              eff_enum _ (effective (ds_F I DS (idx y))) n = Some b /\
              embed_func' _ _ o#a ≈ b)) with (natset x).
      intros. destruct H. hnf in H. subst y0; auto.
      intro m.
      destruct  (finset_find_dec N
        (fun n =>
            exists a b,
              eff_enum _ (effective (ds_F I DS (idx x))) m = Some a /\
              eff_enum _ (effective (ds_F I DS (idx y))) n = Some b /\
              embed_func' _ _ o#a ≈ b)) with (natset y).
      intros. destruct H. hnf in H. subst y0; auto.
      intros n.
      case_eq (eff_enum _ (effective (ds_F I DS (idx x))) m). intros a Ha.
      case_eq (eff_enum _ (effective (ds_F I DS (idx y))) n). intros b Hb.
      destruct (PREORD_EQ_DEC _ (dec (ds_F I DS (idx y)))
        (embed_func' _ _ o#a) b).
      left. exists a. exists b. intuition.
      right.
      intros [a' [b' [?[??]]]].
      apply n0.
      inversion H. inversion H0. auto.
      intros. right. intros [a' [b' [?[??]]]]. discriminate.
      intros. right. intros [a' [b' [?[??]]]]. discriminate.
      destruct s as [z [??]].
      left; eauto.
      right. intros [q [??]].
      apply (n q); auto.
      destruct s as [z [??]].
      right; intro.
      apply H0; clear H0.
      destruct H1.
      destruct (H0 z) as [z' [??]]; auto.
      exists z'; split; auto.
      destruct H2 as [a [b [?[??]]]].
      exists a. exists b.  split; auto. split; auto.
      clear -H4.
      simpl in *.
      unfold choose' in *.
      match goal with [ |- appcontext[find_inhabitant' ?A ?X ?Y] ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      match goal with [ _ : appcontext[find_inhabitant' ?A ?X ?Y] |- _ ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      unfold embed_image in *.
      rewrite esubset_elem in m0.
      rewrite esubset_elem in m.
      intuition.
      split.
      cut ((b,x1) ∈ hom_rel id).
      simpl; intros. apply ident_elem in H2; auto.
      generalize (ep_correct _ _ (ds_hom I DS _ _ o)).
      intros [??]. apply ep_ident0. clear pe_ident0 ep_ident0.
      simpl. apply compose_elem. apply hom_order.
      exists a; split; auto.
      generalize (ds_compose' I DS (idx x) (idx x) (idx y) (ord_refl _ _) x0 o).
      intros [? _]. apply H2; clear H2.
      simpl. apply compose_elem. apply hom_order.
      exists a. split.
      apply hom_order with x2 a; auto.
      destruct (ds_ident' I DS (idx x) (ord_refl _ _)). apply H7.
      simpl. apply ident_elem. auto.
      cut ((x1,b) ∈ hom_rel id).
      simpl; intros. apply ident_elem in H2; auto.
      generalize (ep_correct _ _ (ds_hom I DS _ _ o)).
      intros [??]. apply ep_ident0. clear pe_ident0 ep_ident0.
      simpl. apply compose_elem. apply hom_order.
      exists a; split; auto.
      generalize (ds_compose I DS (idx x) (idx x) (idx y) (ord_refl _ _) x0 o).
      intros [? _]. apply H2; clear H2.
      simpl. apply compose_elem. apply hom_order.
      exists a. split.
      destruct (ds_ident I DS (idx x) (ord_refl _ _)). apply H7.
      simpl. apply ident_elem. auto.
      apply hom_order with a x2; auto.

      left. exists o. auto.
      right. intros [??]. elim n; auto.
    Qed.
      
    Lemma reindex_ext1 : forall (x y:reindex'),
      idx x = idx y ->
      natset x ≈ natset y ->
      x ≤ y.
    Proof.
      repeat intro.
      hnf. rewrite H.
      exists (ord_refl I (idx y)).
      intros. exists m. split.
      rewrite <- H0; auto.
      generalize (natset_ok x m H1).
      rewrite H.
      destruct (eff_enum _ (effective (ds_F I DS (idx y))) m).
      intros. exists c. exists c. intuition.
      simpl. unfold choose'.
      match goal with [ |- appcontext[find_inhabitant' ?A ?X ?Y] ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      unfold embed_image in m0.
      apply esubset_elem in m0.
      intuition.
      generalize (ds_ident I DS (idx y) (ord_refl _ _)).
      intros. destruct H4. apply H4 in H5.
      simpl in H5. clear H4 H7.
      generalize (ds_ident' I DS (idx y) (ord_refl _ _)).
      intros. destruct H4. apply H4 in H6. simpl in H6. clear H4 H7.
      apply ident_elem in H5. apply ident_elem in H6.
      split; auto.
      intros. elim H2; auto.
    Qed.

    Lemma reindex_ext : forall (x y:reindex'),
      idx x = idx y ->
      natset x ≈ natset y ->
      x ≈ y.
    Proof.
      intros. split; apply reindex_ext1; auto.
    Qed.

    Definition enum_reindex : eset reindex' :=
      fun n => 
        match eprod (eff_enum _ (ds_eff I DS))
                    (finsubsets _ (eff_enum _ effective_Nord)) n with
        | Some (i,X) =>
             match reindex_properties_dec i X with
             | left H => Some (Reindex i X (proj1 H) (proj1 (proj2 H)) (proj2 (proj2 H)))
             | right _ => None
             end
        | None => None
        end.

    Lemma push_natset (i j:I) (Hij:i≤j) (X:finset N) :
      (forall m, m ∈ X -> eff_enum _ (effective (ds_F I DS i)) m <> None) ->
      exists Y:finset N,
        (forall m, m ∈ Y -> eff_enum _ (effective (ds_F I DS j)) m <> None) /\
           (inh hf X -> inh hf Y) /\
           (image (embed_func' i j Hij) 
              (clip_set _ X (eff_enum _ (effective (ds_F I DS i)))) 
              : finset (ord (ds_F I DS j)))
           ≈
              (clip_set _ Y (eff_enum _ (effective (ds_F I DS j)))).           
    Proof.
      induction X; simpl; intros.
      exists nil. simpl; intuition.
      apply nil_elem in H0. auto.
      destruct IHX as [Y [?[??]]].
      intros. apply H. apply cons_elem; auto.
      assert (eff_enum (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
        (effective (ds_F I DS i)) a <> None).
      apply H. apply cons_elem; auto.
      case_eq (eff_enum (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
         (effective (ds_F I DS i)) a).
      intros. 2: intros; rewrite H4 in H3; elim H3; auto.
      set (c' := embed_func' i j Hij#c).
      generalize (eff_complete _ (effective (ds_F I DS j)) c').
      intros [n' ?].
      case_eq (eff_enum (cls_ord (ds_F I DS j) (class (ds_F I DS j)))
           (effective (ds_F I DS j)) n'); intros.
      2: rewrite H6 in H5; elim H5.
      rewrite H6 in H5.
      exists (n'::Y)%list.
      split; intros.
      apply cons_elem in H7. destruct H7.
      destruct H7. hnf in H7. subst n'.
      rewrite H6. discriminate.
      apply H0. auto.
      split.
      destruct hf; simpl; auto.
      exists n'. apply cons_elem; auto.
      split. hnf; intros.
Opaque embed_func'.
      simpl in H7.
      apply cons_elem in H7.
      destruct H7.
      apply clip_set_elem.
      exists n'. exists c0.
      split. apply cons_elem; auto.
      split. auto.
      rewrite H7.
      rewrite <- H5. auto.
      rewrite H2 in H7.
      apply clip_set_elem in H7.
      destruct H7 as [q [a' [?[??]]]].
      apply clip_set_elem.
      exists q. exists a'. split; auto.
      apply cons_elem; auto.
      hnf; intros.
      apply clip_set_elem in H7.
      destruct H7 as [q [a' [?[??]]]].
      apply cons_elem in H7. destruct H7.
      destruct H7. hnf in H7. subst n'. clear H10.
      simpl finset.fimage.
      apply cons_elem. left.
      assert (a' = c0) by congruence. subst c0.
      rewrite H9. rewrite <- H5. auto.
      simpl finset.fimage.
      apply cons_elem. right.
      rewrite H2.
      apply clip_set_elem.
      exists q. exists a'.
      split; auto.
    Qed.
Transparent embed_func'.
      
(* FIXME: move *)
Lemma finset_sub_image (A B:preord) (T:set.theory) 
  (f:A → B) (X:set T A) (M:finset B) :
  M ⊆ image f X ->
  exists M', M ≈ image f M' /\ M' ⊆ X.
Proof.
  induction M; intros.
  exists nil. split; simpl; auto.
  hnf; simpl; intros. apply nil_elem in H0. elim H0.
  destruct IHM as [M' [??]].
  hnf; intros. apply H. apply cons_elem; auto.
  assert (a ∈ image f X). apply H. apply cons_elem. auto.
  apply image_axiom2 in H2.
  destruct H2 as [y [??]].
  exists (y::M')%list.
  split.
  split. hnf. simpl. intros.
  apply cons_elem in H4. destruct H4.
  apply cons_elem. left.
  rewrite H4; auto.
  apply cons_elem. right.
  rewrite H0 in H4. auto.
  hnf. simpl; intros.
  apply cons_elem in H4.
  apply cons_elem.
  destruct H4.
  left. rewrite H4; auto.
  right. rewrite H0. auto.
  hnf; simpl; intros.
  apply cons_elem in H4.
  destruct H4.
  rewrite H4; auto.
  apply H1; auto.
Qed.
  

    Lemma reindex_sideways (x:reindex') (j:I) (Hxj : idx x ≈ j) :
      exists y: reindex', idx y = j /\ x ≈ y.
    Proof.
      destruct Hxj.
      destruct (push_natset (idx x) j H (natset x)) as [Y [?[??]]].
      apply natset_ok.
      assert (Hmc :
            mub_closed hf 
              (ord (ds_F I DS j)) 
              (clip_set _ Y (eff_enum _ (effective (ds_F I DS j))))).

      hnf. intros.
      rewrite <- H3 in H5.
      generalize H5; intro.
      apply finset_sub_image in H5.
      destruct H5 as [M' [??]].
      assert (HinhM' : inh hf M').
      destruct hf; simpl; auto.
      destruct H4.
      rewrite H5 in H4.
      apply image_axiom2 in H4.
      destruct H4 as [y [??]]. exists y. auto.
      set (q := embed_func' j (idx x) H0#x0).

      assert (Hembed : forall z:ord (ds_F I DS j),
        embed_func' (idx x) j H#(embed_func' j (idx x) H0#z) ≈ z).
      clear.
      simpl.
      intro z.
      unfold choose' at 1.
      match goal with [ |- appcontext[find_inhabitant' ?A ?X ?Y] ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      unfold embed_image in m.
      apply esubset_elem in m.
      destruct m as [?[??]].
      simpl in *.
      unfold choose' in *.
      match goal with [ _ : appcontext[find_inhabitant' ?A ?X ?Y] |- _ ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      rewrite esubset_elem in m.
      intuition.
      split.
      cut ((z,x0) ∈ hom_rel id).
      simpl; intros. apply ident_elem in H5. auto.
      destruct (ds_ident I DS j (ord_refl _ _)).
      apply H5. clear H5 H8.
      destruct (ds_compose I DS j (idx x) j H0 H (ord_refl _ _)).
      apply H5; clear H5 H8.
      simpl. apply compose_elem; eauto. apply hom_order.
      cut ((x0,z) ∈ hom_rel id).
      simpl; intros. apply ident_elem in H5. auto.
      destruct (ds_ident' I DS j (ord_refl _ _)).
      apply H5. clear H5 H8.
      destruct (ds_compose' I DS j (idx x) j H0 H (ord_refl _ _)).
      apply H5; clear H5 H8.
      simpl. apply compose_elem; eauto. apply hom_order.
      
      assert (Hq : minimal_upper_bound q M').
      split.
      hnf; intros.
      unfold q.
      apply embed_func_reflects with (ds_F I DS j)
                 (embed (ds_hom I DS (idx x) j H))
                 (project (ds_hom I DS (idx x) j H))
                 (ep_correct _ _ (ds_hom I DS (idx x) j H)).
      rewrite (Hembed x0).
      apply H6.
      rewrite H5.
      apply image_axiom1. auto.

      intros.
      unfold q.
      apply embed_func_reflects with (ds_F I DS j)
                 (embed (ds_hom I DS (idx x) j H))
                 (project (ds_hom I DS (idx x) j H))
                 (ep_correct _ _ (ds_hom I DS (idx x) j H)).
      rewrite (Hembed x0).
      destruct H6.
      apply H11.
      hnf; intros.
      rewrite H5 in H12.
      apply image_axiom2 in H12.
      destruct H12 as [y [??]].
      rewrite H13.
      apply Preord.axiom.
      apply H9. auto.
      rewrite <- (Hembed x0).
      apply Preord.axiom. auto.
      
      generalize (reindex_mubclos x M' HinhM' H8 q Hq).
      intros.
      rewrite <- H3.
      unfold q in H9.
      rewrite <- (Hembed x0).
      apply image_axiom1. auto.

      exists (Reindex j Y H1 (H2 (natset_inh x)) Hmc).
      split. simpl. auto.
      split. hnf; simpl.
      exists H.
      intros.
      generalize (natset_ok x m H4).
      case_eq (eff_enum _ (effective (ds_F I DS (idx x))) m); intros.
      assert (embed_func' (idx x) j H # c ∈ 
        image (embed_func' (idx x) j H)
         (clip_set (ds_F I DS (idx x)) (natset x)
            (eff_enum
               (cls_ord (ds_F I DS (idx x)) (class (ds_F I DS (idx x))))
               (effective (ds_F I DS (idx x)))))).
      apply image_axiom1.
      apply clip_set_elem. exists m. exists c. split; auto.
      rewrite H3 in H7.
      apply clip_set_elem in H7.
      destruct H7 as [q [a' [?[??]]]].
      exists q. split; auto.
      exists c. exists a'. intuition.
      elim H6; auto.
     
      exists H0. simpl.
      intros.
      
      generalize (H1 m H4).
      case_eq (eff_enum _ (effective (ds_F I DS j)) m); intros.
      assert (c ∈ clip_set (ds_F I DS j) Y
           (eff_enum (cls_ord (ds_F I DS j) (class (ds_F I DS j)))
              (effective (ds_F I DS j)))).
      apply clip_set_elem.
      exists m. exists c. split; auto.
      rewrite <- H3 in H7.
      apply image_axiom2 in H7.
      destruct H7 as [y [??]].
      apply clip_set_elem in H7.
      destruct H7 as [q [a' [?[??]]]].
      exists q. split; auto.
      exists c. exists a'.
      intuition.
      rewrite H10 in H8.
      clear -H8.
      simpl in H8.
      unfold choose' in *.
      match goal with [ _ : appcontext[find_inhabitant' ?A ?X ?Y] |- _ ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      match goal with [ |- appcontext[find_inhabitant' ?A ?X ?Y] ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      unfold embed_image in *.
      rewrite esubset_elem in m.
      rewrite esubset_elem in m0.
      intuition.
      split.
      cut ((a',x1) ∈ hom_rel id).
      simpl; intros. apply ident_elem in H4. auto.
      destruct (ds_ident I DS (idx x) (ord_refl _ _)).
      apply H4. clear H4 H9.
      destruct (ds_compose I DS (idx x) j (idx x) H H0 (ord_refl _ _)).
      apply H4. clear H4 H9.
      simpl. apply compose_elem. apply hom_order.
      exists x0. split; auto.
      apply hom_order with c x1; auto.
      cut ((x1,a') ∈ hom_rel id).
      simpl; intros. apply ident_elem in H4. auto.
      destruct (ds_ident' I DS (idx x) (ord_refl _ _)).
      apply H4. clear H4 H9.
      destruct (ds_compose' I DS (idx x) j (idx x) H H0 (ord_refl _ _)).
      apply H4. clear H4 H9.
      simpl. apply compose_elem. apply hom_order.
      exists x0. split; auto.
      apply hom_order with x1 c; auto.
      elim H6; auto.
    Qed.

    Program Definition reindex_effective : effective_order reindex' 
      := EffectiveOrder reindex' reindex_dec enum_reindex _.
    Next Obligation.
      intros. unfold enum_reindex.
      assert ((idx x) ∈ eff_enum I (ds_eff I DS)).
      apply eff_complete.
      destruct H as [n ?].
      unfold eprod.
      case_eq (eff_enum I (ds_eff I DS) n); intros.
      rewrite H0 in H.
      2: rewrite H0 in H. 2: elim H.
      destruct (reindex_sideways x c H) as [y [??]].
      assert (natset y ∈ finsubsets N (eff_enum N effective_Nord)).
      apply finsubsets_complete. hnf; intros. apply eff_complete.
      destruct H3 as [m ?].
      case_eq (finsubsets N (eff_enum N effective_Nord) m); intros.
      rewrite H4 in H3.
      2: rewrite H4 in H3; elim H3.
      exists (pairing.pairing (n,m)).
      rewrite pairing.unpairing_pairing.
      rewrite H0. rewrite H4.
      destruct (reindex_properties_dec c c0).
      rewrite H2.
      apply reindex_ext; simpl; auto.

      apply n0; clear n0.
      split. intros.
      rewrite <- H3 in H5.
      rewrite <- H1.
      apply (natset_ok y m0); auto.
      split.
      generalize (natset_inh y).
      destruct hf; simpl; intros.
      destruct H5 as [q ?]. exists q.
      rewrite <- H3; auto. auto.
      rewrite <- H1.
      hnf; intros.
      assert (x0
       ∈ clip_set (ds_F I DS (idx y)) (natset y)
           (eff_enum
              (cls_ord (ds_F I DS (idx y)) (class (ds_F I DS (idx y))))
              (effective (ds_F I DS (idx y))))).
      apply (reindex_mubclos y M H5); auto.
      hnf; intros.
      apply H6 in H8.
      apply clip_set_elem in H8.
      apply clip_set_elem.
      destruct H8 as [q [a' [?[??]]]].
      exists q. exists a'. intuition.
      rewrite H3; auto.
      apply clip_set_elem in H8.
      apply clip_set_elem.
      destruct H8 as [q [a' [?[??]]]].
      exists q. exists a'. intuition.
      rewrite <- H3; auto.
    Qed.

    Lemma build_natset (A:ob) (X:finset (ord A)) :
      exists Y:finset N,
        (forall m, 
           m ∈ Y ->
           eff_enum _ (effective A) m <> None) /\
        X ≈ clip_set A Y (eff_enum _ (effective A)).
    Proof.
      induction X. exists nil. simpl. auto.
      split; auto. intros. apply nil_elem in H. elim H.
      destruct IHX as [Y [Hm ?]].
      generalize (eff_complete _ (effective A) a).
      intros [n ?].
      exists (n :: Y)%list.
      split; hnf; intros.
      apply cons_elem in H1.
      destruct H1.
      destruct H1. hnf in H1. subst.
      destruct (eff_enum _ (effective A) n) ; auto.
      discriminate.
      apply Hm. auto.

      split; hnf; intros.
      apply cons_elem in H1. destruct H1.
      apply clip_set_elem.
      case_eq (eff_enum _ (effective A) n); intros.
      rewrite H2 in H0.
      exists n. exists c. split; auto.
      apply cons_elem; auto. split; auto.
      rewrite H1; auto.
      rewrite H2 in H0. elim H0.
      rewrite H in H1.
      apply clip_set_elem in H1.
      destruct H1 as [m [a' [?[??]]]].
      apply clip_set_elem. exists m. exists a'. intuition.
      apply cons_elem; auto.
      apply clip_set_elem in H1.
      destruct H1 as [m [a' [?[??]]]].
      apply cons_elem in H1. destruct H1.
      rewrite H3.      
      destruct H1. hnf in H1. subst m.
      rewrite H2 in H0.
      apply cons_elem; auto.
      apply cons_elem. right.
      rewrite H.
      apply clip_set_elem.
      exists m. exists a'. intuition.
    Qed.

    Lemma reindex_directed : directed hf (eff_enum reindex' reindex_effective).
    Proof.
      apply prove_directed.

      case_eq hf; auto. intros.
      destruct (ds_dir I DS nil) as [i [??]].
      rewrite H. hnf; auto.
      hnf; intros. apply nil_elem in H0. elim H0.
      set (X := mub_closure (plotkin (ds_F I DS i)) nil).
      destruct (build_natset (ds_F I DS i) X) as [Y [??]].
      assert (inh hf Y).
      rewrite H. hnf; auto.
      assert (
            mub_closed hf 
              (ord (ds_F I DS i)) 
              (clip_set _ Y (eff_enum _ (effective (ds_F I DS i))))).
      hnf. intros. rewrite <- H3 in H6.
      rewrite <- H3.
      unfold X.
      apply (mub_clos_mub) with M; auto.
      rewrite H. hnf; auto.
      exists (Reindex i Y H2 H4 H5).      
      apply eff_complete.

      intros. clear H H0.
      destruct (ds_dir I DS ((idx x)::(idx y)::nil)%list) as [k [??]].
      destruct hf; hnf; auto.
      exists (idx x). apply cons_elem; auto.
      hnf; intros. apply eff_complete.
      assert (Hxk : idx x ≤ k).      
      apply H. apply cons_elem. auto.
      assert (Hyk : idx y ≤ k).
      apply H. apply cons_elem. right. apply cons_elem; auto.
      
      set (X := image (embed_func' (idx x) k Hxk)
        (clip_set _ (natset x) (eff_enum _ (effective (ds_F I DS (idx x)))))).
      set (Y := image (embed_func' (idx y) k Hyk)
        (clip_set _ (natset y) (eff_enum _ (effective (ds_F I DS (idx y)))))).
      set (Z := mub_closure (plotkin (ds_F I DS k)) (X++Y)%list).
      destruct (build_natset (ds_F I DS k) Z) as [Z' [??]].
      assert (inh hf Z').
      case_eq hf; hnf; simpl; intros; auto.
      generalize (natset_inh x).
      rewrite H3. intros [q ?].
      generalize (natset_ok x q H4).
      case_eq (eff_enum _ (effective (ds_F I DS (idx x))) q); intros.
      assert (embed_func' (idx x) k Hxk#c ∈ Z).
      unfold Z.
      apply mub_clos_incl.
      apply app_elem. left.
      unfold X.
      apply image_axiom1.
      apply clip_set_elem.
      exists q. exists c. auto.
      rewrite H2 in H7.
      apply clip_set_elem in H7.
      destruct H7 as [m [a' [?[??]]]].
      exists m. auto.
      elim H6; auto.

      assert (mub_closed hf _
         (clip_set (ds_F I DS k) Z'
           (eff_enum (cls_ord (ds_F I DS k) (class (ds_F I DS k)))
              (effective (ds_F I DS k))))).
      hnf. intros.
      rewrite <- H2 in H5.
      rewrite <- H2.
      apply (mub_clos_mub (plotkin (ds_F I DS k))) with M; auto.
      case_eq hf; hnf; simpl; intros; auto.
      generalize (natset_inh x).
      rewrite H7. intros [q ?].
      generalize (natset_ok x q H8).
      case_eq (eff_enum _ (effective (ds_F I DS (idx x))) q); intros.
      exists (embed_func' (idx x) k Hxk#c).
      apply app_elem. left.
      unfold X. apply image_axiom1.
      apply clip_set_elem.
      exists q. exists c. auto.
      elim H10; auto.
      
      exists (Reindex k Z' H1 H3 H4).
      split.
      exists Hxk. simpl.
      intros.
      generalize (natset_ok x m H5).
      case_eq (eff_enum _ (effective (ds_F I DS (idx x))) m); intros.
      assert (embed_func' (idx x) k Hxk#c ∈ Z).
      unfold Z. apply mub_clos_incl.
      apply app_elem. left.
      unfold X. apply image_axiom1.
      apply clip_set_elem.
      exists m. exists c. auto.
      rewrite H2 in H8.
      apply clip_set_elem in H8.
      destruct H8 as [n [a' [?[??]]]].
      exists n. split; auto.
      exists c. exists a'. split; auto.
      elim H7; auto.

      split.
      exists Hyk. simpl; intros.
      generalize (natset_ok y m H5).
      case_eq (eff_enum _ (effective (ds_F I DS (idx y))) m); intros.
      assert (embed_func' (idx y) k Hyk#c ∈ Z).
      unfold Z. apply mub_clos_incl.
      apply app_elem. right.
      unfold Y. apply image_axiom1.
      apply clip_set_elem.
      exists m. exists c. auto.
      rewrite H2 in H8.
      apply clip_set_elem in H8.
      destruct H8 as [n [a' [?[??]]]].
      exists n. split; auto.
      exists c. exists a'. split; auto.
      elim H7; auto.
      
      apply eff_complete.
    Qed.

    Definition choose_fin_rows (x:reindex) (q:N2) :=
           match
             eff_enum _ (effective (ds_F I DS (idx x))) (fst q),
             eff_enum _ (effective (ds_F I DS (idx x))) (snd q) with
           | Some a, Some b => a ≤ b
           | _, _ => False
           end.

    Program Definition reindex_finord_G (x:reindex) : finset N2 := 
      finsubset N2
         (choose_fin_rows x)
         _
         (finprod (natset x) (natset x)).
    Next Obligation.
      intros x [n m].
      case_eq (eff_enum _ (effective (ds_F I DS (idx x))) n). intros a Ha.
      case_eq (eff_enum _ (effective (ds_F I DS (idx x))) m). intros b Hb.
      destruct (eff_ord_dec _ (effective (ds_F I DS (idx x))) a b).
      left. hnf; simpl.
      rewrite Ha. rewrite Hb. auto.
      right; intro.
      hnf in H; simpl in H.
      rewrite Ha in H. rewrite Hb in H. contradiction.
      intros. right; intro.
      hnf in H0; simpl in H0.
      rewrite Ha in H0.
      rewrite H in H0. auto.
      intros. right; intro.
      hnf in H0; simpl in H0.
      rewrite H in H0. auto.
    Qed.

    Lemma reindex_finord_elem (x:reindex) n m :
      (n,m) ∈ reindex_finord_G x 
      <-> n ∈ natset x /\ m ∈ natset x /\
        exists a b,
             eff_enum _ (effective (ds_F I DS (idx x))) n = Some a /\
             eff_enum _ (effective (ds_F I DS (idx x))) m = Some b /\
             a ≤ b.
    Proof.
      split; intros.
      unfold reindex_finord_G in H.
      rewrite finsubset_elem in H.
      destruct H.
      apply finprod_elem in H. destruct H.
      split; auto.
      split; auto.
      hnf in H0. simpl in H0.
      destruct (eff_enum _ (effective (ds_F I DS (idx x))) n).
      destruct (eff_enum _ (effective (ds_F I DS (idx x))) m).
      exists c. exists c0. split; auto.
      elim H0. elim H0.
      intros. hnf in H0. destruct H0.
      destruct H0. hnf in H0. hnf in H3.
      destruct x0; destruct y; simpl in *. subst; auto.
      
      destruct H as [?[??]].
      destruct H1 as [a [b [?[??]]]].
      unfold reindex_finord_G.
      rewrite finsubset_elem.
      split.
      apply finprod_elem; auto.
      hnf; simpl.
      rewrite H1. rewrite H2. auto.
      clear.
      intros. hnf in H. destruct H.
      destruct H. hnf in H. hnf in H2.
      destruct x0; destruct y; simpl in *. subst; auto.
    Qed.

    Lemma reindex_is_finord (x:reindex) : preord_graph hf (reindex_finord_G x).
    Proof.
      split; intros.
      rewrite reindex_finord_elem in H.
      rewrite reindex_finord_elem.
      intuition.
      destruct H2 as [a [b [?[??]]]].
      exists a. exists a. intuition.
      split; intros.
      rewrite reindex_finord_elem in H.
      rewrite reindex_finord_elem.
      intuition.
      destruct H2 as [a [b [?[??]]]].
      exists b. exists b. intuition.
      split; intros.
      rewrite reindex_finord_elem in H.
      rewrite reindex_finord_elem in H0.
      rewrite reindex_finord_elem.
      intuition.
      destruct H4 as [a [b [?[??]]]].
      destruct H5 as [b' [c [?[??]]]].      
      exists a. exists c. intuition.
      transitivity b; auto.
      replace b with b'; auto.
      congruence.
      
      case_eq hf; auto.
      intros.
      generalize (natset_inh x). 
      unfold inh. intros.
      rewrite H in H0.
      destruct H0 as [n ?].
      exists n. exists n.
      rewrite reindex_finord_elem. intuition.
      generalize (natset_ok x n). 
      destruct (eff_enum _ (effective (ds_F I DS (idx x))) n).
      intros. exists c. exists c. intuition.
      intros. elim H1; auto.
    Qed.

    Definition reindex_finord (x:reindex) : finord hf :=
      exist _ (reindex_finord_G x) (reindex_is_finord x).

    Lemma reindex_out {x y:reindex} (H:reindex_ord x y) : idx x ≤ idx y.
    Proof.
      destruct H. auto.
    Defined.

    Definition choose_embed_rows (x:reindex) (y:reindex) (Hxy:reindex_ord x y) (q:N2) :=
           match
             eff_enum _ (effective (ds_F I DS (idx x))) (fst q),
             eff_enum _ (effective (ds_F I DS (idx y))) (snd q) with
           | Some a, Some b => embed_func' _ _ (reindex_out Hxy)#a ≥ b
           | _, _ => False
           end.

    Program Definition reindex_embed (x y:reindex) (Hxy:reindex_ord x y) : finset N2 := 
      finsubset N2
         (choose_embed_rows x y Hxy)
         _
         (finprod (natset x) (natset y)).
    Next Obligation.
      intros x y Hxy [n m].
      case_eq (eff_enum _ (effective (ds_F I DS (idx x))) n). intros a Ha.
      case_eq (eff_enum _ (effective (ds_F I DS (idx y))) m). intros b Hb.
      destruct (eff_ord_dec _ (effective (ds_F I DS (idx y)))
                     b (embed_func' _ _ (reindex_out Hxy)#a)).
      left. hnf; simpl.
      rewrite Ha. rewrite Hb. auto.
      right. repeat intro.
      hnf in H; simpl in H.
      rewrite Ha in H. rewrite Hb in H. elim n0; auto.
      intros. right; repeat intro.
      hnf in H0. simpl in H0.
      rewrite Ha in H0. rewrite H in H0. auto.
      intros. right; repeat intro.
      hnf in H0. simpl in H0.
      rewrite H in H0. auto.
    Qed.

    Definition choose_project_rows (x:reindex) (y:reindex) (Hxy:reindex_ord x y) (q:N2) :=
           match
             eff_enum _ (effective (ds_F I DS (idx x))) (snd q),
             eff_enum _ (effective (ds_F I DS (idx y))) (fst q) with
           | Some a, Some b => embed_func' _ _ (reindex_out Hxy)#a ≤ b
           | _, _ => False
           end.

    Program Definition reindex_project (x y:reindex) (Hxy:reindex_ord x y) : finset N2 := 
      finsubset N2
         (choose_project_rows x y Hxy)
         _
         (finprod (natset y) (natset x)).
    Next Obligation.
      intros x y Hxy [n m].
      case_eq (eff_enum _ (effective (ds_F I DS (idx x))) m). intros a Ha.
      case_eq (eff_enum _ (effective (ds_F I DS (idx y))) n). intros b Hb.
      destruct (eff_ord_dec _ (effective (ds_F I DS (idx y)))
                     (embed_func' _ _ (reindex_out Hxy)#a) b).
      left. hnf; simpl.
      rewrite Ha. rewrite Hb. auto.
      right; intro.
      hnf in H. simpl in H.
      rewrite Ha in H. rewrite Hb in H. elim n0; auto.
      intro; right; intro.
      hnf in H0; simpl in H0.
      rewrite Ha in H0. rewrite H in H0. auto.
      intro; right; intro.
      hnf in H0; simpl in H0.
      rewrite H in H0. auto.
    Qed.

    Lemma reindex_embed_elem x y (Hxy:reindex_ord x y) n m:
      (n,m) ∈ reindex_embed x y Hxy <-> 
         n ∈ natset x /\ m ∈ natset y /\
         exists a b,
             eff_enum _ (effective (ds_F I DS (idx x))) n = Some a /\
             eff_enum _ (effective (ds_F I DS (idx y))) m = Some b /\
             (a,b) ∈ hom_rel (embed (ds_hom I DS (idx x) (idx y) (reindex_out Hxy))).
    Proof.
      split; intros.
      unfold reindex_embed in H.
      rewrite finsubset_elem in H. destruct H.
      apply finprod_elem in H. intuition.
      unfold choose_embed_rows in H0.
      simpl fst in H0. simpl snd in H0.
      destruct (eff_enum _ (effective (ds_F I DS (idx x))) n).
      destruct (eff_enum _ (effective (ds_F I DS (idx y))) m).
      exists c. exists c0. split; auto. split; auto.
      unfold embed_func' in H0.
      unfold embed_func in H0. simpl in H0.
      unfold choose' in H0.
      match goal with [ H0 : appcontext[find_inhabitant' ?A ?X ?Y] |- _ ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      unfold embed_image in m0.
      rewrite esubset_elem in m0.
      destruct m0. destruct H3.
      apply hom_order with c x0; auto.      
      elim H0. elim H0.

      intros.
      destruct H0 as [[??][??]].      
      destruct x0; destruct y0; simpl in *.
      hnf in H0. hnf in H2. subst; auto.

      destruct H as [?[??]].
      destruct H1 as [a [b [?[??]]]].
      unfold reindex_embed.
      rewrite finsubset_elem.
      split. apply finprod_elem. split; auto.
      unfold choose_embed_rows.
      simpl fst. simpl snd.
      rewrite H1. rewrite H2.
      unfold embed_func'. unfold embed_func. simpl.
      unfold choose'.
      match goal with [ |- appcontext[find_inhabitant' ?A ?X ?Y]] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      unfold embed_image in m0.
      apply esubset_elem in m0.
      destruct m0 as [?[??]].
      generalize (ep_correct _ _ (ds_hom I DS _ _ (reindex_out Hxy))).
      intros [??].
      cut ((x0,b) ∈ hom_rel id). intros.
      simpl in H7. apply ident_elem in H7. auto.
      apply ep_ident0.
      simpl.
      rewrite compose_elem. 2: apply hom_order.
      exists a. split; auto.
      
      clear; intros.
      destruct H as [[??][??]].      
      destruct x0; destruct y0; simpl in *.
      hnf in H. hnf in H1. subst; auto.
    Qed.      

    Lemma reindex_project_elem x y (Hxy:reindex_ord x y) n m:
      (n,m) ∈ reindex_project x y Hxy <-> 
         n ∈ natset y /\ m ∈ natset x /\
         exists a b,
             eff_enum _ (effective (ds_F I DS (idx x))) m = Some a /\
             eff_enum _ (effective (ds_F I DS (idx y))) n = Some b /\
             (b,a) ∈ hom_rel (project (ds_hom I DS (idx x) (idx y) (reindex_out Hxy))).
    Proof.
      split; intros.
      unfold reindex_project in H.
      rewrite finsubset_elem in H. destruct H.
      apply finprod_elem in H. intuition.
      unfold choose_project_rows in H0.
      simpl fst in H0. simpl snd in H0.
      destruct (eff_enum _ (effective (ds_F I DS (idx x))) m).
      destruct (eff_enum _ (effective (ds_F I DS (idx y))) n).
      exists c. exists c0. split; auto. split; auto.
      unfold embed_func' in H0.
      unfold embed_func in H0. simpl in H0.
      unfold choose' in H0.
      match goal with [ H0 : appcontext[find_inhabitant' ?A ?X ?Y] |- _ ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      unfold embed_image in m0.
      rewrite esubset_elem in m0.
      destruct m0. destruct H3.
      apply hom_order with x0 c; auto.      
      elim H0. elim H0.

      intros.
      destruct H0 as [[??][??]].      
      destruct x0; destruct y0; simpl in *.
      hnf in H0. hnf in H2. subst; auto.

      destruct H as [?[??]].
      destruct H1 as [a [b [?[??]]]].
      unfold reindex_project.
      rewrite finsubset_elem.
      split. apply finprod_elem. split; auto.
      unfold choose_project_rows.
      simpl fst. simpl snd.
      rewrite H1. rewrite H2.
      unfold embed_func'. unfold embed_func. simpl.
      unfold choose'.
      match goal with [ |- appcontext[find_inhabitant' ?A ?X ?Y]] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      unfold embed_image in m0.
      apply esubset_elem in m0.
      destruct m0 as [?[??]].
      generalize (ep_correct _ _ (ds_hom I DS _ _ (reindex_out Hxy))).
      intros [??].
      cut ((b,x0) ∈ hom_rel id). intros.
      simpl in H7. apply ident_elem in H7. auto.
      apply ep_ident0.
      simpl.
      rewrite compose_elem. 2: apply hom_order.
      exists a. split; auto.
      
      clear; intros.
      destruct H as [[??][??]].      
      destruct x0; destruct y0; simpl in *.
      hnf in H. hnf in H1. subst; auto.
    Qed.      

    Lemma finapprox_embed x y (Hxy:reindex_ord x y) :
      finapprox_rel hf (reindex_finord_G x) (reindex_finord_G y) (reindex_embed x y Hxy).
    Proof.
      split; intros.
      apply reindex_embed_elem in H. destruct H as [?[??]].
      destruct H1 as [a [b [?[??]]]].
      split; apply reindex_finord_elem.
      intuition. exists a. exists a. intuition.
      intuition. exists b. exists b. intuition.

      split; intros.
      rewrite reindex_finord_elem in H.
      rewrite reindex_finord_elem in H0.
      intuition.
      destruct H5 as [a [b [?[??]]]].
      destruct H6 as [c [d [?[??]]]].
      rewrite reindex_embed_elem in H1.
      destruct H1 as [?[??]].
      destruct H11 as [p [q [?[??]]]].
      rewrite reindex_embed_elem.
      intuition.
      exists b. exists c. intuition.
      assert (a = p) by congruence. subst p.
      assert (d = q) by congruence. subst q.
      apply hom_order with a d; auto.
            
      split; intros.
      rewrite reindex_embed_elem in H.
      rewrite reindex_embed_elem in H0.
      intuition.
      destruct H4 as [a [b [?[??]]]].
      destruct H5 as [a' [b' [?[??]]]].
      assert (a = a') by congruence. subst a'. clear H5.
      destruct (hom_directed _ _ (embed (ds_hom I DS _ _ (reindex_out Hxy)))
        a (b::b'::nil)%list) as [q [??]].
      destruct hf; hnf; auto.
      exists b. apply cons_elem; auto.
      hnf; intros.
      rewrite erel_image_elem.
      apply cons_elem in H5. destruct H5.
      apply hom_order with a b; auto.
      apply cons_elem in H5. destruct H5.
      apply hom_order with a b'; auto.
      apply nil_elem in H5. elim H5.
      apply erel_image_elem in H9.
      destruct (mub_complete (plotkin (ds_F I DS (idx y)))
        (b::b'::nil)%list q) as [q' [??]]; auto.
      destruct hf; simpl; auto.
      exists b. apply cons_elem; auto.
      assert (q' ∈ 
          (clip_set _ (natset y) (eff_enum _ (effective (ds_F I DS (idx y)))))).
      apply (reindex_mubclos y) with (b::b'::nil)%list; auto.
      destruct hf; simpl; auto.
      exists b. apply cons_elem; auto.
      hnf; simpl; intros.
      apply cons_elem in H12. destruct H12. rewrite H12.
      apply clip_set_elem; eauto.
      apply cons_elem in H12. destruct H12. rewrite H12.
      apply clip_set_elem; eauto.
      apply nil_elem in H12. elim H12.
      apply clip_set_elem in H12.
      destruct H12 as [p [q'' [?[??]]]].
      exists p.
      split.
      apply reindex_finord_elem. intuition.
      exists b. exists q''. intuition.
      rewrite <- H14.
      destruct H10.
      apply H10.
      apply cons_elem; auto.
      split.
      apply reindex_finord_elem. intuition.
      exists b'. exists q''. intuition.
      rewrite <- H14.
      destruct H10.
      apply H10.
      apply cons_elem; right.
      apply cons_elem; auto.
      apply reindex_embed_elem. intuition.
      exists a. exists q''. intuition.
      apply hom_order with a q; auto.
      rewrite <- H14; auto.

      case_eq hf; auto. intros.
      apply reindex_finord_elem in H0.
      destruct H0 as [? [_ ?]].
      destruct H1 as [a [_ [? _]]].
      
      destruct (hom_directed _ _ (embed (ds_hom I DS _ _ (reindex_out Hxy)))
        a nil) as [q [??]].
      rewrite H. hnf. auto.
      hnf; simpl; intros. apply nil_elem in H2. elim H2.
      apply erel_image_elem in H3.
      destruct (mub_complete (plotkin (ds_F I DS (idx y)))
        nil q) as [q' [??]]; auto.
      rewrite H. hnf. auto.
      assert (q' ∈ 
          (clip_set _ (natset y) (eff_enum _ (effective (ds_F I DS (idx y)))))).
      apply (reindex_mubclos y) with nil; auto.
      rewrite H; hnf; auto.
      hnf; simpl; intros. apply nil_elem in H6. elim H6.
      apply clip_set_elem in H6.
      destruct H6 as [n [a' [?[??]]]].
      exists n.
      rewrite reindex_embed_elem.
      intuition.
      exists a. exists a'. intuition.
      apply hom_order with a q; auto.
      rewrite <- H8; auto.
    Qed.

    Lemma finapprox_project x y (Hxy:reindex_ord x y) :
      finapprox_rel hf (reindex_finord_G y) (reindex_finord_G x) 
           (reindex_project x y Hxy).
    Proof.
      split; intros.
      apply reindex_project_elem in H. destruct H as [?[??]].
      destruct H1 as [a [b [?[??]]]].
      split; apply reindex_finord_elem.
      intuition. exists b. exists b. intuition.
      intuition. exists a. exists a. intuition.

      split; intros.
      rewrite reindex_finord_elem in H.
      rewrite reindex_finord_elem in H0.
      intuition.
      destruct H5 as [a [b [?[??]]]].
      destruct H6 as [c [d [?[??]]]].
      rewrite reindex_project_elem in H1.
      destruct H1 as [?[??]].
      destruct H11 as [p [q [?[??]]]].
      rewrite reindex_project_elem.
      intuition.
      exists c. exists b. intuition.
      assert (d = p) by congruence. subst p.
      assert (a = q) by congruence. subst q.
      apply hom_order with a d; auto.
            
      split; intros.
      rewrite reindex_project_elem in H.
      rewrite reindex_project_elem in H0.
      intuition.
      destruct H4 as [a [b [?[??]]]].
      destruct H5 as [a' [b' [?[??]]]].
      assert (b = b') by congruence. subst b'. clear H7.
      destruct (hom_directed _ _ (project (ds_hom I DS _ _ (reindex_out Hxy)))
        b (a::a'::nil)%list) as [q [??]].
      destruct hf; hnf; auto.
      exists a. apply cons_elem; auto.
      hnf; intros.
      rewrite erel_image_elem.
      apply cons_elem in H7. destruct H7.
      apply hom_order with b a; auto.
      apply cons_elem in H7. destruct H7.
      apply hom_order with b a'; auto.
      apply nil_elem in H7. elim H7.
      apply erel_image_elem in H9.
      destruct (mub_complete (plotkin (ds_F I DS (idx x)))
        (a::a'::nil)%list q) as [q' [??]]; auto.
      destruct hf; simpl; auto.
      exists a. apply cons_elem; auto.
      assert (q' ∈ 
          (clip_set _ (natset x) (eff_enum _ (effective (ds_F I DS (idx x)))))).
      apply (reindex_mubclos x) with (a::a'::nil)%list; auto.
      destruct hf; simpl; auto.
      exists a. apply cons_elem; auto.
      hnf; simpl; intros.
      apply cons_elem in H12. destruct H12. rewrite H12.
      apply clip_set_elem; eauto.
      apply cons_elem in H12. destruct H12. rewrite H12.
      apply clip_set_elem; eauto.
      apply nil_elem in H12. elim H12.
      apply clip_set_elem in H12.
      destruct H12 as [p [q'' [?[??]]]].
      exists p.
      split.
      apply reindex_finord_elem. intuition.
      exists a. exists q''. intuition.
      rewrite <- H14.
      destruct H10.
      apply H10.
      apply cons_elem; auto.
      split.
      apply reindex_finord_elem. intuition.
      exists a'. exists q''. intuition.
      rewrite <- H14.
      destruct H10.
      apply H10.
      apply cons_elem; right.
      apply cons_elem; auto.
      apply reindex_project_elem. intuition.
      exists q''. exists b. intuition.
      apply hom_order with b q; auto.
      rewrite <- H14; auto.

      case_eq hf; auto. intros.
      apply reindex_finord_elem in H0.
      destruct H0 as [? [_ ?]].
      destruct H1 as [a [_ [? _]]].
      
      destruct (hom_directed _ _ (project (ds_hom I DS _ _ (reindex_out Hxy)))
        a nil) as [q [??]].
      rewrite H. hnf. auto.
      hnf; simpl; intros. apply nil_elem in H2. elim H2.
      apply erel_image_elem in H3.
      destruct (mub_complete (plotkin (ds_F I DS (idx x)))
        nil q) as [q' [??]]; auto.
      rewrite H. hnf. auto.
      assert (q' ∈ 
          (clip_set _ (natset x) (eff_enum _ (effective (ds_F I DS (idx x)))))).
      apply (reindex_mubclos x) with nil; auto.
      rewrite H; hnf; auto.
      hnf; simpl; intros. apply nil_elem in H6. elim H6.
      apply clip_set_elem in H6.
      destruct H6 as [n [a' [?[??]]]].
      exists n.
      rewrite reindex_project_elem.
      intuition.
      exists a'. exists a. intuition.
      apply hom_order with a q; auto.
      rewrite <- H8; auto.
    Qed.

    Lemma reindex_ep_pair x y (Hxy:reindex_ord x y) :
      fin_ep_pair hf (proj1_sig (reindex_finord x)) (proj1_sig (reindex_finord y))
         (reindex_embed x y Hxy) (reindex_project x y Hxy).
    Proof.
      constructor. apply finapprox_embed. apply finapprox_project.

      simpl. intros. split; intros.
      rename x0 into n. rename y0 into m.
      rewrite finrel_compose_elem in H.
      2: apply finapprox_embed.
      2: apply finapprox_project.
      destruct H as [p [??]].
      rewrite reindex_finord_elem.
      rewrite reindex_embed_elem in H.
      rewrite reindex_project_elem in H0.
      intuition.
      destruct H4 as [a [b [?[??]]]].
      destruct H5 as [c [b' [?[??]]]].
      assert (b=b') by congruence. subst b'. clear H7.
      exists c. exists a. intuition.
      cut ((a,c) ∈ hom_rel id).
      intros. simpl in H7. apply ident_elem in H7. auto.
      destruct (ep_correct _ _ (ds_hom I DS _ _ (reindex_out Hxy))).
      destruct pe_ident0. apply H7.
      clear H7 H9 ep_ident0.
      simpl. rewrite compose_elem. 2: apply hom_order. eauto.
      
      rewrite finrel_compose_elem.
      2: apply finapprox_embed.
      2: apply finapprox_project.
      apply reindex_finord_elem in H.
      intuition.
      destruct H2 as [a [b [?[??]]]].

      destruct Hxy as [Hidx ?]. simpl in *.
      destruct (e x0) as [q [??]]; auto.
      destruct H5 as [b' [c [?[??]]]].
      assert (b=b') by congruence. subst b'. clear H5.
      unfold choose' in H7.
      match goal with [ _ : appcontext[find_inhabitant' ?A ?X ?Y] |- _ ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      unfold embed_image in m.
      apply esubset_elem in m.
      destruct m as [?[??]].
      exists q. split.
      rewrite reindex_embed_elem. simpl.
      intuition.
      exists b. exists c. intuition.
      apply hom_order with b x1; auto.
      rewrite reindex_project_elem. simpl.
      intuition.
      exists a. exists c. intuition.
      apply hom_order with x1 b; auto.

      intros.
      rename x0 into n. rename y0 into m.
      rewrite finrel_compose_elem in H.
      2: apply finapprox_project.
      2: apply finapprox_embed.
      destruct H as [p [??]].
      simpl.
      rewrite reindex_project_elem in H.
      rewrite reindex_embed_elem in H0.
      intuition.
      destruct H4 as [a [b [?[??]]]].
      destruct H5 as [a' [b' [?[??]]]].
      assert (a=a') by congruence. subst a'. clear H5.
      rewrite reindex_finord_elem. intuition.
      exists b'. exists b. intuition.
      cut ((b,b') ∈ hom_rel id).
      simpl; intros. apply ident_elem in H5. auto.
      destruct (ep_correct _ _ (ds_hom I DS _ _ (reindex_out Hxy))).
      apply ep_ident0. simpl.
      rewrite compose_elem; eauto.
      apply hom_order.
    Qed.      

    Lemma reindex_embed_ident x (Hxx:reindex_ord x x) :
      reindex_embed x x Hxx ≈
      (finrel_inv (proj1_sig (reindex_finord x))).
    Proof.
      split; hnf; simpl; intros.
      destruct a as [n m].
      apply finrel_inv_elem.
      rewrite reindex_embed_elem in H.
      rewrite reindex_finord_elem.
      intuition.
      destruct H2 as [a [b [?[??]]]].
      exists b. exists a. intuition.
      generalize (ds_ident I DS (idx x) (reindex_out Hxx)).
      intros.
      destruct H4.
      apply H4 in H3.
      simpl in H3. apply ident_elem in H3. auto.
      destruct a as [n m].
      rewrite finrel_inv_elem in H.
      rewrite reindex_finord_elem in H.
      rewrite reindex_embed_elem.
      intuition.
      destruct H2 as [a [b [?[??]]]].
      exists b. exists a. intuition.
      generalize (ds_ident I DS (idx x) (reindex_out Hxx)).
      intros. destruct H4.
      apply H5.
      simpl. apply ident_elem. auto.
    Qed.

    Lemma reindex_embed_compose :
      forall i j k 
         (Hij:reindex_ord i j)
         (Hjk:reindex_ord j k)
         (Hik:reindex_ord i k),
          finrel_compose 
            (proj1_sig (reindex_finord j))
            (reindex_embed j k Hjk)
            (reindex_embed i j Hij)
          ≈ 
          reindex_embed i k Hik.
    Proof.
      intros. split; hnf; simpl; intros; destruct a as [n m].
      rewrite finrel_compose_elem in H.
      2: apply finapprox_embed.
      2: apply finapprox_embed.
      destruct H as [p [??]].
      rewrite reindex_embed_elem in H.
      rewrite reindex_embed_elem in H0.     
      rewrite reindex_embed_elem.
      intuition.
      destruct H4 as [a [b [?[??]]]].            
      destruct H5 as [b' [c [?[??]]]].            
      assert (b=b') by congruence. subst b'. clear H5.
      exists a. exists c. intuition.
      destruct (ds_compose I DS (idx i) (idx j) (idx k)
         (reindex_out Hij) (reindex_out Hjk) (reindex_out Hik)).
      apply H5. clear H5 H9.
      simpl. rewrite compose_elem; eauto.
      apply hom_order.
      rewrite finrel_compose_elem.
      2: apply finapprox_embed.
      2: apply finapprox_embed.
      rewrite reindex_embed_elem in H.
      intuition.
      destruct H2 as [a [b [?[??]]]].
      
      destruct Hij as [Hij Hij']; simpl in *.
      destruct Hjk as [Hjk Hjk']; simpl in *.
      destruct (Hij' n) as [q [??]]; auto.
      destruct H5 as [a' [z [?[??]]]].
      assert (a=a') by congruence. subst a'. clear H5.
      unfold choose' in H7.
      match goal with [ _ : appcontext[find_inhabitant' ?A ?X ?Y] |- _ ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      unfold embed_image in m0.
      rewrite esubset_elem in m0.
      destruct m0 as [?[??]].
      destruct (Hjk' q) as [q' [??]]; auto.
      destruct H11 as [z' [y [?[??]]]].
      assert (z=z') by congruence. subst z'. clear H11.
      unfold choose' in H13.
      match goal with [ _ : appcontext[find_inhabitant' ?A ?X ?Y] |- _ ] =>
        destruct (find_inhabitant' A X Y); simpl in *
      end.
      unfold embed_image in m0.
      rewrite esubset_elem in m0.
      destruct m0 as [?[??]].
      exists q.
      split; rewrite reindex_embed_elem; simpl.
      intuition.
      exists a. exists z. intuition.
      apply hom_order with a x; auto.
      intuition.
      exists z. exists b. intuition.
      apply hom_order with z x0; auto.
      cut ((x0,b) ∈ hom_rel id).
      simpl; intro. apply ident_elem in H16. auto.
      destruct (ep_correct _ _ (ds_hom I DS _ _ (reindex_out Hik))).
      apply ep_ident0. clear pe_ident0 ep_ident0.
      simpl. rewrite compose_elem.
      2: apply hom_order.
      exists a. split; auto.
      destruct (ds_compose' I DS (idx i) (idx j) (idx k)
        Hij Hjk (reindex_out Hik)).
      apply H16. clear H16 H17.
      simpl. rewrite compose_elem; eauto.
      exists z; split; auto.
      apply hom_order with x a; auto.
      apply hom_order.
    Qed.

    Definition reindex_fds : finite_directed_system hf reindex' :=
        FinDirSys hf reindex'
          reindex_effective
          reindex_directed
          reindex_finord
          reindex_embed
          reindex_project
          reindex_ep_pair
          reindex_embed_ident
          reindex_embed_compose.

    Definition bilimit : ob := 
       Ob (lim_set hf reindex' reindex_fds)
          (Class _ 
            (lim_ord_mixin hf reindex' reindex_fds)
            (lim_ord_effective hf reindex' reindex_fds)
            (lim_ord_plotkin hf reindex' reindex_fds)).
    
    Program Definition build_reindex (i:I) (x:ds_F I DS i) : reindex :=
      Reindex i 
        (List.map (unenumerate _ (effective (ds_F I DS i)))
               (mub_closure (plotkin (ds_F I DS i)) (x::nil)%list))
        _ _ _.
    Next Obligation.
      repeat intro.
      destruct H as [n [??]].
      apply List.in_map_iff in H.
      destruct H as [q [??]].
      destruct H1. hnf in H1. subst m. clear H3.
      unfold unenumerate in H.
      match goal with [ _ : appcontext[find_inhabitant ?A ?X ?Y] |- _ ] =>
        destruct (find_inhabitant A X Y); simpl in *
      end.
      destruct s as [m [??]].
      simpl in *.
      unfold unenumerate_set in e.
      case_eq (eff_enum _ (effective (ds_F I DS i)) m); intros.
      rewrite H1 in e.
      destruct ((PREORD_EQ_DEC (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
               (eff_to_ord_dec (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
                  (effective (ds_F I DS i)))) q c).
      inversion e. subst x0; clear e.
      subst m.
      rewrite H0 in H1. discriminate.
      discriminate.
      rewrite H1 in e. discriminate.
    Qed.
    Next Obligation.
      intros.
      generalize (refl_equal hf).
      pattern hf at 2.
      case hf. intros. 
      rewrite H at 1.
      hnf.
      exists ((unenumerate (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
        (effective (ds_F I DS i))) x).
      exists ((unenumerate (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
        (effective (ds_F I DS i))) x).
      split.
      apply List.in_map_iff.
      assert (x ∈ mub_closure (plotkin (ds_F I DS i)) (x :: nil)%list).
      apply mub_clos_incl.
      apply cons_elem. auto.
      destruct H0 as [n [??]].
      exists n.
      split; auto.
      apply unenumerate_uniq. auto.
      auto.
      intro. rewrite H at 1.
      hnf. auto.
    Qed.
    Next Obligation.
      repeat intro.
      apply clip_set_elem.
      exists (unenumerate (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
          (effective (ds_F I DS i)) x0).
      case_eq (eff_enum (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
       (effective (ds_F I DS i))
       (unenumerate (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
          (effective (ds_F I DS i)) x0)).
      simpl; intros. exists c. split; auto.
      exists (unenumerate (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
          (effective (ds_F I DS i)) x0).
      split; auto.
      apply List.in_map_iff.
      assert (x0 ∈ mub_closure (plotkin (ds_F I DS i)) (x :: nil)%list).
      apply mub_clos_mub with M; auto.
      apply elem_inh with x. apply cons_elem; auto.
      hnf; intros.
      apply H0 in H3.
      apply clip_set_elem in H3.
      destruct H3 as [n [a' [?[??]]]].
      destruct H3 as [q [??]].
      destruct H6. hnf in H6. subst q. clear H7.
      apply List.in_map_iff in H3.
      destruct H3 as [z [??]].
      exists z. split; auto.
      destruct (unenumerate_correct _ (effective (ds_F I DS i)) z)
        as [q [??]].
      rewrite H3 in H7.
      rewrite H4 in H7.
      inversion H7. subst q.
      rewrite H5; auto.
      destruct H3 as [q [??]].
      exists q; split; auto.
      apply unenumerate_uniq; auto. 
      split; auto.
      destruct (unenumerate_correct _ (effective (ds_F I DS i)) x0)
        as [q [??]].
      rewrite H2 in H3.
      inversion H3. subst q. auto.
      intros.
      destruct (unenumerate_correct _ (effective (ds_F I DS i)) x0)
        as [q [??]].
      rewrite H2 in H3. discriminate.
    Qed.


    Program Definition build_bilimit_elem (i:I) (x:ds_F I DS i) : bilimit :=
      LimSet hf reindex' reindex_fds
          (build_reindex i x)
          (unenumerate _ (effective (ds_F I DS i)) x)
          _.
    Next Obligation.
      simpl.
      intros. apply reindex_finord_elem.
      assert (unenumerate (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
        (effective (ds_F I DS i)) x ∈ natset (build_reindex i x)).
      simpl.
      exists (unenumerate (cls_ord (ds_F I DS i) (class (ds_F I DS i)))
        (effective (ds_F I DS i)) x).
      split; auto.
      apply List.in_map_iff.
      assert (x ∈ mub_closure (plotkin (ds_F I DS i)) (x :: nil)%list).
      apply mub_clos_incl. apply cons_elem; auto.
      destruct H as [z [??]].
      exists z; split; auto.
      apply unenumerate_uniq. auto.
      split; auto. split; auto.
      destruct (unenumerate_correct _ (effective (ds_F I DS i)) x)
        as [q [??]].
      exists q. exists q.
      split; auto.
    Qed.



    Variables X Y:ob.
    Variable embed : ord X → ord Y.
    Hypothesis embed_reflects : forall x x',
      embed#x ≤ embed#x' -> x ≤ x'.
    Hypothesis embed_func_directed0 : forall y,
      if hf then True else exists x, embed#x ≤ y.
    Hypothesis embed_directed2 : forall y, forall a b,
      embed#a ≤ y ->
      embed#b ≤ y ->
      exists c, embed#c ≤ y /\ a ≤ c /\ b ≤ c.

    Definition bilimit_spoke_embed (i:I) (x:ds_F I DS i) (y:bilimit) :=
      exists n:reindex, exists x':reindex_finord n, exists c:ds_F I DS i,
        idx n = i /\
        lim_embed_spec hf _ reindex_fds n x' y /\
        eff_enum _ (effective (ds_F I DS i)) (proj1_sig x') = Some c /\
        c ≤ x.
      
    Definition bilimit_spoke_project (i:I) (x:ord bilimit) (y:ord (ds_F I DS i)) :=
      exists n:reindex, exists y':reindex_finord n, exists c:ds_F I DS i,
        idx n = i /\
        lim_proj_spec hf _ reindex_fds n x y' /\
        eff_enum _ (effective (ds_F I DS i)) (proj1_sig y') = Some c /\
        y ≤ c.

    Lemma bilimit_pe (i:I) x y :
      (exists q,
        bilimit_spoke_project i x q /\
        bilimit_spoke_embed i q y) ->
      x ≥ y.
    Proof.
      intros [q[??]].
      destruct H as [n [y' [c [?[?[??]]]]]].
      destruct H0 as [m [x' [d [?[?[??]]]]]].
      destruct (reindex_directed (n::m::nil)%list) as [k [??]].
      case_eq hf; simpl; intros; auto.
      exists n. apply cons_elem; auto.
      hnf; intros. apply eff_complete.
      assert (n ≤ k).
      apply H7. apply cons_elem; auto.
      assert (m ≤ k).
      apply H7. apply cons_elem; right. apply cons_elem; auto.
      clear H7 H8.
      generalize (lim_proj_cone hf reindex' reindex_fds n k H9 x y').
      intros.
      generalize H1; intros.
      rewrite H7 in H1. clear H7.
      destruct H1 as [w [??]].
      simpl in H7.
      generalize (lim_embed_cocone hf reindex' reindex_fds m k H10 x' y).
      intros. generalize H8; intros.
      rewrite H11 in H4; clear H11.
      destruct H4 as [v [??]].
      simpl in H4.
      apply reindex_embed_elem in H4.
      destruct H4 as [?[? [ww [qq [?[??]]]]]].
      simpl in H4.
      revert ww H14 H16.
      simpl.
      generalize (reindex_out H10).
      rewrite H0. intros.
      simpl in H5. simpl in H14.
      rewrite H5 in H14.
      assert (ww = d) by congruence. subst ww; clear H14.
      apply reindex_project_elem in H7.
      destruct H7 as [? [? [ww [zz [?[??]]]]]].
      revert ww H17 H19.
      generalize (reindex_out H9).
      rewrite H. intros.
      simpl in H17. simpl in H2. rewrite H2 in H17.
      assert (ww = c) by congruence. subst ww; clear H17.
      assert ((zz,qq) ∈ hom_rel id).
      generalize (ep_correct _ _ (ds_hom I DS i (idx k) o)).
      intros [??].
      apply ep_ident0. clear pe_ident0 ep_ident0.
      simpl. apply compose_elem. apply hom_order.
      exists d. split; auto.
      generalize (ds_compose' I DS i i (idx k) (ord_refl _ _) o0 o). 
      intros [??]. apply H17. clear H17 H20.
      simpl. apply compose_elem. apply hom_order.
      exists c. split; auto.
      generalize (ds_ident' I DS i (ord_refl _ _)).
      intros [??]. apply H20. clear H17 H20.
      simpl. apply ident_elem.
      transitivity q; auto.
      simpl in H17.
      apply ident_elem in H17.
      assert ((v:fds_F hf _ reindex_fds k) ≤ w).
      red. simpl. red. simpl.
      apply reindex_finord_elem.
      intuition.
      exists qq. exists zz. intuition.
      assert (lim_proj_spec hf _ reindex_fds k x v).
      apply lim_proj_spec_order with x w; auto.
      
      revert H21 H11.
      admit. (* pe lemma at finord level *)
    Qed.

    Lemma bilimit_ep1 (i:I) x y :
      (exists q,
        bilimit_spoke_embed i x q /\
        bilimit_spoke_project i q y)
      ->
      x ≥ y.
    Proof.
      intros [q [??]].
      
    Qed.

  End fds.

End XPLT.



Module PLT.
  Module PARAM.
    Definition hf := false.
  End PARAM.
  Include XPLT(PARAM).

  Canonical Structure PLT : category := Category PLT.ob PLT.hom PLT.cat_class.

  Theorem pair_commute1 C A B (f:hom C A) (g:hom C B) :
    pi1 ∘ pair f g ≈ f.
  Proof.
    apply pair_proj_commute1.
    apply hom_order.
    apply hom_order.
    apply hom_directed.
  Qed.

  Theorem pair_commute2 C A B (f:hom C A) (g:hom C B) :
    pi2 ∘ pair f g ≈ g.
  Proof.
    apply pair_proj_commute2.
    apply hom_order.
    apply hom_order.
    apply hom_directed.
  Qed.

  Theorem pair_universal C A B (f:hom C A) (g:hom C B) (PAIR:hom C (prod A B)) :
    pi1 ∘ PAIR ≈ f -> pi2 ∘ PAIR ≈ g -> PAIR ≈ pair f g.
  Proof.
    apply (pair_rel_universal false).
    apply hom_order.
    apply hom_order.
    apply hom_order.
    apply hom_directed.
  Qed.

  Theorem curry_apply A B C (f:hom (prod C A) B) :
    app ∘ pair_map (curry f) id ≈ f.
  Proof.
    rewrite pair_map_eq.
    apply curry_apply. 
    apply hom_directed. 
    apply plotkin.
  Qed. 

  Theorem curry_universal A B C (f:hom (prod C A) B) (CURRY:hom C (exp A B)) :
    app ∘ pair_map CURRY id ≈ f -> CURRY ≈ curry f.
  Proof.
    intro. apply (curry_universal false); auto.
    apply (hom_directed _ _ f).
    apply plotkin.
    apply (hom_order _ _ CURRY).
    apply (hom_directed _ _ CURRY).
    rewrite pair_map_eq in H. apply H.
  Qed.
End PLT.

Notation PLT := PLT.PLT.

Canonical Structure PLT.ord.
Canonical Structure PLT.dec.
Canonical Structure PLT.hom_ord.
Canonical Structure PLT.hom_eq.
Canonical Structure PLT.prod.
Canonical Structure PLT.comp.
Canonical Structure PLT.


Module PPLT.
  Module PARAM.
    Definition hf := true.
  End PARAM.
  Include XPLT(PARAM).

  Canonical Structure PPLT : category := Category PPLT.ob PPLT.hom PPLT.cat_class.

  Theorem pair_commute1 C A B (f:hom C A) (g:hom C B) :
    pi1 ∘ pair f g ≤ f.
  Proof.
    apply pair_proj_commute1_le.
    apply hom_order.
    apply hom_order.
  Qed.

  Theorem pair_commute2 C A B (f:hom C A) (g:hom C B) :
    pi2 ∘ pair f g ≤ g.
  Proof.
    apply pair_proj_commute2_le.
    apply hom_order.
    apply hom_order.
  Qed.

  Theorem pair_universal C A B (f:hom C A) (g:hom C B) (PAIR:hom C (prod A B)) :
    pi1 ∘ PAIR ≈ f -> pi2 ∘ PAIR ≈ g -> PAIR ≈ pair f g.
  Proof.
    apply (pair_rel_universal true).
    apply hom_order.
    apply hom_order.
    apply hom_order.
    apply hom_directed.
  Qed.

  Theorem pair_universal_le C A B (f:hom C A) (g:hom C B) (PAIR:hom C (prod A B)) :
    pi1 ∘ PAIR ≤ f -> pi2 ∘ PAIR ≤ g -> PAIR ≤ pair f g.
  Proof.
    apply pair_rel_universal_le.
    apply hom_order.
    apply hom_order.
    apply hom_order.
  Qed.

  Theorem curry_apply A B C (f:hom (prod C A) B) :
    app ∘ pair_map (curry f) id ≈ f.
  Proof.
    rewrite pair_map_eq.
    apply curry_apply. 
    apply hom_directed. 
    apply plotkin.
  Qed. 

  Theorem curry_universal A B C (f:hom (prod C A) B) (CURRY:hom C (exp A B)) :
    app ∘ pair_map CURRY id ≈ f -> CURRY ≈ curry f.
  Proof.
    intro. apply (curry_universal true); auto.
    apply (hom_directed _ _ f).
    apply plotkin.
    apply (hom_order _ _ CURRY).
    apply (hom_directed _ _ CURRY).
    rewrite pair_map_eq in H. apply H.
  Qed.
End PPLT.

Notation PPLT := PPLT.PPLT.

Canonical Structure PPLT.ord.
Canonical Structure PPLT.dec.
Canonical Structure PPLT.hom_ord.
Canonical Structure PPLT.hom_eq.
Canonical Structure PPLT.prod.
Canonical Structure PPLT.comp.
Canonical Structure PPLT.

Program Definition plotkin_forget (A:preord)
  (Heff:effective_order A)
  (HA:plotkin_order false A) : plotkin_order true A

    := norm_plt A Heff true _.
Next Obligation.
  repeat intro. exists (mub_closure HA X).
  split.
  intros. apply mub_clos_incl; auto.
  split.
  hnf. hnf in Hinh.
  destruct Hinh as [x ?].
  exists x. apply mub_clos_incl; auto.
  repeat intro.
  generalize (mub_clos_mub HA X I M).
  intros. 
  destruct (mub_complete HA M z).
  hnf; auto.
  hnf; intros.
  apply H in H1.
  apply finsubset_elem in H1. destruct H1; auto.
  intros. rewrite <- H2; auto.
  destruct H1.
  exists x. split.
  destruct H1; auto.
  apply finsubset_elem.
  intros. rewrite <- H3; auto.
  split; auto.
  apply H0; auto.
  hnf; auto.
  hnf; intros.
  apply H in H3.
  apply finsubset_elem in H3.
  destruct H3; auto.
  intros. rewrite <- H4; auto.
Qed.


Definition forgetPLT_ob (X:PLT.ob) : PPLT.ob :=
  PPLT.Ob (PLT.carrier X) (PPLT.Class _
    (Preord.mixin (PLT.ord X))
    (PLT.effective X)
    (plotkin_forget _ (PLT.effective X) (PLT.plotkin X))).

Program Definition forgetPLT_map (X Y:PLT.ob) (f:PLT.hom X Y) 
  : PPLT.hom (forgetPLT_ob X) (forgetPLT_ob Y) :=
  PPLT.Hom (forgetPLT_ob X) (forgetPLT_ob Y) 
    (PLT.hom_rel f) (PLT.hom_order _ _ f) _.
Next Obligation.
  repeat intro. apply (PLT.hom_directed _ _ f); hnf; auto.
Qed.

Program Definition forgetPLT : functor PLT PPLT :=
  Functor PLT PPLT forgetPLT_ob forgetPLT_map _ _ _.
Solve Obligations of forgetPLT using auto.

Definition liftPPLT_ob (X:PPLT.ob) : PLT.ob :=
  PLT.Ob (option (PPLT.carrier X)) (PLT.Class _
    (lift_mixin (PPLT.ord X)) 
    (effective_lift (PPLT.effective X)) 
    (lift_plotkin _ _ _  (PPLT.plotkin X) (PPLT.effective X))).

Definition liftPPLT_rel (X Y:preord) (HX:effective_order X) (f:erel X Y)
  : erel (lift X) (lift Y) :=
  union2 (union2 (single (None,None))
    (image (mk_pair (liftup X) (const (@None Y))) (eff_enum X HX)))
    (image (pair_map (liftup X) (liftup Y)) f).

Lemma liftPPLT_rel_elem X Y HX f :
  forall x y, (x,y) ∈ liftPPLT_rel X Y HX f <->
    (y ≈ None \/ exists a b, (a,b) ∈ f /\ x ≈ Some a /\ y ≈ Some b).
Proof.
  unfold liftPPLT_rel.
  intuition.
  apply elem_union2 in H. destruct H.
  apply elem_union2 in H. destruct H.
  apply single_axiom in H.
  left.
  destruct H as [[??][??]]; split; auto.
  apply image_axiom2 in H.
  destruct H as [q [??]].
  simpl in H0.
  left.
  destruct H0 as [[??][??]]; split; auto.
  apply image_axiom2 in H.
  destruct H as [[p q] [??]].
  right.
  simpl in H0.
  exists p. exists q.
  split; auto.
  destruct H0 as [[??][??]]; split; split; auto.
  apply elem_union2.
  left.
  apply elem_union2.
  destruct x.
  right.
  apply image_axiom1'.
  simpl. exists c. split; auto.
  split; split; auto.
  apply eff_complete.
  left.
  apply single_axiom.
  split; split; auto.
  destruct H0 as [a [b [?[??]]]].
  apply elem_union2. right.
  apply image_axiom1'.
  exists (a,b). split; auto.
  simpl.
  split; split; auto.
Qed.  

Program Definition liftPPLT_map (X Y:PPLT.ob) (f:X → Y) : liftPPLT_ob X → liftPPLT_ob Y :=
  PLT.Hom (liftPPLT_ob X) (liftPPLT_ob Y)
     (liftPPLT_rel (PPLT.ord X) (PPLT.ord Y) (PPLT.effective X) (PPLT.hom_rel f))
      _ _.
Next Obligation.
  intros. simpl in *.
  apply liftPPLT_rel_elem.
  apply (liftPPLT_rel_elem (PPLT.ord X) (PPLT.ord Y)) in H1.
  destruct H1. left.
  rewrite H1 in H0.
  split; auto. red; simpl; auto.
  destruct H1 as [a [b [?[??]]]].
  destruct y'.
  right.
  rewrite H2 in H.
  destruct x'.
  exists c0. exists c.
  split; auto.
  apply PPLT.hom_order with a b; auto.
  rewrite H3 in H0. auto.
  elim H.
  left; auto.
Qed.
Next Obligation.
  repeat intro.
  set (M' := unlift_list M).
  case_eq M'; intros.
  exists None.
  split.
  red; intros.
  destruct x0; auto.
  destruct H1 as [q [??]].
  destruct q.
  assert (List.In c0 M').
  apply in_unlift. auto.
  rewrite H0 in H3. elim H3.
  auto.
  apply erel_image_elem.
  apply liftPPLT_rel_elem.
  auto.
  destruct x.
  destruct (PPLT.hom_directed _ _ f c0 M').
  exists c. rewrite H0. apply cons_elem; auto.
  red; intros.
  destruct H1 as [q [??]].
  apply in_unlift in H1.
  assert (Some a ∈ M).
  exists (Some q); split; auto.
  apply H in H3.
  apply erel_image_elem in H3.
  apply (liftPPLT_rel_elem (PPLT.ord X) (PPLT.ord Y)) in H3.
  destruct H3.
  destruct H3. elim H3.
  destruct H3 as [m [n [?[??]]]].
  apply erel_image_elem.
  apply PPLT.hom_order with m n; auto.
  destruct H1.
  exists (Some x).
  split.
  red; intros.
  destruct x0.
  apply erel_image_elem in H2.
  apply H1.
  destruct H3 as [q [??]].
  destruct q.
  exists c2; split; auto.
  apply in_unlift; auto.
  destruct H4. elim H4.
  red; auto.
  apply erel_image_elem in H2.  
  apply erel_image_elem.  
  apply liftPPLT_rel_elem.
  right; eauto.
  assert (Some c ∈ M).
  exists (Some c). split; auto.
  apply in_unlift.
  fold M'. rewrite H0. simpl; auto.
  apply H in H1.
  apply erel_image_elem in H1.
  apply (liftPPLT_rel_elem (PPLT.ord X) (PPLT.ord Y)) in H1.
  destruct H1.
  destruct H1. elim H1.
  destruct H1 as [a [b [?[??]]]].
  destruct H2. elim H4.
Qed.

Program Definition liftPPLT : functor PPLT PLT :=
  Functor PPLT PLT liftPPLT_ob liftPPLT_map _ _ _.
Next Obligation.
  simpl; intros.
  split; hnf; simpl; intros.
  destruct a as [a a'].
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel f)) in H0.
  destruct H0.
  apply ident_elem. rewrite H0. red; simpl; auto.
  apply ident_elem. 
  destruct H0 as [p [q [?[??]]]].
  rewrite H1. rewrite H2.  
  destruct H. red in H. simpl in H.
  apply H in H0.
  apply ident_elem in H0. auto.
  destruct a as [a a'].
  apply ident_elem in H0.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel f)).
  destruct a'; auto.
  right.
  destruct a. 2: elim H0.
  exists c0. exists c.  
  split; auto.
  destruct H. apply H1.
  simpl. apply ident_elem. auto.
Qed.
Next Obligation.
  intros.
  split; hnf; simpl; intros.
  destruct a as [a c].
  apply compose_elem.
  apply liftPPLT_map_obligation_1.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel h)) in H0.
  destruct H0.
  exists None.
  split.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel g)).
  auto.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective B) (PPLT.hom_rel f)).
  auto.
  destruct H0 as [a' [c' [?[??]]]].  
  destruct H.
  apply H in H0.
  simpl in H0.
  apply compose_elem in H0.
  destruct H0 as [b' [??]].
  exists (Some b').
  split.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel g)).
  right.
  eauto.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective B) (PPLT.hom_rel f)).
  right. eauto.
  apply PPLT.hom_order.

  destruct a as [a c].
  apply compose_elem in H0.
  destruct H0 as [b [??]]. simpl in b.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel g)) in H0.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective B) (PPLT.hom_rel f)) in H1.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel h)).
  destruct H1; auto.
  destruct H0.
  destruct H1 as [?[?[?[??]]]].
  rewrite H0 in H2. destruct H2. elim H4.
  right.  
  destruct H0 as [x [y [?[??]]]].
  destruct H1 as [x' [y' [?[??]]]].
  rewrite H3 in H4.
  exists x. exists y'.
  split; auto.
  destruct H. apply H6.
  simpl. apply compose_elem.
  apply PPLT.hom_order.
  exists y.
  split; auto.
  apply PPLT.hom_order with x' y'; auto.
  simpl. intros.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel g)) in H3.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel g)).
  destruct H3. left.
  split; auto.
  rewrite H3 in H2; auto.
  red; simpl; auto.
  destruct H3 as [p [q [?[??]]]].  
  destruct y'. 2: auto.
  right.  
  destruct x. destruct y.
  destruct x'.
  exists c3. exists c0. split; auto.
  apply PPLT.hom_order with p q; auto.
  destruct H4.
  transitivity c1; auto.
  destruct H5.
  transitivity c2; auto.
  elim H1.
  destruct H5. elim H6.
  destruct H4. elim H6.
Qed.
Next Obligation.
  intros.  
  split; hnf; simpl; intros.
  destruct a as [a b].
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel f)) in H0.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel g)).
  destruct H0; auto.    
  right.
  destruct H0 as [p [q [?[??]]]].
  exists p. exists q. split; auto.
  destruct H. apply H; auto.
  destruct a as [a b].
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel g)) in H0.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel f)).
  destruct H0; auto.    
  right.
  destruct H0 as [p [q [?[??]]]].
  exists p. exists q. split; auto.
  destruct H. apply H3; auto.
Qed.

Coercion PLT.ord : PLT.ob >-> preord.
Coercion PPLT.ord : PPLT.ob >-> preord.

Definition adj_unit_rel (X:preord) (HX:effective_order X) : erel X (lift X) :=
 union2
    (image (mk_pair (id(X)) (const None)) (eff_enum X HX))
    (image (pair_map (id(X)) (liftup X))
      (esubset_dec _ (fun q => fst q ≥ snd q)
                  (fun q => eff_ord_dec X HX (snd q) (fst q))
                  (eprod (eff_enum X HX)
                         (eff_enum X HX)))).

Lemma adj_unit_rel_elem X HX x x' :
  (x,x') ∈ adj_unit_rel X HX <-> Some x ≥ x'.
Proof.
  unfold adj_unit_rel.
  split; intros.
  apply elem_union2 in H.
  destruct H.
  apply image_axiom2 in H.
  destruct H as [y [??]].
  simpl in H0.
  destruct H0. destruct H0.
  transitivity (@None X); auto.
  red; simpl; auto.
  apply image_axiom2 in H.
  destruct H as [y [??]].
  simpl in H0.
  apply esubset_dec_elem in H.
  destruct H.
  destruct H0. destruct H0.
  transitivity (Some (snd y)); auto.
  transitivity (Some (fst y)); auto.
  destruct H2. auto.
  intros.
  destruct H1 as [[??][??]].
  transitivity (snd x0); auto.
  transitivity (fst x0); auto.
  apply elem_union2.
  destruct x'.
  right.
  apply image_axiom1'.
  simpl. exists (x,c).
  split; auto.
  apply esubset_dec_elem.
  intros.
  destruct H0 as [[??][??]].
  transitivity (snd x0); auto.
  transitivity (fst x0); auto.
  split; auto.
  apply elem_eprod. split; apply eff_complete.
  left.
  apply image_axiom1'.
  simpl. exists x. split; auto. apply eff_complete.
Qed.

Program Definition adj_unit_hom (X:PLT.ob) : PLT.hom X (liftPPLT (forgetPLT X))
  := PLT.Hom X (liftPPLT (forgetPLT X)) (adj_unit_rel (PLT.ord X) (PLT.effective X)) _ _.
Next Obligation.
  intros.
  apply adj_unit_rel_elem in H1.
  apply adj_unit_rel_elem.
  transitivity y; auto.
  transitivity (Some x); auto.
Qed.
Next Obligation.
  repeat intro.
  exists (Some x).
  split.
  red; intros.
  apply H in H0.
  apply erel_image_elem in H0.
  apply adj_unit_rel_elem in H0. auto.
  apply erel_image_elem.
  apply adj_unit_rel_elem.
  auto.
Qed.

Program Definition adj_unit : nt id(PLT) (liftPPLT ∘ forgetPLT)
  := NT id(PLT) (liftPPLT ∘ forgetPLT) adj_unit_hom _.
Next Obligation.
  simpl; intros.
  split; hnf; simpl; intros.
  destruct a as [a b].
  apply compose_elem in H.
  destruct H as [b' [??]].
  apply adj_unit_rel_elem in H0.
  apply compose_elem.
  apply adj_unit_hom_obligation_1.
  simpl.
  exists (Some a).
  split.
  apply adj_unit_rel_elem. auto.
  apply liftPPLT_rel_elem.
  destruct b; auto.
  right.
  exists a. exists c.
  split; auto.
  apply PLT.hom_order with a b'; auto.
  apply PLT.hom_order.
  
  destruct a as [a b].
  apply compose_elem in H.
  simpl in H.
  destruct H as [a' [??]].
  apply adj_unit_rel_elem in H.
  apply compose_elem.
  apply PLT.hom_order.
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel f)) in H0.
  destruct H0.
  destruct (PLT.hom_directed _ _ f a nil).  
  red; simpl; auto.
  red; simpl; intros. apply nil_elem in H1. elim H1.
  destruct H1. apply erel_image_elem in H2.
  exists x. split; auto.
  apply adj_unit_rel_elem; auto.
  rewrite H0. red; simpl; auto.
  destruct H0 as [p [q [?[??]]]].
  exists q. split; auto.
  apply PLT.hom_order with p q; auto.
  rewrite H1 in H. auto.
  apply adj_unit_rel_elem. auto.
  apply adj_unit_hom_obligation_1.
Qed.

Definition adj_counit_rel (Y:PPLT.ob) : erel (forgetPLT (liftPPLT Y)) Y :=
    (image (pair_map (liftup Y) (id(PPLT.ord Y)))
      (esubset_dec _ (fun q => fst q ≥ snd q)
                  (fun q => eff_ord_dec Y (PPLT.effective Y) (snd q) (fst q))
                  (eprod (eff_enum Y (PPLT.effective Y))
                         (eff_enum Y (PPLT.effective Y))))).

Lemma adj_counit_rel_elem Y : forall y y',
  (y,y') ∈ adj_counit_rel Y <-> y ≥ Some y'.
Proof.
  unfold adj_counit_rel.
  intuition.
  apply image_axiom2 in H.
  destruct H as [[p q] [??]].
  apply esubset_dec_elem in H. destruct H.
  simpl in H0.
  destruct H0 as [[??][??]]. simpl in *.
  transitivity (Some q); auto.
  transitivity (Some p); auto.
  intros. destruct H1 as [[??][??]].
  transitivity (snd x); auto.  
  transitivity (fst x); auto.  
  
  apply image_axiom1'.
  destruct y.
  exists (c,y'). split; simpl; auto.
  apply esubset_dec_elem.
  intros. destruct H0 as [[??][??]].
  transitivity (snd x); auto.  
  transitivity (fst x); auto.  
  split; auto.
  apply elem_eprod. split; apply eff_complete.
  elim H.
Qed.

Program Definition adj_counit_hom Y : PPLT.hom (forgetPLT (liftPPLT Y)) Y :=
  PPLT.Hom (forgetPLT (liftPPLT Y)) Y (adj_counit_rel Y) _ _.
Next Obligation.
  intros.
  apply adj_counit_rel_elem in H1.
  apply adj_counit_rel_elem.
  transitivity (Some y); auto.
  transitivity x; auto.  
Qed.  
Next Obligation.
  repeat intro.
  destruct x.
  exists c.
  split.
  red; intros.
  apply H in H0.
  apply image_axiom2 in H0.
  destruct H0 as [[p q] [??]].
  apply esubset_dec_elem in H0.
  destruct H0.
  simpl in H1, H2. 
  rewrite H1.
  apply adj_counit_rel_elem in H0.
  rewrite H2 in H0. auto.
  simpl; intros.
  destruct H2 as [[??][??]]; auto.
  transitivity (fst x0); auto.
  apply erel_image_elem.
  apply adj_counit_rel_elem. auto.

  destruct Hinh as [q ?].
  apply H in H0.
  apply erel_image_elem in H0.
  apply adj_counit_rel_elem in H0.
  elim H0.
Qed.

Program Definition adj_counit : nt (forgetPLT ∘ liftPPLT) id(PPLT)
  := NT (forgetPLT ∘ liftPPLT) id(PPLT) adj_counit_hom _.
Next Obligation.
  intros.
  split; hnf; simpl; intros.
  destruct a as [a b].
  apply compose_elem in H; simpl.
  simpl in H.
  destruct H as [b' [??]].
  apply (adj_counit_rel_elem B) in H0.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel f)) in H.
  destruct H.
  rewrite H in H0. elim H0.
  destruct H as [p [q [?[??]]]].  
  apply compose_elem.
  apply adj_counit_hom_obligation_1.
  rewrite H2 in H0.
  exists p.
  split.
  apply adj_counit_rel_elem.
  rewrite H1; auto.
  apply PPLT.hom_order with p q; auto.
  apply liftPPLT_map_obligation_1.

  destruct a as [a b].
  apply compose_elem in H; simpl.
  destruct H as [a' [??]].  
  apply adj_counit_rel_elem in H.
  destruct a. 2: elim H.
  apply compose_elem; simpl.
  apply liftPPLT_map_obligation_1.
  exists (Some b).
  split.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel f)).
  right.
  exists c. exists b. split; auto.
  apply (PPLT.hom_order _ _ f) with a' b; auto.
  apply adj_counit_rel_elem. auto.
  apply adj_counit_hom_obligation_1.
Qed.

Program Definition adj_counit_inv_hom Y : PPLT.hom Y (forgetPLT (liftPPLT Y)) :=
  PPLT.Hom Y (forgetPLT (liftPPLT Y)) (adj_unit_rel (PPLT.ord Y) (PPLT.effective Y)) _ _.
Next Obligation.
  intros.
  apply adj_unit_rel_elem in H1.
  apply adj_unit_rel_elem.
  transitivity y; auto.
  transitivity (Some x); auto.
Qed.
Next Obligation.
  repeat intro.
  exists (Some x).
  split.
  red; intros.
  apply H in H0.
  apply erel_image_elem in H0.
  apply adj_unit_rel_elem in H0. auto.
  apply erel_image_elem.
  apply adj_unit_rel_elem.
  auto.
Qed.

Lemma adj_counit_inv_ntish : forall A B f,
  adj_counit_inv_hom B ∘ f ≤ forgetPLT@(liftPPLT@ f) ∘ adj_counit_inv_hom A.
Proof.
  intros. hnf; simpl; intros.
  destruct a as [a b].
  apply compose_elem in H.
  apply compose_elem. simpl.
  intros. apply adj_unit_rel_elem in H2.
  apply adj_unit_rel_elem.
  transitivity y; auto.
  transitivity (Some x); auto.
  simpl.
  destruct H as [y [??]].
  exists (Some a). split.
  apply adj_unit_rel_elem; auto.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective A) (PPLT.hom_rel f)).
  apply adj_unit_rel_elem in H0.
  destruct b; auto.
  right.
  exists a. exists c. split; auto.
  apply PPLT.hom_order with a y; auto.
  apply PPLT.hom_order.
Qed.

Lemma adj_counit_inv_le Y : adj_counit_inv_hom Y ∘ adj_counit Y ≤ id.
Proof.
  hnf; simpl; intros.
  destruct a as [y y'].
  apply compose_elem in H.
  destruct H as  [y'' [??]].
  apply adj_counit_rel_elem in H.
  apply adj_unit_rel_elem in H0. 
  apply ident_elem.
  transitivity (Some y''); auto.
  apply adj_counit_hom_obligation_1.
Qed.

Lemma adj_counit_inv_largest Y : forall f,
  f ∘ adj_counit Y ≤ id -> f ≤ adj_counit_inv_hom Y.
Proof.
  repeat intro; simpl in *.
  destruct a.
  apply adj_unit_rel_elem.
  assert ((Some c, o) ∈ PPLT.hom_rel (f ∘ adj_counit_hom Y)).
  simpl.
  apply compose_elem.
  apply adj_counit_hom_obligation_1.
  exists c. split; auto.
  apply adj_counit_rel_elem. auto.
  apply H in H1.
  simpl in H1.
  apply ident_elem in H1. auto.
Qed.

Lemma adj_counit_inv_eq Y : adj_counit Y ∘ adj_counit_inv_hom Y ≈ id.
Proof.
  split; hnf; simpl; intros.
  destruct a as [y y'].
  apply compose_elem in H.
  simpl in H.
  destruct H as  [y'' [??]].
  apply adj_unit_rel_elem in H.
  apply ident_elem.
  rewrite (adj_counit_rel_elem Y) in H0.
  destruct y''.
  transitivity c; auto.
  elim H0.
  simpl. intros.
  apply adj_unit_rel_elem in H2.
  apply adj_unit_rel_elem.
  transitivity y0; auto.
  transitivity (Some x); auto.

  destruct a as [y y'].
  apply ident_elem in H.
  apply compose_elem.
  simpl; intros.
  apply adj_unit_rel_elem in H2.
  apply adj_unit_rel_elem.
  transitivity y0; auto.
  transitivity (Some x); auto.
  simpl.  
  exists (Some y').
  split.
  apply adj_unit_rel_elem. auto.
  apply adj_counit_rel_elem; auto.
Qed.

Program Definition PLT_adjoint : adjunction forgetPLT liftPPLT :=
  Adjunction forgetPLT liftPPLT adj_unit adj_counit _ _.
Next Obligation.
  split; hnf; simpl; intros.
  destruct a as [a a'].
  apply ident_elem. 
  apply compose_elem in H; simpl in *.
  destruct H as [y [??]].  
  apply adj_unit_rel_elem in H.
  apply (adj_counit_rel_elem (forgetPLT_ob A)) in H0.
  change (Some a' ≤ Some a).
  transitivity y; auto.
  apply adj_unit_hom_obligation_1.

  destruct a as [a a'].
  apply ident_elem in H.
  apply compose_elem; simpl in *.
  apply adj_unit_hom_obligation_1.
  exists (Some a).
  split.
  apply adj_unit_rel_elem. auto.
  apply (adj_counit_rel_elem (forgetPLT_ob A)).
  auto.  
Qed.
Next Obligation.
  split; hnf; simpl; intros.
  destruct a as [a a'].
  apply ident_elem. 
  apply compose_elem in H; simpl in *.
  destruct H as [y [??]].  
  apply adj_unit_rel_elem in H.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective _) (adj_counit_rel A)) in H0.
  destruct H0.
  rewrite H0. red; simpl; auto.
  destruct H0 as [p [q [?[??]]]].
  rewrite H2.
  apply (adj_counit_rel_elem A) in H0.
  transitivity p; auto.
  rewrite H1 in H. auto.
  simpl; intros.
  eapply adj_unit_hom_obligation_1; eauto.
  
  destruct a as [a a'].
  apply ident_elem in H.  
  apply compose_elem; simpl in *.
  simpl; intros.
  eapply adj_unit_hom_obligation_1; eauto.
  exists (Some a).  
  split.
  apply adj_unit_rel_elem. auto.
  apply (liftPPLT_rel_elem _ _ (PPLT.effective _) (adj_counit_rel A)).
  destruct a'; auto.
  right.
  destruct a.
  simpl.
  exists (Some c0). exists c.
  split; auto.
  apply (adj_counit_rel_elem A). auto.
  elim H.  
Qed.

Lemma liftPPLT_reflects : forall (X Y:ob PPLT) (f f':X → Y),
  liftPPLT@f ≤ liftPPLT@f' -> f ≤ f'.
Proof.
  repeat intro; simpl in *.
  destruct a as [x y].
  assert ((Some x, Some y) ∈ (PLT.hom_rel (liftPPLT_map X Y f))).
  simpl.
  apply (liftPPLT_rel_elem _ _ _ (PPLT.hom_rel f)).
  right. exists x. exists y. split; auto.
  apply H in H1.
  simpl in H1.
  apply (liftPPLT_rel_elem _ _ _ (PPLT.hom_rel f')) in H1.
  destruct H1.
  destruct H1. elim H1.
  destruct H1 as [a [b [?[??]]]].
  apply member_eq with (a,b); auto.
  split; split; auto.
Qed.

Lemma liftPPLT_mono : forall (X Y:ob PPLT) (f f':X → Y),
  f ≤ f' -> liftPPLT@f ≤ liftPPLT@f'.
Proof.
  repeat intro; simpl in *.
  destruct a as [x y].
  apply (liftPPLT_rel_elem _ _ _ (PPLT.hom_rel f)) in H0.
  apply (liftPPLT_rel_elem _ _ _ (PPLT.hom_rel f')).
  destruct H0; auto. right.
  destruct H0 as [a [b [?[??]]]].
  exists a. exists b. split; auto.
Qed.  

Lemma forgetPLT_mono : forall (X Y:ob PLT) (f f':X → Y),
  f ≤ f' -> forgetPLT@f ≤ forgetPLT@f'.
Proof.
  auto.
Qed.

Lemma forgetPLT_reflects : forall (X Y:ob PLT) (f f':X → Y),
  forgetPLT@f ≤ forgetPLT@f' -> f ≤ f'.
Proof.
  auto.
Qed.

Section strictify.
  Variables X Y:ob PPLT.
  Variable f: liftPPLT X → liftPPLT Y.  

  Let strictify := adj_counit Y ∘ forgetPLT@f ∘ adj_counit_inv_hom X.

  Lemma f_explode : liftPPLT@(adj_counit Y ∘ forgetPLT@f) ∘ adj_unit (liftPPLT X) ≈ f.
    rewrite Functor.compose. 2: reflexivity.
    rewrite <- (cat_assoc (liftPPLT@adj_counit Y)).
    rewrite <- (NT.axiom adj_unit f).
    rewrite (cat_assoc (liftPPLT@adj_counit Y)).
    generalize (Adjunction.adjoint_axiom2 PLT_adjoint Y).
    intros. simpl in H.
    rewrite H.
    rewrite (cat_ident2 (id@f)).
    auto.
  Qed.

  Lemma strictify_le : liftPPLT@strictify ≤ f.
  Proof.  
    unfold strictify.
    rewrite Functor.compose. 2: reflexivity.
    rewrite <- f_explode at 2.
    apply PLT.compose_mono.

    generalize (Adjunction.adjoint_axiom2 PLT_adjoint).
    intro.
    generalize (H X).
    intros.
    transitivity
      (liftPPLT@adj_counit_inv_hom X ∘ id (liftPPLT X)).
    rewrite (cat_ident1 (liftPPLT@adj_counit_inv_hom X)). auto.
    rewrite <- H0.
    simpl.
    rewrite (cat_assoc (liftPPLT@adj_counit_inv_hom X)).
    rewrite <- (Functor.compose liftPPLT). 2: reflexivity.
    transitivity (id ∘ adj_unit_hom (liftPPLT_ob X)).
    apply PLT.compose_mono. auto.
    transitivity (liftPPLT@(id (forgetPLT (liftPPLT X)))).
    apply liftPPLT_mono.
    apply adj_counit_inv_le.
    rewrite Functor.ident; auto.
    rewrite (cat_ident2 (adj_unit_hom _)). auto.
    auto.        
  Qed.    

  Lemma strictify_largest : forall q, liftPPLT@q ≤ f -> q ≤ strictify.
  Proof.
    intros.
    unfold strictify.
    transitivity (adj_counit Y ∘ forgetPLT@(liftPPLT@q) ∘ adj_counit_inv_hom X).
    transitivity (adj_counit Y ∘ adj_counit_inv_hom Y ∘ q).
    rewrite (adj_counit_inv_eq Y).
    rewrite (cat_ident2 q). auto.
    rewrite <- (cat_assoc (adj_counit Y)).
    rewrite <- (cat_assoc (adj_counit Y)).
    apply PPLT.compose_mono; auto.
    apply adj_counit_inv_ntish. 
    rewrite <- (cat_assoc (adj_counit Y)).
    rewrite <- (cat_assoc (adj_counit Y)).
    apply PPLT.compose_mono; auto.
    apply PPLT.compose_mono; auto.
  Qed.    
End strictify.
