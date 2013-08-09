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

Module PLT.
  Record class_of (A:Type) :=
    Class
    { cls_preord : Preord.mixin_of A
    ; cls_ord := Preord.Pack A cls_preord
    ; cls_effective : effective_order cls_ord
    ; cls_plotkin : plotkin_order cls_ord
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
    ; hom_directed : directed_rel (ord A) (ord B) (effective A) hom_rel
    }.
  Arguments hom_rel [A] [B] h n.

  Program Definition eq_mixin (A B:ob) : Eq.mixin_of (hom A B) :=
    Eq.Mixin (hom A B) (fun f g => hom_rel f ≈ hom_rel g) _ _ _.
  Solve Obligations of eq_mixin using (intros; eauto).

  Canonical Structure eq (A B:ob) := Eq.Pack (hom A B) (eq_mixin A B).


  Definition ident (A:ob) : hom A A :=
    Hom A A (ident_rel (effective A))
            (ident_ordering (ord A) (effective A))
            (ident_image_dir (ord A) (effective A)).

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

  Lemma cat_axioms : Category.category_axioms ob hom (eq_mixin) (comp_mixin).
  Proof.
    constructor.

    intros. apply compose_ident_rel2. apply hom_order.
    intros. apply compose_ident_rel1. apply hom_order.
    intros. apply compose_assoc.
    intros. unfold comp_op. simpl.
    unfold compose. red. simpl.
    split; hnf; intros [??] ?.
    apply compose_elem in H1.
    destruct H1 as [y [??]].
    apply compose_elem.
    apply hom_order.
    exists y; split.
    destruct H0.
    apply H0. auto.
    destruct H. apply H; auto.
    apply hom_order.
    apply compose_elem in H1.
    destruct H1 as [y [??]].
    apply compose_elem.
    apply hom_order.
    exists y. split.
    destruct H0. apply H3. auto.
    destruct H. apply H3; auto.
    apply hom_order.
  Qed.

  Definition cat_class : Category.class_of ob hom :=
    Category.Class ob hom eq_mixin comp_mixin cat_axioms.


  Definition prod (A B:ob) : ob :=
    Ob (carrier A * carrier B)
       (Class _ 
         (Preord.mixin (ord A × ord B))
         (effective_prod (effective A) (effective B))
         (plotkin_prod (ord A) (ord B) (effective A) (effective B) (plotkin A) (plotkin B))).
  Canonical Structure prod.
  
  Definition exp (A B:ob) : ob :=
    Ob (joinable_relation (ord A) (ord B))
       (Class _
         (joinable_rel_ord_mixin (ord A) (ord B))
         (joinable_rel_effective (ord A) (ord B) (effective A) (effective B) (plotkin A))
         (joinable_rel_plt (ord A) (ord B) (effective A) (plotkin A) (effective B) (plotkin B))).

  Definition app A B : hom (prod (exp A B) A) B :=
    Hom (prod (exp A B) A) B
      (apply_rel (ord A) (ord B) (effective A) (effective B) (plotkin A))
      (apply_rel_ordering (ord A) (ord B) (effective A) (effective B) (plotkin A))
      (apply_rel_dir (ord A) (ord B) (effective A) (effective B) (plotkin A)).
 
  Definition curry {C A B} (f:hom (prod C A) B) : hom C (exp A B) :=
    Hom C (exp A B)
      (curry_rel (ord A) (ord B) (ord C)
        (effective A) (effective B) (effective C) (plotkin A) 
        f (hom_order _ _ f))
      (curry_rel_ordering (ord A) (ord B) (ord C)
        (effective A) (effective B) (effective C) (plotkin A) 
        f (hom_order _ _ f))
      (curry_rel_dir (ord A) (ord B) (ord C)
        (effective A) (effective B) (effective C) (plotkin A) 
        f (hom_order _ _ f) (hom_directed _ _ f)
        (plotkin B)).

  Program Definition pair_map {A B C D} (f:hom A C) (g:hom B D) : hom (prod A B) (prod C D) :=
    Hom (prod A B) (prod C D) (pair_rel' f g) _ _.
  Next Obligation.
    unfold pair_rel'; intros.
    apply image_axiom2 in H1.
    destruct H1 as [q [??]].
    destruct q as [[a c][b d]].
    simpl in H2.
    destruct x. destruct y.
    destruct x'. destruct y'.
    change (c4,c5,(c6,c7)) with
       ((mk_pair (mk_pair (π₁ ∘ π₁) (π₁ ∘ π₂)) (mk_pair (π₂ ∘ π₁) (π₂ ∘ π₂)))#
         (((c4,c6),(c5,c7)) : ((ord A×ord C)×(ord B×ord D)))).
    apply image_axiom1.
    apply elem_eprod in H1.
    apply elem_eprod.
    destruct H1; split.
    apply hom_order with a c; auto.
    transitivity c0; auto.
    destruct H2. destruct H4. destruct H4; auto.
    destruct H; auto.
    transitivity c2.
    destruct H0; auto.
    destruct H2.
    destruct H2.
    destruct H5; auto.
    apply hom_order with b d; auto.
    transitivity c1.
    destruct H; auto.
    destruct H2. destruct H5. destruct H5; auto.
    destruct H; auto.
    transitivity c3.
    destruct H0; auto.
    destruct H2.
    destruct H2. destruct H5; auto.
  Qed.
  Next Obligation.
    repeat intro.
    destruct x as [a b].
    destruct (hom_directed A C f a (image π₁ M)).
    red; intros.
    apply image_axiom2 in H0.
    destruct H0 as [[p q] [??]]. simpl in H1. rewrite H1.
    apply erel_image_elem.
    apply H in H0.
    apply erel_image_elem in H0.
 admit.
    destruct (hom_directed B D g b (image π₂ M)).
    red; intros.
    apply image_axiom2 in H1.
    destruct H1 as [[p q] [??]]. simpl in H2. rewrite H2.
    apply erel_image_elem.
    apply H in H1.
    apply erel_image_elem in H1.
admit.    
    exists (x,x0).
    split.
    red; intros.
    split; simpl.
    destruct H0. apply H0.
    change (fst x1) with (π₁#x1).
    apply image_axiom1. auto.
    destruct H1. apply H1.
    change (snd x1) with (π₂#x1).
    apply image_axiom1. auto.
    apply erel_image_elem.
    destruct H0. destruct H1.
    apply erel_image_elem in H2.
    apply erel_image_elem in H3.
admit.
  Qed.  

  Theorem curry_apply A B C (f:hom (prod C A) B) :
    app A B ∘ pair_map (curry f) (ident A) ≈ f.
  Proof.
    apply curry_apply. apply hom_directed. apply plotkin.
  Qed. 

End PLT.

Canonical Structure PLT.ord.
Canonical Structure PLT.dec.
Canonical Structure PLT.eq.
Canonical Structure PLT.prod.
Canonical Structure PLT.comp.

Canonical Structure PLT : category := Category PLT.ob PLT.hom PLT.cat_class.

