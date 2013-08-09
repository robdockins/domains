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

  Program Definition hom_ord_mixin (A B:ob) : Preord.mixin_of (hom A B) :=
    Preord.Mixin (hom A B) (fun f g => hom_rel f ≤ hom_rel g) _ _.
  Solve Obligations of hom_ord_mixin using (intros; eauto).
  
  Canonical Structure hom_ord (A B:ob) := Preord.Pack (hom A B) (hom_ord_mixin A B).

  Definition hom_eq_mixin (A B:ob) := Preord.ord_eq (hom_ord A B).
  Canonical Structure hom_eq (A B:ob) := Eq.Pack (hom A B) (hom_eq_mixin A B).

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

  Lemma cat_axioms : Category.category_axioms ob hom hom_eq_mixin comp_mixin.
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
    Category.Class ob hom hom_eq_mixin comp_mixin cat_axioms.

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

  Definition app {A B} : hom (prod (exp A B) A) B :=
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

  Definition pair {C A B} (f:hom C A) (g:hom C B) : hom C (prod A B) :=
    Hom C (prod A B) 
      (pair_rel (effective C) f g)
      (pair_rel_ordering _ _ _ (effective C) f g (hom_order _ _ f) (hom_order _ _ g))
      (pair_rel_dir _ _ _ (effective C) f g 
        (hom_order _ _ f) (hom_order _ _ g)
        (hom_directed _ _ f) (hom_directed _ _ g)).

  Definition pi1 {A B} : hom (prod A B) A :=
    Hom (prod A B) A 
      (pi1_rel (effective A) (effective B))
      (pi1_rel_ordering _ _ (effective A) (effective B))
      (pi1_rel_dir _ _ (effective A) (effective B)).

  Definition pi2 {A B} : hom (prod A B) B :=
    Hom (prod A B) B 
      (pi2_rel (effective A) (effective B))
      (pi2_rel_ordering _ _ (effective A) (effective B))
      (pi2_rel_dir _ _ (effective A) (effective B)).

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
    repeat intro.
    destruct (hom_directed _ _ f (fst x) (image π₁ M)).
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
    apply pair_rel_universal.
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
    intro. apply curry_universal; auto.
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
