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

Program Definition plotkin_forget (A:preord)
  (HA:plotkin_order false A) : plotkin_order true A :=
  PlotkinOrder true A _ (mub_closure HA) _ _.
Next Obligation.
  repeat intro.
  apply (mub_complete HA M); simpl; auto.
Qed.
Next Obligation.
  intros. apply mub_clos_incl; auto.
Qed.
Next Obligation.
  repeat intro.
  apply (mub_clos_mub HA M) with M0; simpl; auto.
Qed.

Module PLT.
  Record class_of (A:Type) :=
    Class
    { cls_preord : Preord.mixin_of A
    ; cls_ord := Preord.Pack A cls_preord
    ; cls_effective : effective_order cls_ord
    ; cls_plotkin : plotkin_order false cls_ord
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
    ; hom_directed : directed_rel false (ord A) (ord B) (effective A) hom_rel
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
            (ident_image_dir false (ord A) (effective A)).

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
         (plotkin_prod false (ord A) (ord B) (effective A) (effective B) (plotkin A) (plotkin B))).
  Canonical Structure prod.
  
  Definition exp (A B:ob) : ob :=
    Ob (joinable_relation false (ord A) (ord B))
       (Class _
         (joinable_rel_ord_mixin false (ord A) (ord B))
         (joinable_rel_effective false (ord A) (ord B) (effective A) (effective B) (plotkin A))
         (joinable_rel_plt false (ord A) (ord B) (effective A) (plotkin A) (effective B) (plotkin B))).

  Definition app {A B} : hom (prod (exp A B) A) B :=
    Hom (prod (exp A B) A) B
      (apply_rel false (ord A) (ord B) (effective A) (effective B) (plotkin A))
      (apply_rel_ordering false (ord A) (ord B) (effective A) (effective B) (plotkin A))
      (apply_rel_dir false (ord A) (ord B) (effective A) (effective B) (plotkin A)).
 
  Definition curry {C A B} (f:hom (prod C A) B) : hom C (exp A B) :=
    Hom C (exp A B)
      (curry_rel false (ord A) (ord B) (ord C)
        (effective A) (effective B) (effective C) (plotkin A) 
        f (hom_order _ _ f))
      (curry_rel_ordering false (ord A) (ord B) (ord C)
        (effective A) (effective B) (effective C) (plotkin A) 
        f (hom_order _ _ f))
      (curry_rel_dir false (ord A) (ord B) (ord C)
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
  Record class_of (A:Type) :=
    Class
    { cls_preord : Preord.mixin_of A
    ; cls_ord := Preord.Pack A cls_preord
    ; cls_effective : effective_order cls_ord
    ; cls_plotkin : plotkin_order true cls_ord
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
    ; hom_directed : directed_rel true (ord A) (ord B) (effective A) hom_rel
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
            (ident_image_dir true (ord A) (effective A)).

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
         (plotkin_prod true (ord A) (ord B) (effective A) (effective B) (plotkin A) (plotkin B))).
  Canonical Structure prod.
  
  Definition exp (A B:ob) : ob :=
    Ob (joinable_relation true (ord A) (ord B))
       (Class _
         (joinable_rel_ord_mixin true (ord A) (ord B))
         (joinable_rel_effective true (ord A) (ord B) (effective A) (effective B) (plotkin A))
         (joinable_rel_plt true (ord A) (ord B) (effective A) (plotkin A) (effective B) (plotkin B))).

  Definition app {A B} : hom (prod (exp A B) A) B :=
    Hom (prod (exp A B) A) B
      (apply_rel true (ord A) (ord B) (effective A) (effective B) (plotkin A))
      (apply_rel_ordering true (ord A) (ord B) (effective A) (effective B) (plotkin A))
      (apply_rel_dir true (ord A) (ord B) (effective A) (effective B) (plotkin A)).
 
  Definition curry {C A B} (f:hom (prod C A) B) : hom C (exp A B) :=
    Hom C (exp A B)
      (curry_rel true (ord A) (ord B) (ord C)
        (effective A) (effective B) (effective C) (plotkin A) 
        f (hom_order _ _ f))
      (curry_rel_ordering true (ord A) (ord B) (ord C)
        (effective A) (effective B) (effective C) (plotkin A) 
        f (hom_order _ _ f))
      (curry_rel_dir true (ord A) (ord B) (ord C)
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

Definition forgetPLT_ob (X:PLT.ob) : PPLT.ob :=
  PPLT.Ob (PLT.carrier X) (PPLT.Class _
    (Preord.mixin (PLT.ord X))
    (PLT.effective X)
    (plotkin_forget _ (PLT.plotkin X))).

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
    (lift_plotkin _ _ _ (PPLT.plotkin X))).

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
  red; auto.
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
