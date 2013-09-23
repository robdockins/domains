Require Import Setoid.

Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import directed.
Require Import plotkin.
Require Import joinable.
Require Import approx_rels.
Require Import cpo.

Module PLT.
Section PLT.
  Variable hf:bool.

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
  Canonical Structure dec (X:ob) := eff_to_ord_dec (ord X) (effective X).
  
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
    Hom A A 
       (ident_rel (effective A))
       (ident_ordering (ord A) (effective A))
       (ident_image_dir hf (ord A) (effective A)).

  Program Definition compose (A B C:ob) (g:hom B C) (f:hom A B) : hom A C :=
    Hom A C (compose_rel (effective B) g f) _ _.
  Next Obligation.
    intros A B C g f. 
    apply compose_ordering. apply hom_order. apply hom_order.
  Qed.
  Next Obligation.
    intros A B C g f. apply compose_directed. 
    apply hom_order. apply hom_order.
    apply hom_directed. apply hom_directed.
  Qed.

  Definition comp_mixin : Comp.mixin_of ob hom
    := Comp.Mixin ob hom ident compose.
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
  
  Definition sum (A B:ob) : ob :=
    Ob (sum_preord (ord A) (ord B))
       (Class _
         (Preord.mixin (sum_preord (ord A) (ord B)))
         (effective_sum (effective A) (effective B))
         (plotkin_sum hf (ord A) (ord B) (effective A) (effective B)
             (plotkin A) (plotkin B))
         ).
  Canonical Structure sum.

  Definition exp (A B:ob) : ob :=
    Ob (joinable_relation hf (ord A) (ord B))
       (Class _
         (joinable_rel_ord_mixin hf (ord A) (ord B))
         (joinable_rel_effective hf (ord A) (ord B) (effective A) (effective B) (plotkin A))
         (joinable_rel_plt hf (ord A) (ord B) (effective A) (plotkin A) (effective B) (plotkin B))).
  Canonical Structure exp.

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

  Canonical Structure PLT : category := Category ob hom cat_class.


  Theorem pair_universal C A B (f:hom C A) (g:hom C B) (PAIR:hom C (prod A B)) :
    pi1 ∘ PAIR ≈ f -> pi2 ∘ PAIR ≈ g -> PAIR ≈ pair f g.
  Proof.
    apply (pair_rel_universal hf).
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
    intro. apply (curry_universal hf); auto.
    apply (hom_directed _ _ f).
    apply plotkin.
    apply (hom_order _ _ CURRY).
    apply (hom_directed _ _ CURRY).
    rewrite pair_map_eq in H. apply H.
  Qed.

  
  Section homset_cpo.
    Variables A B:ob.

    Program Definition hom_rel' : hom_ord A B → erel (ord A) (ord B) :=
      Preord.Hom (hom_ord A B) (erel (ord A) (ord B)) (@hom_rel A B) _.
    Next Obligation. simpl. auto. Qed.

    Program Definition homset_sup (M:cl_eset (directed_hf_cl hf) (hom_ord A B)) 
      : hom A B := Hom A B (∪(image hom_rel' M)) _ _.
    Next Obligation.
      intros. apply union_axiom in H1. apply union_axiom.
      destruct H1 as [X [??]].
      exists X. split; auto.
      apply image_axiom2 in H1.
      destruct H1 as [Y [??]].
      rewrite H3. simpl.
      apply hom_order with x y; auto.
      rewrite H3 in H2. auto.
    Qed.
    Next Obligation.
      intros. red. intro x.
      apply prove_directed.
      generalize (refl_equal hf).
      pattern hf at 2. case hf; intros.
      pattern hf at 1. rewrite H; auto.
      pattern hf at 1. rewrite H; auto.
      destruct M as [M HM]; simpl in *.
      destruct (HM nil) as [q [??]].
      rewrite H. hnf; auto.
      hnf; intros. apply nil_elem in H0. elim H0.
      destruct (hom_directed A B q x nil) as [z [??]].
      rewrite H. hnf. auto.
      hnf; intros. apply nil_elem in H2. elim H2.
      apply erel_image_elem in H3.
      exists z. apply erel_image_elem.
      apply union_axiom.
      exists (hom_rel q). split; auto.
      apply image_axiom1'; eauto.
      exists q. split; auto.
      
      intros y1 y2. intros.
      apply erel_image_elem in H.
      apply erel_image_elem in H0.
      apply union_axiom in H.      
      apply union_axiom in H0.
      destruct H as [X1 [??]].
      destruct H0 as [X2 [??]].
      apply image_axiom2 in H.
      destruct H as [Y1 [??]].
      apply image_axiom2 in H0.
      destruct H0 as [Y2 [??]].
      destruct M as [M HM]; simpl in *.
      destruct (HM (Y1::Y2::nil)%list) as [Y [??]].
      apply elem_inh with Y1. apply cons_elem; auto.
      hnf; intros.
      apply cons_elem in H5.
      destruct H5. rewrite H5; auto.
      apply cons_elem in H5.
      destruct H5. rewrite H5; auto.
      apply nil_elem in H5. elim H5.
      destruct (hom_directed A B Y x (y1::y2::nil)%list) as [z [??]].
      apply elem_inh with y1; auto. apply cons_elem; auto.
      hnf; intros.
      apply cons_elem in H7. destruct H7.
      rewrite H7. apply erel_image_elem.
      assert (Y1 ≤ Y). apply H5. apply cons_elem. auto.
      apply H8. rewrite <- H3. auto.
      assert (Y2 ≤ Y). apply H5. apply cons_elem. right.
      apply cons_elem. auto.
      apply cons_elem in H7. destruct H7.
      rewrite H7. apply erel_image_elem.
      apply H8. rewrite <- H4. auto.
      apply nil_elem in H7. elim H7.
      apply erel_image_elem in H8.
      exists z.
      split.
      apply H7. apply cons_elem; auto.
      split.
      apply H7. apply cons_elem; right. apply cons_elem; auto.
      apply erel_image_elem.
      apply union_axiom.
      exists (hom_rel Y). split; auto.
      apply image_axiom1'. exists Y; split; auto.
    Qed.

    Program Definition homset_cpo_mixin : 
      CPO.mixin_of (directed_hf_cl hf) (hom_ord A B)
      := CPO.Mixin _ _ homset_sup _ _.
    Next Obligation.
      repeat intro; simpl.
      apply union_axiom.
      exists (hom_rel x). split; auto.
      apply image_axiom1'. exists x. split; auto.
    Qed.
    Next Obligation.
      repeat intro.
      simpl in H0.
      apply union_axiom in H0.
      destruct H0 as [Q [??]].
      apply image_axiom2 in H0.
      destruct H0 as [y [??]].
      generalize (H y H0); intros.
      apply H3.
      rewrite H2 in H1. auto.
    Qed.

    Definition homset_cpo : CPO.type (directed_hf_cl hf) :=
      CPO.Pack _ (hom A B) (hom_ord_mixin A B) homset_cpo_mixin.
  End homset_cpo.
End PLT.
End PLT.

Notation PLT := PLT.PLT.
Canonical Structure PLT.
Canonical Structure PLT.ord.
Canonical Structure PLT.dec.
Canonical Structure PLT.hom_ord.
Canonical Structure PLT.hom_eq.
Canonical Structure PLT.comp.
Canonical Structure PLT.prod.
Canonical Structure PLT.homset_cpo.

Arguments PLT.hom [hf] A B.
Arguments PLT.hom_rel [hf] [A] [B] h n.
Arguments PLT.effective [hf] X.
Arguments PLT.plotkin [hf] X.
Arguments PLT.ord [hf] X.
Arguments PLT.dec [hf] X.
Arguments PLT.pi1 [hf] [A] [B].
Arguments PLT.pi2 [hf] [A] [B].
Arguments PLT.pair [hf] [C] [A] [B] f g.
Arguments PLT.prod [hf] A B.
Arguments PLT.exp [hf] A B.
Arguments PLT.app [hf] A B.
Arguments PLT.curry [hf] C A B f.

Coercion PLT.ord : PLT.ob >-> preord.
Coercion PLT.carrier : PLT.ob >-> Sortclass.



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

Definition empty_plt hf : ob (PLT hf) :=
  PLT.Ob hf False (PLT.Class _ _ (Preord.mixin emptypo) empty_eff (empty_plotkin hf)).

Record embedding (hf:bool) (A B:PLT.ob hf) :=
  Embedding
  { embed_map :> A -> B
  ; embed_mono : forall a a', a ≤ a' -> embed_map a ≤ embed_map a'
  ; embed_reflects : forall a a', embed_map a ≤ embed_map a' -> a ≤ a'
  ; embed_directed0 : forall y,
      if hf then True else exists x, embed_map x ≤ y
  ; embed_directed2 : forall y a b,
      embed_map a ≤ y ->
      embed_map b ≤ y ->
      exists c, embed_map c ≤ y /\ a ≤ c /\ b ≤ c
  }.
Arguments embed_map [hf] [A] [B] e a.
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
  Embedding hf A C (fun x => embed_map g (embed_map f x)) _ _ _ _.
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
  transitivity (embed_map g q); auto.
  apply embed_mono. auto.
Qed.
Next Obligation.
  intros.
  destruct (embed_directed2 g y (embed_map f a) (embed_map f b)) as [c [?[??]]]; auto.
  destruct (embed_directed2 f c a b) as [q [?[??]]]; auto.
  exists q. split; auto.
  transitivity (embed_map g c); auto.
  apply embed_mono; auto.
Qed.
  
Definition embed_order hf A B (E G:embedding hf A B) :=
  forall x, embed_map E x ≤ embed_map G x.

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
  Preord.Hom A B (embed_map E) (embed_mono E).
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
  transitivity (embed_map f' (embed_map g x)).
  destruct H. apply H.
  apply embed_mono.  
  destruct H0. apply H0.
  transitivity (embed_map f' (embed_map g x)).
  apply embed_mono.
  destruct H0. apply H1.
  destruct H. apply H1.
Qed.

Definition EMBED hf :=
  Category (PLT.ob hf) (embedding hf) (embed_cat_class hf).

Notation "A ⇀ B" := (hom (EMBED _) A B) (at level 70, no associativity).

Add Parametric Morphism hf A B :
  (@embed_map hf A B) with signature
        (@Preord.ord_op (embed_ord hf A B)) ==>
        (@Preord.ord_op A) ==>
        (@Preord.ord_op B)
    as embed_map_morphism.
Proof.
  intros.
  transitivity (y x0).
  apply H. apply embed_mono. auto.
Qed.

Add Parametric Morphism hf A B :
  (@embed_map hf A B) with signature
        (@eq_op (CAT_EQ (EMBED hf) A B)) ==>
        (@eq_op (Preord_Eq A)) ==>
        (@eq_op (Preord_Eq B))
    as embed_map_eq_morphism.
Proof.
  intros. split; apply embed_map_morphism; auto.
Qed.

Lemma embed_unlift hf (A B:PLT.ob hf) (f g:A ⇀ B) x :
  f ≤ g -> f x ≤ g x.
Proof.
  intros. apply H; auto.
Qed.

Lemma embed_unlift' hf (A B:PLT.ob hf) (f g:A ⇀ B) x :
  f ≈ g -> f x ≈ g x.
Proof.
  intros. 
  destruct H; split; auto.
Qed.

Lemma embed_lift hf (A B:PLT.ob hf) (f g:A ⇀ B) :
  (forall x, f x ≤ g x) -> f ≤ g.
Proof.
  repeat intro; auto.
Qed.  

Lemma embed_lift' hf (A B:PLT.ob hf) (f g:A ⇀ B) :
  (forall x, f x ≈ g x) -> f ≈ g.
Proof.
  intros; split; hnf; auto.
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


Section ep_pairs.
  Variable hf:bool.

  Notation PLT := (PLT hf).

  Record is_ep_pair (X Y:ob PLT) (e:X → Y) (p:Y → X) :=
  IsEP
  { pe_ident : p ∘ e ≈ id
  ; ep_ident : e ∘ p ≤ id
  }.

  Record ep_pair (X Y:ob PLT) :=
  EpPair
  { embed : X → Y
  ; project : Y → X
  ; ep_correct : is_ep_pair X Y embed project
  }.
  Arguments embed [X] [Y] e.
  Arguments project [X] [Y] e.

  Program Definition ep_id (X:ob PLT) : ep_pair X X :=
    EpPair X X id id _.
  Next Obligation.
    intros. constructor.
    rewrite (cat_ident1 id(X)); auto.
    rewrite (cat_ident1 id(X)); auto.
  Qed.

  Program Definition ep_compose (X Y Z:ob PLT) (g:ep_pair Y Z) (f:ep_pair X Y) :=
    EpPair X Z (embed g ∘ embed f) (project f ∘ project g) _.
  Next Obligation.
    intros.
    destruct g as [e' p' [??]].
    destruct f as [e p [??]]. simpl in *.
    constructor.
    rewrite <- (cat_assoc p).
    rewrite (cat_assoc p').
    rewrite pe_ident0.
    rewrite (cat_ident2 e). auto.
    
    rewrite <- (cat_assoc e').
    rewrite (cat_assoc e).
    transitivity (e' ∘ p'); auto.
    apply PLT.compose_mono; auto.
    transitivity (id ∘ p').
    apply PLT.compose_mono; auto.
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
    transitivity ((p' ∘ e') ∘ p).
    apply PLT.compose_mono; auto.
    rewrite <- H1.
    rewrite <- (cat_assoc p').
    transitivity (p' ∘ id).
    apply PLT.compose_mono.
    destruct H. auto.
    auto.
    rewrite (cat_ident1 p'). auto.
    transitivity (id ∘ p').
    rewrite (cat_ident2 p'). auto.
    destruct H.
    transitivity ((p ∘ e) ∘ p').
    apply PLT.compose_mono; auto.
    rewrite H1.
    rewrite <- (cat_assoc p).
    transitivity (p ∘ id).
    apply PLT.compose_mono.
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
    
  Definition ep_pair_comp_mixin : Comp.mixin_of (PLT.ob hf) ep_pair :=
    Comp.Mixin _ ep_pair ep_id ep_compose.

  Canonical Structure ep_pair_eq X Y := Eq.Pack (ep_pair X Y) (ep_pair_eq_mixin X Y).
  Canonical Structure ep_pair_comp := Comp.Pack _ ep_pair ep_pair_comp_mixin.

  Lemma ep_cat_axioms :
    Category.category_axioms _ ep_pair ep_pair_eq_mixin ep_pair_comp_mixin.
  Proof.  
    constructor; simpl; intros.
    red. simpl. apply (cat_ident1 (embed f)).
    red. simpl. apply (cat_ident2 (embed f)).
    red. simpl. apply (cat_assoc (embed f)).
    red. simpl. apply (cat_respects H H0).
  Qed.

  Definition ep_cat_class : Category.class_of _ ep_pair :=
    Category.Class _ ep_pair ep_pair_eq_mixin ep_pair_comp_mixin ep_cat_axioms.

  Canonical Structure PLT_EP :=
    Category (PLT.ob hf) ep_pair ep_cat_class.

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
    Variables X Y:ob PLT.
    Variable ep : ep_pair X Y.

    Let e := embed ep.
    Let p := project ep.
    Let Hep := ep_correct X Y ep.

    Section embed_func.
      Variable x:X.

      Lemma ep_semidec : semidec (fun y => (x,y) ∈ PLT.hom_rel e /\ (y,x) ∈ PLT.hom_rel p).
      Proof.
        apply semidec_conj.
        apply semidec_iff with (fun y => y ∈ erel_image (PLT.ord X) (PLT.ord Y) (PLT.dec X) 
          (PLT.hom_rel e) x).
        intros. apply erel_image_elem.
        apply semidec_in. apply PLT.dec.
        apply semidec_iff with (fun y => y ∈ erel_inv_image (PLT.ord Y) (PLT.ord X) (PLT.dec X) 
          (PLT.hom_rel p) x).
        intros. apply erel_inv_image_elem.
        apply semidec_in. apply PLT.dec.
      Qed.

      Definition embed_image :=
        esubset (fun y => (x,y) ∈ PLT.hom_rel e /\ (y,x) ∈ PLT.hom_rel p)
           ep_semidec 
           (eff_enum (PLT.ord Y) (PLT.effective Y)).

      Lemma embed_image_inhabited : einhabited embed_image.
      Proof.
        apply member_inhabited.
        generalize (pe_ident _ _ _ _ Hep).
        intros.
        assert ((x,x) ∈ PLT.hom_rel (p ∘ e)).
        apply H.
        apply ident_elem. auto.
        simpl in H0.
        apply compose_elem in H0.
        2: apply PLT.hom_order.
        destruct H0 as [y [??]].
        exists y. unfold embed_image.
        apply esubset_elem.
        split.
        apply eff_complete.
        split; auto.
      Qed.
    End embed_func.  
    
    Program Definition ep_embed : Preord.hom (PLT.ord X) (PLT.ord Y) :=
      Preord.Hom X Y 
        (fun x => choose' (PLT.ord Y) (embed_image x) (embed_image_inhabited x)) _.
    Next Obligation.
      intros.
      unfold choose'.
      destruct (find_inhabitant' (PLT.ord Y) (embed_image a) (embed_image_inhabited a))
        as [y ?]. simpl.
      destruct (find_inhabitant' (PLT.ord Y) (embed_image b) (embed_image_inhabited b))
        as [y' ?]. simpl.

      unfold embed_image in *.
      apply esubset_elem in m.
      apply esubset_elem in m0.
      destruct m as [_ [??]].
      destruct m0 as [_ [??]]. 
      destruct Hep.
      cut ((y',y) ∈ PLT.hom_rel id).
      intros. simpl in H4.
      apply ident_elem in H4. auto.
      apply ep_ident0.
      simpl.
      apply compose_elem; auto.
      apply PLT.hom_order.
      exists a. split; auto.
      apply PLT.hom_order with y' b; auto.
    Qed.

    Lemma embed_func_reflects : forall x x',
      ep_embed#x ≤ ep_embed#x' -> x ≤ x'.
    Proof.
      intros x x'. unfold ep_embed. simpl. unfold choose'.
      destruct (find_inhabitant' (PLT.ord Y) (embed_image x) (embed_image_inhabited x))
        as [y ?]. simpl.
      destruct (find_inhabitant' (PLT.ord Y) (embed_image x') (embed_image_inhabited x'))
        as [y' ?]. simpl.
      intros.
      unfold embed_image in *.
      apply esubset_elem in m.
      apply esubset_elem in m0.
      destruct m. destruct m0.
      destruct Hep.
      cut ((x',x) ∈ PLT.hom_rel id).
      simpl; intros. apply ident_elem in H4. auto.
      apply pe_ident0.
      simpl. apply compose_elem.
      apply PLT.hom_order.
      exists y'. intuition.
      apply PLT.hom_order with y x; auto.
    Qed.

    Lemma embed_func_directed0 : forall y,
      if hf then True else exists x, ep_embed#x ≤ y.
    Proof.
      intros.
      generalize (refl_equal hf).
      pattern hf at 2; case hf; intros.
      pattern hf at 1; rewrite H; auto.
      destruct (PLT.hom_directed _ _ _ p y nil).
      hnf.
      pattern hf at 1. rewrite H. auto.
      hnf; intros. apply nil_elem in H0. elim H0.
      destruct H0.
      pattern hf at 1. rewrite H.
      exists x. apply erel_image_elem in H1.
      unfold embed_func; simpl.
      unfold choose'.
      destruct (find_inhabitant' (PLT.ord Y) (embed_image x) (embed_image_inhabited x))
        as [y' ?]. simpl in *.
      unfold embed_image in m.
      apply esubset_elem in m.
      destruct m as [_ [??]].
      destruct Hep.
      cut ((y,y') ∈ PLT.hom_rel id).
      simpl; auto.
      intros. apply ident_elem in H4. auto.
      apply ep_ident0.
      simpl. apply compose_elem.
      apply PLT.hom_order.
      exists x; auto.
    Qed.

    Lemma embed_func_directed2 : forall y, forall a b,
      ep_embed#a ≤ y ->
      ep_embed#b ≤ y ->
      exists c, ep_embed#c ≤ y /\ a ≤ c /\ b ≤ c.
    Proof.
      intro. intros.
      unfold ep_embed in *. simpl in *.
      unfold choose' in *.
      destruct (find_inhabitant' (PLT.ord Y) (embed_image a) (embed_image_inhabited a))
        as [ya ?]. simpl in *.
      destruct (find_inhabitant' (PLT.ord Y) (embed_image b) (embed_image_inhabited b))
        as [yb ?]. simpl in *.
      unfold embed_image in m.
      unfold embed_image in m0.
      apply esubset_elem in m.
      apply esubset_elem in m0.
      destruct m as [_ [??]].
      destruct m0 as [_ [??]].
      assert ((y,a) ∈ PLT.hom_rel p).
      apply PLT.hom_order with ya a; auto.
      assert ((y,b) ∈ PLT.hom_rel p).
      apply PLT.hom_order with yb b; auto.
      destruct (PLT.hom_directed _ _ _ p y (a::b::nil)%list).
      apply elem_inh with a. apply cons_elem; auto.
      hnf; simpl; intros.
      apply erel_image_elem.
      apply cons_elem in H7. destruct H7.
      apply PLT.hom_order with y a; auto.
      apply cons_elem in H7. destruct H7.
      apply PLT.hom_order with y b; auto.
      apply nil_elem in H7. elim H7.
      destruct H7.
      apply erel_image_elem in H8.
      rename x into q.
      exists q.
      split.
      destruct (find_inhabitant' (PLT.ord Y) (embed_image q) (embed_image_inhabited q))
        as [yq ?]. simpl in *.
      unfold embed_image in m.
      apply esubset_elem in m.
      destruct m as [_ [??]].
      destruct Hep.
      cut ((y,yq) ∈ PLT.hom_rel id).
      simpl; intros. apply ident_elem in H11. auto.
      apply ep_ident0.
      simpl.
      apply compose_elem.
      apply PLT.hom_order.
      exists q. split; auto.
      split; apply H7; auto.
      apply cons_elem; auto.
      apply cons_elem; right.
      apply cons_elem; auto.
    Qed.

    Definition ep_embedding : embedding hf X Y :=
      Embedding hf X Y 
        (Preord.map _ _ ep_embed)
        (Preord.axiom _ _ ep_embed)
        embed_func_reflects
        embed_func_directed0
        embed_func_directed2.

  End ep_pair_embed_func.

  Section embed_func_ep_pair.
    Variables X Y:ob PLT.
    Variable embed : embedding hf X Y.

    Definition project_rel :=
      esubset_dec (Y×X)
         (fun yx => fst yx ≥ embed#(snd yx))
         (fun yx => eff_ord_dec Y (PLT.effective Y) (embed#(snd yx)) (fst yx))
         (eprod (eff_enum Y (PLT.effective Y)) (eff_enum X (PLT.effective X))).

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
      apply eprod_elem; split; apply eff_complete; auto.
      unfold project_rel in H.
      apply esubset_dec_elem in H.
      destruct H; auto.
      intros.
      change (fst y0) with (π₁#y0).
      change (snd y0) with (π₂#y0).
      rewrite <- H0. auto.
    Qed.

    Program Definition project_hom : Y → X :=
      PLT.Hom hf Y X project_rel _ _.
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
      generalize (refl_equal hf). pattern hf at 2. case hf; intros.
      pattern hf at 1. rewrite H. auto.
      pattern hf at 1. rewrite H.
      generalize (embed_directed0 embed y).
      rewrite H at 1.
      intros [x ?].
      exists x.
      apply erel_image_elem.
      apply project_rel_elem. auto.
      
      intros.
      apply erel_image_elem in H.
      apply erel_image_elem in H0.
      apply project_rel_elem in H.
      apply project_rel_elem in H0.
      destruct (embed_directed2 embed y x y0) as [z [?[??]]]; auto.
      exists z; split; auto. split; auto.
      apply erel_image_elem.
      apply project_rel_elem. auto.
    Qed.      

    Definition embed_rel :=
      esubset_dec (X×Y)
         (fun xy => embed#(fst xy) ≥ snd xy)
         (fun xy => eff_ord_dec Y (PLT.effective Y) (snd xy) (embed#(fst xy)))
         (eprod (eff_enum X (PLT.effective X)) (eff_enum Y (PLT.effective Y))).

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
      apply eprod_elem; split; apply eff_complete; auto.
      unfold embed_rel in H.
      apply esubset_dec_elem in H.
      destruct H; auto.
      intros.
      change (fst y0) with (π₁#y0).
      change (snd y0) with (π₂#y0).
      rewrite <- H0. auto.
    Qed.

    Program Definition embed_hom : X → Y :=
      PLT.Hom hf X Y embed_rel _ _.
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
      exists (embed#(x:X)).
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
      apply (embed_reflects embed).
      transitivity y; auto.

      hnf; simpl; intros.
      destruct a as [x x'].
      apply ident_elem in H.
      apply compose_elem.
      apply embed_hom_obligation_1.
      exists (embed#(x:X)).
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

    Definition embed_ep_pair := 
      EpPair X Y embed_hom project_hom embed_func_is_ep_pair.
      
  End embed_func_ep_pair.

  Arguments ep_embedding [X] [Y] ep.
  Arguments embed_ep_pair [X] [Y] _.

  Lemma embed_ep_roundtrip1 : forall X Y (ep:ep_pair X Y),
    embed_ep_pair (ep_embedding ep) ≈ ep.
  Proof.
    intros. split; hnf; simpl; intros.
    destruct a.
    apply embed_rel_elem in H.
    simpl in H.
    unfold choose' in H.
    match goal with [ _ : appcontext[find_inhabitant' ?A ?X ?Y] |- _ ] =>
      destruct (find_inhabitant' A X Y); simpl in *
    end.
    unfold embed_image in m.
    apply esubset_elem in m.
    destruct m as [?[??]].
    apply PLT.hom_order with c x; auto.
    destruct a.
    apply embed_rel_elem.
    simpl. unfold choose'.
    match goal with [ |- appcontext[find_inhabitant' ?A ?X ?Y] ] =>
      destruct (find_inhabitant' A X Y); simpl in *
    end.
    unfold embed_image in m.
    apply esubset_elem in m. intuition.
    cut ((x,c0) ∈ PLT.hom_rel id).
    simpl; intros. apply ident_elem in H1. auto.
    generalize (ep_correct X Y ep). intros [??].
    apply ep_ident0. simpl.
    apply compose_elem. apply PLT.hom_order.
    eauto.
  Qed.

  Lemma embed_ep_roundtrip2 : forall X Y (e : X ⇀ Y),
    e ≈ ep_embedding (embed_ep_pair e).
  Proof.
    intros. split; hnf; simpl; intros.
    unfold choose'.
    match goal with [ |- appcontext[find_inhabitant' ?A ?X ?Y] ] =>
      destruct (find_inhabitant' A X Y); simpl in *
    end.
    unfold embed_image in m.
    apply esubset_elem in m.
    intuition.
    unfold embed_hom in H1.
    simpl in *.
    apply embed_rel_elem in H1.
    apply project_rel_elem in H2.
    simpl in *; auto.
    unfold choose'.
    match goal with [ |- appcontext[find_inhabitant' ?A ?X ?Y] ] =>
      destruct (find_inhabitant' A X Y); simpl in *
    end.
    unfold embed_image in m.
    apply esubset_elem in m.
    intuition.
    simpl in *.
    apply embed_rel_elem in H1.
    auto.
  Qed.
End ep_pairs.

Arguments embed [hf] [X] [Y] e.
Arguments project [hf] [X] [Y] e.
Arguments ep_embedding [hf] [X] [Y] ep.
Arguments embed_ep_pair [hf] [X] [Y] _.

Canonical Structure PLT_EP.
Canonical Structure ep_pair_eq.
Canonical Structure ep_pair_comp.
