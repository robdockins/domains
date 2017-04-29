(* Copyright (c) 2014, Robert Dockins *)

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
Require Import approx_rels.
Require Import profinite.

(**  * Basis embeddings and EP-pairs

     Here we define the category of embeddings over PLT.  These are used
     to construct the solutions to recursive domain equations.  Here
     we show that the category of basis embeddings is equivalant to
     the more usual category of embedding-projection pairs.  Basis
     embeddings are considerably more convenient to work with than EP-pairs, so
     we prefer them for building bilimits and proving functors continuous.

     Basis embeddings form a category with the effective Plotkin orders
     as objects.  To avoid notational confusion, we use the symbol ⇀
     to refer to embeddings, reserving → for the homs of PLT.
  *)

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
Solve Obligations with (simpl; intros; auto).
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
Solve Obligations with (unfold embed_order; intros; eauto).

Canonical Structure embed_ord hf A B :=
  Preord.Pack (embedding hf A B) (embed_order_mixin hf A B).

Definition embed_comp_mixin hf :=
    (Comp.Mixin _ _ (embed_ident hf) (embed_compose hf)).

Canonical Structure embed_comp hf :=
  Comp.Pack (PLT.ob hf) (embedding hf) (embed_comp_mixin hf).

Program Definition embed_func {hf A B} (E:embedding hf A B) : PLT.ord A → PLT.ord B :=
  Preord.Hom A B (embed_map E) (embed_mono E).
Coercion embed_func : embedding >-> hom.

Definition embed_eq_mixin hf A B := Preord.ord_eq (embed_ord hf A B).

Lemma embed_cat_axioms hf : 
  Category.axioms (PLT.ob hf) (embedding hf) (embed_eq_mixin hf) (embed_comp_mixin hf).
Proof.
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
  Category (PLT.ob hf) (embedding hf) _ _ (embed_cat_axioms hf).

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


(** The category of embeddings over _partial_ plotkin orders has
    an initial object.  The category of embeddings over total plotkin
    orders, however, does not.
 *)
Program Definition embed_initiate X : PLT.empty true ⇀ X :=
  Embedding true (PLT.empty true) X (fun x => False_rect _ x) _ _ _ _.
Solve Obligations of embed_initiate with (simpl; intros; trivial; elim a).

Program Definition PPLT_EMBED_initialized_mixin :=
  Initialized.Mixin
    (PLT.ob true)
    (embedding true)
    (embed_eq_mixin true)
    (PLT.empty true)
    embed_initiate
    _.
Next Obligation.
  repeat intro.
  split; intro x; elim x.
Qed.

Canonical Structure PPLT_EMBED_initialized :=
  Initialized 
    (PLT.ob true) (embedding true)
    (embed_eq_mixin true)
    (embed_comp_mixin true)
    (embed_cat_axioms true)
    PPLT_EMBED_initialized_mixin.


Section ep_pairs.
  Variable hf:bool.

  Notation PLT := (PLT.PLT hf).

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
    rewrite (cat_ident1 _ _ _ id(X)); auto.
    rewrite (cat_ident1 _ _ _ id(X)); auto.
  Qed.

  Program Definition ep_compose (X Y Z:ob PLT) (g:ep_pair Y Z) (f:ep_pair X Y) :=
    EpPair X Z (embed g ∘ embed f) (project f ∘ project g) _.
  Next Obligation.
    intros.
    destruct g as [e' p' [??]].
    destruct f as [e p [??]]. simpl in *.
    constructor.
    rewrite <- (cat_assoc _ _ _ _ _ p).
    rewrite (cat_assoc _ _ _ _ _ p').
    rewrite pe_ident0.
    rewrite (cat_ident2 _ _ _ e). auto.
    
    rewrite <- (cat_assoc _ _ _ _ _ e').
    rewrite (cat_assoc _ _ _ _ _ e).
    transitivity (e' ∘ p'); auto.
    apply PLT.compose_mono; auto.
    transitivity (id ∘ p').
    apply PLT.compose_mono; auto.
    rewrite (cat_ident2 _ _ _ p').
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
    rewrite (cat_ident2 _ _ _ p). auto.
    destruct H0.
    transitivity ((p' ∘ e') ∘ p).
    apply PLT.compose_mono; auto.
    rewrite <- H1.
    rewrite <- (cat_assoc _ _ _ _ _ p').
    transitivity (p' ∘ id).
    apply PLT.compose_mono.
    destruct H. auto.
    auto.
    rewrite (cat_ident1 _ _ _ p'). auto.
    transitivity (id ∘ p').
    rewrite (cat_ident2 _ _ _ p'). auto.
    destruct H.
    transitivity ((p ∘ e) ∘ p').
    apply PLT.compose_mono; auto.
    rewrite H1.
    rewrite <- (cat_assoc _ _ _ _ _ p).
    transitivity (p ∘ id).
    apply PLT.compose_mono.
    destruct H0. auto.
    auto.
    rewrite (cat_ident1 _ _ _ p). auto.
  Qed.

  Program Definition ep_pair_eq_mixin X Y : Eq.mixin_of (ep_pair X Y) :=
    Eq.Mixin _ (fun f g => embed f ≈ embed g) _ _ _.
  Solve Obligations of ep_pair_eq_mixin with (simpl; intros; eauto).
    
  Definition ep_pair_comp_mixin : Comp.mixin_of (PLT.ob hf) ep_pair :=
    Comp.Mixin _ ep_pair ep_id ep_compose.

  Canonical Structure ep_pair_eq X Y := Eq.Pack (ep_pair X Y) (ep_pair_eq_mixin X Y).
  Canonical Structure ep_pair_comp := Comp.Pack _ ep_pair ep_pair_comp_mixin.

  Lemma ep_cat_axioms :
    Category.axioms _ ep_pair ep_pair_eq_mixin ep_pair_comp_mixin.
  Proof.  
    constructor; simpl; intros.
    red. simpl. apply (cat_ident1 _ _ _ (embed f)).
    red. simpl. apply (cat_ident2 _ _ _ (embed f)).
    red. simpl. apply (cat_assoc _ _ _ _ _ (embed f)).
    red. simpl. apply (cat_respects _ _ _ _ _ _ _ _ H H0).
  Qed.

  Canonical Structure PLT_EP :=
    Category (PLT.ob hf) ep_pair ep_pair_eq_mixin ep_pair_comp_mixin ep_cat_axioms.

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

      Lemma ep_semidec : forall y, semidec ((x,y) ∈ PLT.hom_rel e /\ (y,x) ∈ PLT.hom_rel p).
      Proof.
        intro.
        apply semidec_conj.
        apply semidec_iff with (y ∈ erel_image (PLT.ord X) (PLT.ord Y) (PLT.dec X) 
          (PLT.hom_rel e) x).
        intros. apply erel_image_elem.
        apply semidec_in. apply PLT.dec.
        apply semidec_iff with (y ∈ erel_inv_image (PLT.ord Y) (PLT.ord X) (PLT.dec X) 
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
        apply PLT.compose_hom_rel in H0.
        destruct H0 as [y [??]].
        exists y. unfold embed_image.
        apply esubset_elem.
        intros. destruct H3; split.
        apply member_eq with (x,a); auto.
        destruct H2; split; split; auto.
        apply member_eq with (a,x); auto.
        destruct H2; split; split; auto.
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
      apply PLT.compose_hom_rel; auto.
      exists a. split; auto.
      apply PLT.hom_order with y' b; auto.
      intros. destruct H2; split.
      apply member_eq with (b,a0); auto.
      destruct H1; split; split; auto.
      apply member_eq with (a0,b); auto.
      destruct H1; split; split; auto.
      intros. destruct H2; split.
      apply member_eq with (a,a0); auto.
      destruct H1; split; split; auto.
      apply member_eq with (a0,a); auto.
      destruct H1; split; split; auto.
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
      simpl. apply PLT.compose_hom_rel.
      exists y'. intuition.
      apply PLT.hom_order with y x; auto.
      intros. destruct H2; split.
      apply member_eq with (x',a); auto.
      destruct H1; split; split; auto.
      apply member_eq with (a,x'); auto.
      destruct H1; split; split; auto.
      intros. destruct H2; split.
      apply member_eq with (x,a); auto.
      destruct H1; split; split; auto.
      apply member_eq with (a,x); auto.
      destruct H1; split; split; auto.
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
      simpl. apply PLT.compose_hom_rel.
      exists x; auto.
      intros. destruct H4; split.
      apply member_eq with (x,a); auto.
      destruct H3; split; split; auto.
      apply member_eq with (a,x); auto.
      destruct H3; split; split; auto.
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
      apply PLT.compose_hom_rel.
      exists q. split; auto.

      intros. destruct H11. split.
      apply member_eq with (q,a0); auto.
      destruct H10; split; split; auto.
      apply member_eq with (a0,q); auto.
      destruct H10; split; split; auto.
      split; apply H7; auto.
      apply cons_elem; auto.
      apply cons_elem; right.
      apply cons_elem; auto.
      intros. destruct H3. split.
      apply member_eq with (b,a0); auto.
      destruct H2; split; split; auto.
      apply member_eq with (a0,b); auto.
      destruct H2; split; split; auto.
      intros. destruct H3. split.
      apply member_eq with (a,a0); auto.
      destruct H2; split; split; auto.
      apply member_eq with (a0,a); auto.
      destruct H2; split; split; auto.
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
      esubset_dec (PLT.ord Y × PLT.ord X)%cat_ob
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
      change (fst y0) with (π₁#y0)%cat_ops.
      change (snd y0) with (π₂#y0)%cat_ops.
      rewrite <- H0. auto.
      split; auto.
      apply eprod_elem; split; apply eff_complete; auto.
      unfold project_rel in H.
      apply esubset_dec_elem in H.
      destruct H; auto.
      intros.
      change (fst y0) with (π₁#y0)%cat_ops.
      change (snd y0) with (π₂#y0)%cat_ops.
      rewrite <- H1. auto.
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
      esubset_dec (PLT.ord X×PLT.ord Y)%cat_ob
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
      change (fst y0) with (π₁#y0)%cat_ops.
      change (snd y0) with (π₂#y0)%cat_ops.
      rewrite <- H0. auto.
      split; auto.
      apply eprod_elem; split; apply eff_complete; auto.
      unfold embed_rel in H.
      apply esubset_dec_elem in H.
      destruct H; auto.
      intros.
      change (fst y0) with (π₁#y0)%cat_ops.
      change (snd y0) with (π₂#y0)%cat_ops.
      rewrite <- H1. auto.
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
      apply PLT.compose_hom_rel in H.
      apply ident_elem.
      destruct H as [y [??]].
      apply embed_rel_elem in H.
      apply project_rel_elem in H0.
      apply (embed_reflects embed).
      transitivity y; auto.

      hnf; simpl; intros.
      destruct a as [x x'].
      apply ident_elem in H.
      apply PLT.compose_hom_rel.
      exists (embed#(x:X)).
      split.
      apply embed_rel_elem. auto.
      apply project_rel_elem. auto.

      hnf; simpl; intros.      
      destruct a as [y y'].
      apply PLT.compose_hom_rel in H.
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

    intros.
    destruct H2. split.
    apply member_eq with (c,a); auto.
    destruct H1; split; split; auto.
    apply member_eq with (a,c); auto.
    destruct H1; split; split; auto.

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
    apply PLT.compose_hom_rel.
    eauto.

    intros.
    destruct H2. split.
    apply member_eq with (c,a); auto.
    destruct H1; split; split; auto.
    apply member_eq with (a,c); auto.
    destruct H1; split; split; auto.
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

    intros. destruct H1; split.
    apply member_eq with (x,a); auto.
    destruct H0; split; split; auto.
    apply member_eq with (a,x); auto.
    destruct H0; split; split; auto.

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

    intros. destruct H1; split.
    apply member_eq with (x,a); auto.
    destruct H0; split; split; auto.
    apply member_eq with (a,x); auto.
    destruct H0; split; split; auto.
  Qed.
End ep_pairs.

Arguments embed [hf] [X] [Y] e.
Arguments project [hf] [X] [Y] e.
Arguments ep_embedding [hf] [X] [Y] ep.
Arguments embed_ep_pair [hf] [X] [Y] _.

Canonical Structure PLT_EP.
Canonical Structure ep_pair_eq.
Canonical Structure ep_pair_comp.


Program Definition embedForget hf : functor (EMBED hf) (PLT.PLT hf) :=
  Functor (EMBED hf) (PLT.PLT hf) (fun X => X) (fun X Y f => embed_hom hf X Y f) _ _ _.
Next Obligation.
  intros. split; hnf; simpl; intros.
  destruct a.
  apply embed_rel_elem in H0.
  apply ident_elem.
  rewrite H0.
  destruct H. apply H.
  destruct a.
  apply embed_rel_elem.
  apply ident_elem in H0.
  rewrite H0. destruct H. apply H1.
Qed.
Next Obligation.
  simpl; intros.
  split; hnf; simpl; intros.
  destruct a as [a c].
  apply embed_rel_elem in H0.
  destruct H. 
  apply PLT.compose_hom_rel.
  exists (g a).
  split.
  apply embed_rel_elem. auto.
  apply embed_rel_elem. 
  rewrite H0. apply H.
  destruct a as [a c].
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [y [??]].
  apply embed_rel_elem.
  simpl in *.
  apply embed_rel_elem in H0.
  apply embed_rel_elem in H1.
  rewrite H1. rewrite H0.
  destruct H. apply H2.
Qed.
Next Obligation.
  repeat intro. split; hnf; simpl; intros.
  destruct a as [a b].
  apply embed_rel_elem in H0. apply embed_rel_elem.
  rewrite H0. destruct H. apply H.
  destruct a as [a b].
  apply embed_rel_elem in H0. apply embed_rel_elem.
  rewrite H0. destruct H. apply H1.
Qed.
