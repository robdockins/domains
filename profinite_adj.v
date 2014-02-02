(* Copyright (c) 2014, Robert Dockins *)

Require Import Setoid.

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
Require Import profinite.

(**  * Adjoint relation between the pointed and unpointed domains.

     Here we define the lifing and forgetful functors between pointed
     and unpointed domains, and show that they are adjoint.

     In addition, I show the counit of this adjunction has a partial inverse,
     which is a useful operation for "strictifying" a nonstrict hom.

     NOTE!! The naming convention here is opposite that of the companion
     paper.  Here the forgetful functor goes from unpointed domains to pointed
     domains, and the lifing functor goes from pointed domains to unpointed
     domains.
  *)

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
  generalize (mub_clos_mub HA X M).
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

Definition forgetPLT_ob (X:ob PLT) : ob ∂PLT :=
  PLT.Ob _ (PLT.carrier _ X) (PLT.Class _ _
    (Preord.mixin (PLT.ord X))
    (PLT.effective X)
    (plotkin_forget _ (PLT.effective X) (PLT.plotkin X))).

Program Definition forgetPLT_map (X Y:ob PLT) (f:X → Y) 
  : forgetPLT_ob X → forgetPLT_ob Y :=

  PLT.Hom _ (forgetPLT_ob X) (forgetPLT_ob Y) 
    (@PLT.hom_rel _ X Y f) (PLT.hom_order _ X Y f) _.
Next Obligation.
  repeat intro. apply (PLT.hom_directed _ _ _ f); hnf; auto.
Qed.

Program Definition forgetPLT : functor PLT ∂PLT :=
  Functor PLT ∂PLT forgetPLT_ob forgetPLT_map _ _ _.
Solve Obligations of forgetPLT using auto.

Definition liftPPLT_ob (X:ob ∂PLT) : ob PLT :=
  PLT.Ob _ (option (PLT.carrier _ X)) (PLT.Class _ _
    (lift_mixin (PLT.ord X)) 
    (effective_lift (PLT.effective X)) 
    (lift_plotkin _ _ _  (PLT.plotkin X) (PLT.effective X))).

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
  apply union2_elem in H. destruct H.
  apply union2_elem in H. destruct H.
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
  apply union2_elem.
  left.
  apply union2_elem.
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
  apply union2_elem. right.
  apply image_axiom1'.
  exists (a,b). split; auto.
  simpl.
  split; split; auto.
Qed.  

Program Definition liftPPLT_map (X Y:ob ∂PLT) (f:X → Y) 
  : liftPPLT_ob X → liftPPLT_ob Y :=

  PLT.Hom _ (liftPPLT_ob X) (liftPPLT_ob Y)
     (liftPPLT_rel (PLT.ord X) (PLT.ord Y) (PLT.effective X) (@PLT.hom_rel _ X Y f))
      _ _.
Next Obligation.
  intros. simpl in *.
  apply liftPPLT_rel_elem.
  apply (liftPPLT_rel_elem (PLT.ord X) (PLT.ord Y)) in H1.
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
  apply PLT.hom_order with a b; auto.
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
  destruct (PLT.hom_directed _ _ _ f c0 M').
  exists c. rewrite H0. apply cons_elem; auto.
  red; intros.
  destruct H1 as [q [??]].
  apply in_unlift in H1.
  assert (Some a ∈ M).
  exists (Some q); split; auto.
  apply H in H3.
  apply erel_image_elem in H3.
  apply (liftPPLT_rel_elem (PLT.ord X) (PLT.ord Y)) in H3.
  destruct H3.
  destruct H3. elim H3.
  destruct H3 as [m [n [?[??]]]].
  apply erel_image_elem.
  apply PLT.hom_order with m n; auto.
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
  apply (liftPPLT_rel_elem (PLT.ord X) (PLT.ord Y)) in H1.
  destruct H1.
  destruct H1. elim H1.
  destruct H1 as [a [b [?[??]]]].
  destruct H2. elim H4.
Qed.

Program Definition liftPPLT : functor ∂PLT PLT :=
  Functor ∂PLT PLT liftPPLT_ob liftPPLT_map _ _ _.
Next Obligation.
  simpl; intros.
  split; hnf; simpl; intros.
  destruct a as [a a'].
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel f)) in H0.
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
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel f)).
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
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel h)) in H0.
  destruct H0.
  exists None.
  split.
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel g)).
  auto.
  apply (liftPPLT_rel_elem _ _ (PLT.effective B) (PLT.hom_rel f)).
  auto.
  destruct H0 as [a' [c' [?[??]]]].  
  destruct H.
  apply H in H0.
  simpl in H0.
  apply compose_elem in H0.
  destruct H0 as [b' [??]].
  exists (Some b').
  split.
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel g)).
  right.
  eauto.
  apply (liftPPLT_rel_elem _ _ (PLT.effective B) (PLT.hom_rel f)).
  right. eauto.
  apply PLT.hom_order.

  destruct a as [a c].
  apply compose_elem in H0.
  destruct H0 as [b [??]]. simpl in b.
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel g)) in H0.
  apply (liftPPLT_rel_elem _ _ (PLT.effective B) (PLT.hom_rel f)) in H1.
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel h)).
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
  apply PLT.hom_order.
  exists y.
  split; auto.
  apply PLT.hom_order with x' y'; auto.
  simpl. intros.
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel g)) in H3.
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel g)).
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
  apply PLT.hom_order with p q; auto.
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
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel f)) in H0.
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel g)).
  destruct H0; auto.    
  right.
  destruct H0 as [p [q [?[??]]]].
  exists p. exists q. split; auto.
  destruct H. apply H; auto.
  destruct a as [a b].
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel g)) in H0.
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel f)).
  destruct H0; auto.    
  right.
  destruct H0 as [p [q [?[??]]]].
  exists p. exists q. split; auto.
  destruct H. apply H3; auto.
Qed.

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
  apply union2_elem in H.
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
  apply union2_elem.
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
  apply eprod_elem. split; apply eff_complete.
  left.
  apply image_axiom1'.
  simpl. exists x. split; auto. apply eff_complete.
Qed.

Program Definition adj_unit_hom (X:ob PLT) 
  : X → (liftPPLT (forgetPLT X))

  := PLT.Hom _ X (liftPPLT (forgetPLT X)) (adj_unit_rel (PLT.ord X) (PLT.effective X)) _ _.
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
  rewrite (liftPPLT_rel_elem _ _ _ (PLT.hom_rel f)).
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
  destruct (PLT.hom_directed _ _ _ f a nil).  
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

Definition adj_counit_rel (Y:ob ∂PLT) 
  : erel (forgetPLT (liftPPLT Y)) Y :=

    (image (pair_map (liftup Y) (id(PLT.ord Y)))
      (esubset_dec _ (fun q => fst q ≥ snd q)
                  (fun q => eff_ord_dec Y (PLT.effective Y) (snd q) (fst q))
                  (eprod (eff_enum Y (PLT.effective Y))
                         (eff_enum Y (PLT.effective Y))))).

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
  apply eprod_elem. split; apply eff_complete.
  elim H.
Qed.

Program Definition adj_counit_hom Y : forgetPLT (liftPPLT Y) → Y :=
  PLT.Hom _ (forgetPLT (liftPPLT Y)) Y (adj_counit_rel Y) _ _.
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

Program Definition adj_counit : nt (forgetPLT ∘ liftPPLT) id(∂PLT)
  := NT (forgetPLT ∘ liftPPLT) id(∂PLT) adj_counit_hom _.
Next Obligation.
  intros.
  split; hnf; simpl; intros.
  destruct a as [a b].
  apply compose_elem in H; simpl.
  simpl in H.
  destruct H as [b' [??]].
  apply (adj_counit_rel_elem B) in H0.
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel f)) in H.
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
  apply PLT.hom_order with p q; auto.
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
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel f)).
  right.
  exists c. exists b. split; auto.
  apply (PLT.hom_order _ _ _ f) with a' b; auto.
  apply adj_counit_rel_elem. auto.
  apply adj_counit_hom_obligation_1.
Qed.

Program Definition adj_counit_inv_hom Y : Y → forgetPLT (liftPPLT Y) :=
  PLT.Hom _ Y (forgetPLT (liftPPLT Y)) (adj_unit_rel (PLT.ord Y) (PLT.effective Y)) _ _.
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
  apply (liftPPLT_rel_elem _ _ (PLT.effective A) (PLT.hom_rel f)).
  apply adj_unit_rel_elem in H0.
  destruct b; auto.
  right.
  exists a. exists c. split; auto.
  apply PLT.hom_order with a y; auto.
  apply PLT.hom_order.
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
  assert ((Some c, o) ∈ PLT.hom_rel (f ∘ adj_counit_hom Y)).
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

Lemma adj_inv_eq : forall A B (f:A → liftPPLT B),
  (forall a, exists b, (a, Some b) ∈ PLT.hom_rel f) ->
  adj_counit_inv_hom B ∘ adj_counit B ∘ forgetPLT@f ≈ forgetPLT@f.
Proof.
  intros. split.
  transitivity (id ∘ forgetPLT@f).
  apply PLT.compose_mono. auto.
  apply adj_counit_inv_le.
  rewrite (cat_ident2 ∂PLT). auto.
  hnf. intros [x y] H0.
  apply compose_hom_rel.
  destruct y.
  exists (Some c). split; auto.
  apply compose_hom_rel. simpl.
  exists c. split.
  apply adj_counit_rel_elem. auto.
  apply adj_unit_rel_elem. auto.
  destruct (H x) as [y ?].
  exists (Some y). split; auto.
  apply compose_hom_rel.
  exists y. split.
  apply adj_counit_rel_elem. auto.
  apply adj_unit_rel_elem. hnf. auto.
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
  apply (liftPPLT_rel_elem _ _ (PLT.effective _) (adj_counit_rel A)) in H0.
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
  apply (liftPPLT_rel_elem _ _ (PLT.effective _) (adj_counit_rel A)).
  destruct a'; auto.
  right.
  destruct a.
  simpl.
  exists (Some c0). exists c.
  split; auto.
  apply (adj_counit_rel_elem A). auto.
  elim H.  
Qed.

Lemma liftPPLT_reflects : forall (X Y:ob ∂PLT) (f f':X → Y),
  liftPPLT@f ≤ liftPPLT@f' -> f ≤ f'.
Proof.
  repeat intro; simpl in *.
  destruct a as [x y].
  assert ((Some x, Some y) ∈ (PLT.hom_rel (liftPPLT_map X Y f))).
  simpl.
  apply (liftPPLT_rel_elem _ _ _ (PLT.hom_rel f)).
  right. exists x. exists y. split; auto.
  apply H in H1.
  simpl in H1.
  apply (liftPPLT_rel_elem _ _ _ (PLT.hom_rel f')) in H1.
  destruct H1.
  destruct H1. elim H1.
  destruct H1 as [a [b [?[??]]]].
  apply member_eq with (a,b); auto.
  split; split; auto.
Qed.

Lemma liftPPLT_mono : forall (X Y:ob ∂PLT) (f f':X → Y),
  f ≤ f' -> liftPPLT@f ≤ liftPPLT@f'.
Proof.
  repeat intro; simpl in *.
  destruct a as [x y].
  apply (liftPPLT_rel_elem _ _ _ (PLT.hom_rel f)) in H0.
  apply (liftPPLT_rel_elem _ _ _ (PLT.hom_rel f')).
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

Require Import cpo.

Notation U := liftPPLT.
Notation L := forgetPLT.

Lemma lift_plt_bottom_least (X:PLT) (Y:∂PLT) (f:X → liftPPLT Y) :
  liftPPLT@⊥ ∘ adj_unit X ≤ f.
Proof.
  intros.
  transitivity
    (liftPPLT@(adj_counit Y ∘ forgetPLT@f) ∘ adj_unit X).
  apply PLT.compose_mono. auto.
  apply liftPPLT_mono.
  apply bottom_least.
  rewrite Functor.compose. 2: reflexivity.
  rewrite <- (cat_assoc PLT).
  rewrite <- (NT.axiom adj_unit f).
  rewrite (cat_assoc PLT).
  rewrite (Adjunction.adjoint_axiom2 PLT_adjoint Y).
  rewrite (cat_ident2 PLT). auto.
Qed.

Instance lift_plt_pointed (X:PLT) (Y:∂PLT) : 
  pointed (PLT.homset_cpo _ X (liftPPLT Y)) :=
  { bottom := liftPPLT @ ⊥ ∘ adj_unit X
  ; bottom_least := lift_plt_bottom_least X Y
  }.

Program Definition lift_unit :
  PLT.unit true → forgetPLT (PLT.unit false)
  := PLT.Hom true (PLT.unit true) (forgetPLT (PLT.unit false))
          (ident_rel effective_unit)
          _ _.
Next Obligation.        
  intros. eapply ident_ordering; eauto.
Qed.
Next Obligation.
  intros. apply ident_image_dir.
Qed.
 
Program Definition lift_unit' :
  forgetPLT (PLT.unit false) → PLT.unit true
  := PLT.Hom true (forgetPLT (PLT.unit false)) (PLT.unit true) 
          (ident_rel effective_unit)
          _ _.
Next Obligation.        
  intros. eapply ident_ordering; eauto.
Qed.
Next Obligation.
  intros. apply ident_image_dir.
Qed.

Lemma lift_unit_id1 : lift_unit ∘ lift_unit' ≈ id.
Proof.
  split; hnf; intros.
  destruct a. destruct c. destruct c0.
  simpl. apply ident_elem. auto.
  destruct a. destruct c. destruct c0.
  apply compose_hom_rel. exists tt.
  split; simpl; apply ident_elem; auto.
Qed.

Lemma lift_unit_id2 : lift_unit' ∘ lift_unit ≈ id.
Proof.
  split; hnf; intros.
  destruct a. destruct c. destruct c0.
  simpl. apply ident_elem. auto.
  destruct a. destruct c. destruct c0.
  apply compose_hom_rel. exists tt.
  split; simpl; apply ident_elem; auto.
Qed.

Program Definition lift_prod (A B:PLT) :
  PLT.prod (forgetPLT A) (forgetPLT B) → forgetPLT (PLT.prod A B)
  := PLT.Hom true
          (PLT.prod (forgetPLT A) (forgetPLT B)) (forgetPLT (PLT.prod A B))
          (ident_rel (effective_prod (PLT.effective A) (PLT.effective B)))
          _ _.
Next Obligation.  
  intros. eapply ident_ordering; eauto.
Qed.
Next Obligation.
  intros. apply ident_image_dir.
Qed.

Program Definition lift_prod' (A B:PLT) :
  forgetPLT (PLT.prod A B) → PLT.prod (forgetPLT A) (forgetPLT B)
  := PLT.Hom true
          (forgetPLT (PLT.prod A B)) (PLT.prod (forgetPLT A) (forgetPLT B)) 
          (ident_rel (effective_prod (PLT.effective A) (PLT.effective B)))
          _ _.
Next Obligation.  
  intros. eapply ident_ordering; eauto.
Qed.
Next Obligation.
  intros. apply ident_image_dir.
Qed.

Lemma lift_prod_id1 A B : lift_prod A B ∘ lift_prod' A B ≈ id.
Proof.
  split; hnf; intros.
  destruct a.
  apply compose_hom_rel in H.
  destruct H as [q [??]].
  simpl in *. apply ident_elem in H. apply ident_elem in H0.
  apply ident_elem. transitivity q; auto.
  destruct a.
  apply compose_hom_rel.
  simpl. exists c0.
  simpl in *. apply ident_elem in H.
  split; apply ident_elem; auto.
Qed.

Lemma lift_prod_id2 A B : lift_prod' A B ∘ lift_prod A B ≈ id.
Proof.
  split; hnf; intros.
  destruct a.
  apply compose_hom_rel in H.
  destruct H as [q [??]].
  simpl in *. apply ident_elem in H. apply ident_elem in H0.
  apply ident_elem. transitivity q; auto.
  destruct a.
  apply compose_hom_rel.
  simpl. exists c0.
  simpl in *. apply ident_elem in H.
  split; apply ident_elem; auto.
Qed.

Lemma lift_prod_pair C A B (f:C → A) (g:C → B) :
  lift_prod A B ∘ PLT.pair (forgetPLT@f) (forgetPLT@g) ≈ forgetPLT@(PLT.pair f g).
Proof.
  split; hnf; intros.
  destruct a.
  apply compose_hom_rel in H.
  destruct H as [q [??]].
  simpl in H0.
  apply ident_elem in H0.
  revert H. simpl.
  apply pair_rel_ordering; auto.
  apply PLT.hom_order.
  apply PLT.hom_order.
  destruct a.
  apply compose_hom_rel.
  exists c0.  
  split. auto.
  simpl. apply ident_elem. auto.
Qed.

Lemma lift_prod_pair' C A B (f:C → A) (g:C → B) :
  PLT.pair (forgetPLT@f) (forgetPLT@g) ≈ lift_prod' A B ∘ forgetPLT@(PLT.pair f g).
Proof.
  split; hnf; intros.
  destruct a.
  apply compose_hom_rel.
  exists c0.  
  split. auto.
  simpl. apply ident_elem. auto.
  destruct a.
  apply compose_hom_rel in H.
  destruct H as [q [??]].
  simpl in H0.
  apply ident_elem in H0.
  simpl.
  destruct c0. destruct q.
  apply (pair_rel_elem _ _ _ _ _ _ c c0 c1).
  simpl in H.
  rewrite (pair_rel_elem _ _ _ _ _ _ c c2 c3) in H.
  destruct H. destruct H0. simpl in *. split.
  eapply (PLT.hom_order _ _ _ f); eauto.
  eapply (PLT.hom_order _ _ _ g); eauto.
Qed.


Section strictify.
  Variables X Y:ob ∂PLT.
  Variable f: liftPPLT X → liftPPLT Y.  

  Let strictify := adj_counit Y ∘ forgetPLT@f ∘ adj_counit_inv_hom X.

  Lemma f_explode : liftPPLT@(adj_counit Y ∘ forgetPLT@f) ∘ adj_unit (liftPPLT X) ≈ f.
    rewrite Functor.compose. 2: reflexivity.
    rewrite <- (cat_assoc _ _ _ _ _ (liftPPLT@adj_counit Y)).
    rewrite <- (NT.axiom adj_unit f).
    rewrite (cat_assoc _ _ _ _ _ (liftPPLT@adj_counit Y)).
    generalize (Adjunction.adjoint_axiom2 PLT_adjoint Y).
    intros. simpl in H.
    rewrite H.
    rewrite (cat_ident2 _ _ _ (id@f)).
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
    rewrite (cat_ident1 _ _ _ (liftPPLT@adj_counit_inv_hom X)). auto.
    rewrite <- H0.
    simpl.
    rewrite (cat_assoc _ _ _ _ _ (liftPPLT@adj_counit_inv_hom X)).
    rewrite <- (Functor.compose liftPPLT). 2: reflexivity.
    transitivity (id ∘ adj_unit_hom (liftPPLT_ob X)).
    apply PLT.compose_mono. auto.
    transitivity (liftPPLT@(id (forgetPLT (liftPPLT X)))).
    apply liftPPLT_mono.
    apply adj_counit_inv_le.
    rewrite Functor.ident; auto.
    rewrite (cat_ident2 _ _ _ (adj_unit_hom _)). auto.
    auto.        
  Qed.    

  Lemma strictify_largest : forall q, liftPPLT@q ≤ f -> q ≤ strictify.
  Proof.
    intros.
    unfold strictify.
    transitivity (adj_counit Y ∘ forgetPLT@(liftPPLT@q) ∘ adj_counit_inv_hom X).
    transitivity (adj_counit Y ∘ adj_counit_inv_hom Y ∘ q).
    rewrite (adj_counit_inv_eq Y).
    rewrite (cat_ident2 _ _ _ q). auto.
    rewrite <- (cat_assoc _ _ _ _ _ (adj_counit Y)).
    rewrite <- (cat_assoc _ _ _ _ _ (adj_counit Y)).
    apply PLT.compose_mono; auto.
    apply adj_counit_inv_ntish. 
    rewrite <- (cat_assoc _ _ _ _ _ (adj_counit Y)).
    rewrite <- (cat_assoc _ _ _ _ _ (adj_counit Y)).
    apply PLT.compose_mono; auto.
    apply PLT.compose_mono; auto.
  Qed.
End strictify.

Global Opaque liftPPLT.
Global Opaque forgetPLT.

