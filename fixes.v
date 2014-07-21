(* Copyright (c) 2014, Robert Dockins *)

Require Import String.
Require Import List.
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
Require Import profinite.
Require Import profinite_adj.

(** * A fixpoint operator for nonstrict functions in PLT.
  *)

Program Definition precompose hf (A B C:PLT.PLT hf) (f:A → B) :
  (Preord.hom (PLT.hom_ord hf B C) (PLT.hom_ord hf A C)) := 
  Preord.Hom (PLT.hom_ord hf B C) (PLT.hom_ord hf A C) 
     (fun g => g ∘ f) _.
Next Obligation.
  intros. apply PLT.compose_mono; auto.
Qed.
Arguments precompose [hf A B] C f.

Program Definition postcompose hf (A B C:PLT.PLT hf) (g:B → C) :
  (Preord.hom (PLT.hom_ord hf A B) (PLT.hom_ord hf A C)) :=
  Preord.Hom (PLT.hom_ord hf A B) (PLT.hom_ord hf A C) 
      (fun f => g ∘ f) _.
Next Obligation.
  intros. apply PLT.compose_mono; auto.
Qed.
Arguments postcompose [hf] A [B C] g.

Lemma precompose_continuous hf (A B C:PLT.PLT hf) (f:A → B) :
  continuous (directed_hf_cl hf) (precompose C f).
Proof.
  apply CPO.continuous_sup.
  repeat intro. destruct a as [a c].
  unfold precompose in H.
  apply PLT.compose_hom_rel in H.
  destruct H as [y [??]].
  simpl in H0.
  apply union_axiom in H0. destruct H0 as [q [??]].
  apply image_axiom2 in H0. destruct H0 as [q' [??]].
  simpl in H2.
  apply union_axiom.
  exists (PLT.hom_rel (precompose C f q')).
  split. apply image_axiom1'.
  exists (precompose C f q').
  split; auto.
  apply image_axiom1'.
  exists q'. split; auto.
  unfold precompose.
  apply PLT.compose_hom_rel.
  exists y. split; auto.
  rewrite <- H2; auto.
Qed.

Lemma postcompose_continuous hf (A B C:PLT.PLT hf) (g:B → C) :
  continuous (directed_hf_cl hf) (postcompose A g).
Proof.
  apply CPO.continuous_sup.
  repeat intro. destruct a as [a c].
  unfold postcompose in H.
  apply PLT.compose_hom_rel in H.
  destruct H as [y [??]].
  simpl in H.
  apply union_axiom in H. destruct H as [q [??]].
  apply image_axiom2 in H. destruct H as [q' [??]].
  simpl in H2.
  apply union_axiom.
  exists (PLT.hom_rel (postcompose A g q')).
  split. apply image_axiom1'.
  exists (postcompose A g q').
  split; auto.
  apply image_axiom1'.
  exists q'. split; auto.
  unfold postcompose.
  apply PLT.compose_hom_rel.
  exists y. split; auto.
  rewrite <- H2; auto.
Qed.

Program Definition pair_right hf (A B C:PLT.PLT hf) (f:C → A) :
  (Preord.hom (PLT.hom_ord hf C B) (PLT.hom_ord hf C (PLT.prod A B))) := 
  Preord.Hom (PLT.hom_ord hf C B) (PLT.hom_ord hf C (PLT.prod A B)) 
  (fun g => PLT.pair f g) _.
Next Obligation.
  intros. apply PLT.pair_mono; auto.
Qed.
Arguments pair_right [hf A] B [C] f.

Program Definition pair_left hf (A B C:PLT.PLT hf) (g:C → B) :
  (Preord.hom (PLT.hom_ord hf C A) (PLT.hom_ord hf C (PLT.prod A B))) := 
  Preord.Hom (PLT.hom_ord hf C A) (PLT.hom_ord hf C (PLT.prod A B)) 
  (fun f => PLT.pair f g) _.
Next Obligation.
  intros. apply PLT.pair_mono; auto.
Qed.
Arguments pair_left [hf] A [B C] g.

Lemma pair_right_continuous hf (A B C:PLT.PLT hf) (f:C → A) :
  continuous (directed_hf_cl hf) (pair_right B f).
Proof.
  apply CPO.continuous_sup.
  repeat intro. destruct a as [c [a b]].
  unfold pair_right in H.  
  simpl in H.
  rewrite (PLT.pair_hom_rel _ _ _ _ _ _ c a b) in H.
  destruct H.
  simpl in H0.
  apply union_axiom in H0. destruct H0 as [q [??]].
  apply image_axiom2 in H0. destruct H0 as [q' [??]].
  simpl in H2.
  apply union_axiom.
  exists (PLT.hom_rel (pair_right B f q')).
  split.
  apply image_axiom1'. 
  exists (pair_right B f q'). split; auto.
  apply image_axiom1'.  exists q'. split; auto.
  simpl.
  apply PLT.pair_hom_rel. split; auto.
  rewrite <- H2; auto.
Qed.

Lemma pair_left_continuous hf (A B C:PLT.PLT hf) (g:C → B) :
  continuous (directed_hf_cl hf) (pair_left A g).
Proof.
  apply CPO.continuous_sup.
  repeat intro. destruct a as [c [a b]].
  unfold pair_right in H.  
  simpl in H.
  rewrite (PLT.pair_hom_rel _ _ _ _ _ _ c a b) in H.
  destruct H.
  simpl in H.
  apply union_axiom in H. destruct H as [q [??]].
  apply image_axiom2 in H. destruct H as [q' [??]].
  simpl in H2.
  apply union_axiom.
  exists (PLT.hom_rel (pair_left A g q')).
  split.
  apply image_axiom1'. 
  exists (pair_left A g q'). split; auto.
  apply image_axiom1'.  exists q'. split; auto.
  simpl.
  apply PLT.pair_hom_rel. split; auto.
  rewrite <- H2; auto.
Qed.

Section fixes.
  Variable Γ:PLT.
  Variable A:∂PLT.
  Variable f:Γ → U A ⇒ U A.

  Definition fixes_step
    (x:Γ → U A) : Γ → U A :=

    apply ∘ 〈f, x〉.

  Program Definition fixes_step' :
    PLT.homset_cpo _ Γ (U A) → PLT.homset_cpo _ Γ (U A) :=

    CPO.Hom _ (PLT.homset_cpo _ Γ (U A)) (PLT.homset_cpo _ Γ (U A)) 
    fixes_step _ _.
  Next Obligation.
    intros. unfold fixes_step.
    apply PLT.compose_mono; auto.
    apply PLT.pair_mono; auto.    
  Qed.    
  Next Obligation.
    red; intros.
    unfold fixes_step.
    apply continuous_equiv with
      (postcompose Γ PLT.app ∘ pair_right (U A) f); auto.
    hnf; simpl; intros. split; auto.
    apply continuous_sequence.
    apply postcompose_continuous.
    apply pair_right_continuous.
  Qed.

  Definition fixes : Γ → U A := lfp fixes_step'.

  Lemma fixes_unroll :
    fixes ≈ apply ∘ 〈f, fixes〉.
  Proof.
    unfold fixes at 1.
    rewrite <- lfp_fixpoint. simpl. unfold fixes_step.
    auto.
  Qed.

End fixes.
Arguments fixes [Γ A] f.


Lemma fixes_mono Γ A (f g:Γ → U A ⇒ U A) : 
  f ≤ g -> fixes f ≤ fixes g.
Proof.
  intro. unfold fixes at 1.
  apply scott_induction.
  red. split. apply bottom_least.
  intros. 
  apply CPO.sup_is_least.
  red; intros. apply H1; auto.
  intros. rewrite <- H0; auto.
  simpl; intros. unfold fixes_step.
  rewrite fixes_unroll.
  apply PLT.compose_mono; auto.
  apply PLT.pair_mono; auto.
Qed.

Lemma fixes_eq Γ A (f g:Γ → U A ⇒ U A) : 
  f ≈ g -> fixes f ≈ fixes g.
Proof.
  intros [??]; split; apply fixes_mono; auto.
Qed.

Add Parametric Morphism Γ A :
  (@fixes Γ A)
  with signature (Preord.ord_op _ ==> Preord.ord_op _)
  as fixes_le_morphism.
Proof.
  intros. apply fixes_mono. auto.
Qed.

Add Parametric Morphism Γ A :
  (@fixes Γ A)
  with signature (eq_op _ ==> eq_op _)
  as fixes_morphism.
Proof.
  intros. apply fixes_eq. auto.
Qed.

Lemma plt_bot_None A B x y :
  (x,y) ∈ PLT.hom_rel (⊥ : A → U B) <-> y = None.
Proof.
  split; intros.
  simpl in H.
  unfold plt_hom_adj' in H.
  apply PLT.compose_hom_rel in H.
  destruct H as [?[??]].
  simpl in H.
  apply adj_unit_rel_elem in H.
  apply U_hom_rel in H0.
  destruct H0; auto.
  destruct H0 as [?[?[??]]].
  simpl in H0.
  apply union_axiom in H0.
  destruct H0 as [?[??]].
  apply image_axiom2 in H0.
  destruct H0 as [?[??]].
  apply empty_elem in H0. elim H0.

  subst y.
  simpl.
  unfold plt_hom_adj'.
  apply PLT.compose_hom_rel.
  exists None.
  split. simpl.
  apply adj_unit_rel_elem.
  hnf; auto.
  apply U_hom_rel. auto.
Qed.

Lemma plt_bot_chomp A B C (g:A → B) :
  (⊥ : B → U C) ∘ g ≈ ⊥.
Proof.
  split. 2: apply bottom_least.
  hnf. intros.
  destruct a.
  apply PLT.compose_hom_rel in H.
  destruct H as [?[??]].
  apply plt_bot_None in H0.
  apply plt_bot_None. auto.
Qed.  

Lemma fixes_compose_commute Γ Γ' A (f:Γ → U A ⇒ U A) (g:Γ' → Γ) :
  fixes f ∘ g ≈ fixes (f ∘ g).
Proof.
  split; unfold fixes at 1; apply scott_induction.
  red; split.
  rewrite plt_bot_chomp.
  apply bottom_least.
  intros.
  transitivity (∐(image (precompose (U A) g) XS)).
  destruct (CPO.continuous_sup _ _ _ (precompose (U A) g)).
  apply H1.
  apply (precompose_continuous false _ _ (U A) g).
  apply CPO.sup_is_least.
  red; intros.
  apply image_axiom2 in H1.
  destruct H1 as [q [??]].
  rewrite H2. simpl.
  apply H0. auto.
  intros. rewrite <- H. auto.
  simpl; intros.
  unfold fixes_step.
  rewrite fixes_unroll.
  rewrite <- (cat_assoc PLT).
  apply PLT.compose_mono; auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_mono; auto.
  
  red; split.
  apply bottom_least.
  intros.
  apply CPO.sup_is_least.
  red; intros.
  apply H0; auto.
  intros.
  rewrite <- H; auto.
  simpl; intros.
  unfold fixes_step.
  rewrite fixes_unroll.
  rewrite <- (cat_assoc PLT).
  apply PLT.compose_mono; auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_mono; auto.
Qed.
