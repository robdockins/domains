(* Copyright (c) 2014, Robert Dockins *)

Require Import String.
Require Import List.

Require Import atoms.
Require Import permutations.

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
Require Import flat.

Arguments lift_prod [A B].
Arguments lift_prod' [A B].

Definition strict_app (A B:∂PLT) 
  : U (A ⊸ B) × U A → U B

  := U·( apply ∘ PLT.pair_map ε ε ∘ lift_prod') ∘ η.

Definition strict_curry (Γ:PLT) (A B:∂PLT)
  (f:Γ×U A → U B) : Γ → U (A ⊸ B) 

  := U·(Λ( ε ∘ L·f ∘ lift_prod ∘ PLT.pair_map id γ)) ∘ η.
  
Definition strict_app' (A B:∂PLT) 
  : U (colift (A ⊸ B)) × U A → U B 

  := strict_app A B ∘ PLT.pair_map (U·ε) id.

Definition strict_curry' (Γ:PLT) (A B:∂PLT)
  (f:Γ × U A → U B) : Γ → U (colift (A ⊸ B))

  := η ∘ strict_curry Γ A B f.


Definition semvalue (Γ:PLT) (A:∂PLT) (f:Γ → U A) :=
  forall g, exists a, (g,Some a) ∈ PLT.hom_rel f.
Arguments semvalue [Γ A] f.

Lemma strict_curry_app2 D (Γ:PLT) (A B:∂PLT) 
  (f : Γ×U A → U B) (g : D → U A) (h:D → Γ) (Hg : semvalue g) :

  strict_app A B ∘ PLT.pair (strict_curry Γ A B f ∘ h) g ≈ f ∘ PLT.pair h g.
Proof.
  unfold strict_app, strict_curry.
  simpl.
  rewrite <- (cat_assoc PLT).
  rewrite (NT.axiom adj_unit
    (PLT.pair
          (U ·
           PLT.curry
             (adj_counit_hom B ∘ L·f ∘ @lift_prod Γ (U A)
              ∘ PLT.pair_map id γ) ∘ adj_unit_hom Γ ∘ h) g)).
  simpl.
  rewrite (cat_assoc PLT).
  rewrite <- (Functor.compose U). 2: reflexivity.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- lift_prod_pair'.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (PLT.pair_map_pair true).
  rewrite (Functor.compose L). 2: reflexivity.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (cat_assoc ∂PLT).
  generalize (NT.axiom adj_counit
    (PLT.curry (adj_counit_hom B
                ∘ (L·f ∘ (@lift_prod Γ (U A) ∘ PLT.pair_map id γ))))).
  simpl; intros.
  etransitivity.
  apply cat_respects. 2: reflexivity.
  apply (Functor.respects U).
  apply cat_respects. reflexivity.
  apply PLT.pair_eq. 2: reflexivity.
  rewrite (cat_assoc ∂PLT).
  rewrite (Functor.compose L). 2: reflexivity.
  rewrite (cat_assoc ∂PLT).
  apply cat_respects. 2: reflexivity.
  apply cat_respects. 2: reflexivity.
  apply H. clear H.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (cat_assoc ∂PLT).
  generalize (Adjunction.adjoint_axiom1 PLT_adjoint Γ).
  simpl. intros. 
  rewrite (cat_assoc ∂PLT _ _ _ _
    (adj_counit_hom (L Γ))).
  rewrite H. clear H.
  rewrite (cat_ident2 ∂PLT).
  rewrite (PLT.curry_apply3 true).
  repeat rewrite <- (cat_assoc ∂PLT).
  rewrite <- (PLT.pair_map_pair true).
  assert (PLT.pair (id ∘ L·h)
             (adj_counit_inv_hom A ∘ (adj_counit_hom A ∘ L·g)) 
             ≈
          PLT.pair (L·h) (L·g)).
  apply PLT.pair_eq.
  apply cat_ident2.
  rewrite (cat_assoc ∂PLT).
  apply adj_inv_eq. auto.
  etransitivity.
  apply cat_respects. 2: reflexivity.
  apply Functor.respects.
  apply cat_respects. reflexivity.
  apply cat_respects. reflexivity.
  apply cat_respects. reflexivity. apply H.
  rewrite lift_prod_pair.
  rewrite <- (Functor.compose L). 2: reflexivity.
  rewrite (Functor.compose U). 2: reflexivity.
  rewrite <- (cat_assoc PLT).
  rewrite <- (NT.axiom adj_unit (f ∘ PLT.pair h g)). simpl.
  rewrite (cat_assoc PLT).
  generalize (Adjunction.adjoint_axiom2 PLT_adjoint B).
  simpl. intros. rewrite H0.
  apply cat_ident2.
Qed.  

Lemma strict_curry_app (Γ:PLT) (A B:∂PLT) 
  (f : Γ×U A → U B) (g : Γ → U A) (Hg: semvalue g) :
  strict_app A B ∘ PLT.pair (strict_curry Γ A B f) g ≈ f ∘ PLT.pair id g.
Proof.
  generalize (strict_curry_app2 Γ Γ A B f g id Hg).
  rewrite (cat_ident1 PLT). auto.
Qed.

Lemma strict_curry_app2' D (Γ:PLT) (A B:∂PLT) 
  (f : Γ×U A → U B) (g : D → U A) (h:D → Γ) (Hg : semvalue g) :

  strict_app' A B ∘ PLT.pair (strict_curry' Γ A B f ∘ h) g ≈ f ∘ PLT.pair h g.
Proof.
  unfold strict_curry'.
  unfold strict_app'.
  rewrite <- (cat_assoc PLT).
  rewrite <- (PLT.pair_map_pair false _ _ _ _ _ (η ∘ strict_curry Γ A B f ∘ h) (U·ε) g id).
  rewrite (cat_assoc PLT).
  rewrite (cat_assoc PLT).
  rewrite (cat_ident2 PLT).
  generalize (Adjunction.adjoint_axiom2 PLT_adjoint (A ⊸ B)).
  intros. simpl in H. rewrite H.
  rewrite (cat_ident2 PLT).
  apply strict_curry_app2. auto.
Qed.

Lemma strict_curry_app' (Γ:PLT) (A B:∂PLT) 
  (f : Γ×U A → U B) (g : Γ → U A) (Hg : semvalue g) :

  strict_app' A B ∘ PLT.pair (strict_curry' Γ A B f) g ≈ f ∘ PLT.pair id g.
Proof.
  generalize (strict_curry_app2' Γ Γ A B f g id Hg).
  rewrite (cat_ident1 PLT). auto.
Qed.


Lemma plt_strict_compose : forall (A B C:∂PLT) (f:B → C),
  f ∘ (⊥: A → B) ≈ ⊥.
Proof.
  intros. split. 2: apply bottom_least.
  hnf. intros.
  destruct a. apply PLT.compose_hom_rel in H.
  destruct H as [y [??]].
  simpl in H.
  apply union_axiom in H. destruct H as [X[??]].
  apply image_axiom2 in H. destruct H as [q [??]].
  apply empty_elem in H. elim H.
Qed.


Lemma strict_app_bot (Γ:PLT) (A B:∂PLT) (f:Γ → U (A ⊸ B)) :
  strict_app A B ∘ 〈f,⊥〉 ≈ ⊥.
Proof.
  unfold strict_app.
  rewrite <- (cat_assoc PLT).

  generalize (NT.axiom adj_unit).
  intros. simpl in H.
  rewrite H.
  rewrite (cat_assoc PLT).
  rewrite <- (Functor.compose U). 2: reflexivity.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- lift_prod_pair'.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (PLT.pair_map_pair true).
  etransitivity.
  apply cat_respects. 2: reflexivity.
  apply Functor.respects.
  etransitivity.
  apply cat_respects. reflexivity.
  2: apply plt_strict_compose.
  etransitivity.
  apply PLT.pair_eq. reflexivity.
  2: apply pair_bottom1.
  generalize (NT.axiom adj_counit). 
  simpl; intros.
  unfold plt_hom_adj'. simpl.
  rewrite (Functor.compose L). 2: reflexivity.
  rewrite (cat_assoc ∂PLT).
  rewrite H0. 
  rewrite <- (cat_assoc ∂PLT).
  generalize (Adjunction.adjoint_axiom1 PLT_adjoint Γ).
  intros. simpl in H1. rewrite H1.
  apply cat_ident1.
  auto.
Qed.

Lemma strict_app_bot' (Γ:PLT) (A B:∂PLT) (f:Γ → U (colift (A ⊸ B))) :
  strict_app' A B ∘ PLT.pair f ⊥ ≈ ⊥.
Proof.
  unfold strict_app'.
  rewrite <- (cat_assoc PLT).
  transitivity (strict_app A B ∘ 〈U·ε ∘ f, id ∘ ⊥〉).
  apply cat_respects; auto.
  symmetry. apply PLT.pair_map_pair.
  rewrite (cat_ident2 PLT).
  apply strict_app_bot.
Qed.

Program Definition precompose hf (A B C:PLT.PLT hf) (f:A → B) :
  (Preord.hom (PLT.hom_ord hf B C) (PLT.hom_ord hf A C)) := 
  Preord.Hom (PLT.hom_ord hf B C) (PLT.hom_ord hf A C) (fun g => g ∘ f) _.
Next Obligation.
  intros. apply PLT.compose_mono; auto.
Qed.
Arguments precompose [hf A B] C f.

Program Definition postcompose hf (A B C:PLT.PLT hf) (g:B → C) :
  (Preord.hom (PLT.hom_ord hf A B) (PLT.hom_ord hf A C)) :=
  Preord.Hom (PLT.hom_ord hf A B) (PLT.hom_ord hf A C) (fun f => g ∘ f) _.
Next Obligation.
  intros. apply PLT.compose_mono; auto.
Qed.
Arguments postcompose [hf] A [B C] g.

Lemma prove_continuous (CL:color) (A B:CPO.type CL) (f:Preord.hom A B) :
  (forall X:cl_eset CL A, f (∐X) ≤ ∐(image f X)) ->
  CPO.continuous f.
Proof.
  repeat intro.
  split; repeat intro.
  apply image_axiom2 in H1. destruct H1 as [q[??]].
  rewrite H2. apply Preord.axiom.
  apply H0; auto.
  transitivity (f (∐XS)).
  apply Preord.axiom.
  destruct H0. apply H2.
  apply CPO.sup_is_ub.
  transitivity (∐(image f XS)). apply H.
  apply CPO.sup_is_least. auto.
Qed.

Lemma precompose_continuous hf (A B C:PLT.PLT hf) (f:A → B) :
  CPO.continuous (precompose C f).
Proof.
  apply prove_continuous.
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
  CPO.continuous (postcompose A g).
Proof.
  apply prove_continuous.
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
  CPO.continuous (pair_right B f).
Proof.
  apply prove_continuous.
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
  CPO.continuous (pair_left A g).
Proof.
  apply prove_continuous.
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

Lemma continuous_sequence hf (A B C:dcpo hf)
  (g:Preord.hom B C) (f:Preord.hom A B) :
  CPO.continuous g -> CPO.continuous f -> CPO.continuous (g ∘ f).
Proof.
  repeat intro. 
  cut (least_upper_bound (g (f lub)) (image g (image f XS))).
  intros [??]; split; repeat intro.
  apply H2. apply image_axiom2 in H4.
  destruct H4 as [q [??]]. simpl in H5.
  rewrite H5.
  apply image_axiom1'. exists (f q); split; auto.
  apply image_axiom1'. exists q; split; auto.
  apply H3. repeat intro.
  apply H4.
  apply image_axiom2 in H5.
  destruct H5 as [y [??]].
  apply image_axiom2 in H5.
  destruct H5 as [y' [??]].
  apply image_axiom1'. exists y'.
  split; auto.
  simpl.
  rewrite H6.
  rewrite H7. auto.

  apply H. apply H0. auto.
Qed.

Lemma continuous_equiv hf (A B:dcpo hf) (f f':Preord.hom A B) :
  f ≈ f' -> CPO.continuous f -> CPO.continuous f'.
Proof.
  unfold CPO.continuous. intros.
  destruct (H0 lub XS); auto.
  split; repeat intro.
  rewrite <- H. apply H2.
  apply image_axiom2 in H4.
  destruct H4 as [q [??]].
  apply image_axiom1'. exists q. split; auto.
  rewrite H; auto.
  rewrite <- H. apply H3.
  repeat intro. apply H4.
  apply image_axiom2 in H5.
  destruct H5 as [q [??]].
  apply image_axiom1'. exists q. split; auto.
  rewrite <- H; auto.  
Qed.


Section fixes.
  Variable Γ:PLT.
  Variable A:∂PLT.
  Variable f:Γ → U A ⇒ U A.

  Definition fixes_step
    (x:Γ → U A) : Γ → U A :=

    PLT.app ∘ PLT.pair f x.

  Program Definition fixes_step' : PLT.homset_cpo _ Γ (U A) → PLT.homset_cpo _ Γ (U A) :=
    CPO.Hom _ (PLT.homset_cpo _ Γ (U A)) (PLT.homset_cpo _ Γ (U A)) fixes_step _ _.
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
    fixes ≈ PLT.app ∘ PLT.pair f fixes.
  Proof.
    unfold fixes at 1.
    rewrite <- lfp_fixpoint. simpl. unfold fixes_step.
    auto.
  Qed.

End fixes.

Arguments strict_app [A B].
Arguments strict_curry [Γ A B] f.

Arguments strict_app' [A B].
Arguments strict_curry' [Γ A B] f.

(*
Lemma hom_rel_pair hf (A B C:PLT.PLT hf) (f:C → A) (g:C → B) c x y :
  (c,(x,y)) ∈ PLT.hom_rel (PLT.pair f g) <->
  ((c,x) ∈ PLT.hom_rel f /\ (c,y) ∈ PLT.hom_rel g).
Proof.
  simpl; split; intros.
  apply pair_rel_elem in H. auto.
  apply pair_rel_elem; auto.
Qed.
*)

Lemma hom_rel_pair_map hf (A B C D:PLT.PLT hf) (f:A → C) (g:B → D) x y x' y' :
  (x,y,(x',y')) ∈ PLT.hom_rel (PLT.pair_map f g) <->
  ((x,x') ∈ PLT.hom_rel f /\ (y,y') ∈ PLT.hom_rel g).
Proof.
  unfold PLT.pair_map.
  split; intros.
  rewrite (PLT.pair_hom_rel _ _ _ _ (f∘π₁) (g∘π₂) (x,y) x' y') in H.
  destruct H.
  apply PLT.compose_hom_rel in H.
  destruct H as [?[??]].
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [?[??]].
  simpl in H. 
  rewrite (pi1_rel_elem _ _ _ _ x y x0)  in H.
  simpl in H0.
  rewrite (pi2_rel_elem _ _ _ _ x y x1) in H0.
  split.
  revert H1. apply PLT.hom_order; auto.
  revert H2. apply PLT.hom_order; auto.
  rewrite (PLT.pair_hom_rel _ _ _ _ (f∘π₁) (g∘π₂)).
  destruct H.
  split.
  apply PLT.compose_hom_rel.
  exists x. split; auto. simpl. apply pi1_rel_elem; auto.
  apply PLT.compose_hom_rel.
  exists y. split; auto. simpl. apply pi2_rel_elem; auto.
Qed.

Definition flat_cases' (X:enumtype) (Γ:PLT) (B:∂PLT) (f:X -> Γ → U B)
  : (Γ × U (flat X))%plt → U B
  := U·(flat_cases (fun x => ε ∘ L·(f x)) ∘ PLT.pair_map id ε ∘ lift_prod') ∘ η.
Arguments flat_cases' [X Γ B] f.

Definition flat_elem' (X:enumtype) (Γ:PLT) (x:X) : Γ → U (flat X)
  := U·(flat_elem x ∘ PLT.terminate _ _) ∘ η.
Arguments flat_elem' [X Γ] x.


Lemma flat_cases_elem_term (X:enumtype) (Γ D B:∂PLT) 
  (f:X -> Γ → B) (x:X) (h:D → Γ) :
  flat_cases f ∘ PLT.pair h (flat_elem x ∘ PLT.terminate true D) ≈ f x ∘ h.
Proof.
  split; intros a H. destruct a.
  apply PLT.compose_hom_rel in H.
  apply PLT.compose_hom_rel.
  destruct H as [q [??]].
  destruct q.
  simpl in H0.
  rewrite <- (flat_cases_rel_elem _ _ _ f) in H0.
  rewrite (PLT.pair_hom_rel _ _ _ _ _ _ c c1 c2) in H. destruct H.
  rewrite PLT.compose_hom_rel in H1.
  destruct H1 as [[] [??]].
  exists c1. split; auto.
  simpl in H2.
  apply single_axiom in H2.
  destruct H2 as [[??][??]]. simpl in *.
  hnf in H3. subst c2. auto.
  destruct a.
  apply PLT.compose_hom_rel in H.
  apply PLT.compose_hom_rel.
  destruct H as [q [??]].
  exists (q,x). split.
  apply PLT.pair_hom_rel. split; auto.
  apply PLT.compose_hom_rel. exists tt.
  split; auto.
  simpl. apply eprod_elem. split.
  apply eff_complete.
  apply single_axiom. auto.
  simpl. apply single_axiom. auto.
  apply (flat_cases_rel_elem).
  auto.   
Qed.

Lemma flat_cases_elem' (X:enumtype) (Γ D:PLT) (B:∂PLT) 
  (f:X -> Γ → U B) (x:X) (h:D → Γ) :
  flat_cases' f ∘ PLT.pair h (flat_elem' x) ≈ f x ∘ h.
Proof.
  unfold flat_cases'.
  rewrite <- (cat_assoc PLT).
  rewrite (NT.axiom adj_unit (PLT.pair h (flat_elem' x))).
  rewrite (cat_assoc PLT).
  simpl. rewrite <- (Functor.compose U). 2: reflexivity.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- lift_prod_pair'.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (PLT.pair_map_pair true).
  unfold flat_elem'.
  rewrite (Functor.compose L _ _ _ (U·(flat_elem x ∘ PLT.terminate true (L D)))).
  2: reflexivity.
  rewrite (cat_assoc ∂PLT).
  generalize (NT.axiom adj_counit (flat_elem x ∘ PLT.terminate true (L D))).
  simpl; intros. rewrite H. clear H.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (cat_assoc ∂PLT).
  generalize (Adjunction.adjoint_axiom1 PLT_adjoint D).
  simpl; intros.
  rewrite H.
  rewrite (cat_ident2 ∂PLT).
  rewrite (cat_ident1 ∂PLT).
  rewrite flat_cases_elem_term.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (Functor.compose L). 2: reflexivity.
  rewrite (Functor.compose U). 2: reflexivity.
  rewrite <- (cat_assoc PLT).
  rewrite <- (NT.axiom adj_unit (f x ∘ h)).
  rewrite (cat_assoc PLT).
  generalize (Adjunction.adjoint_axiom2 PLT_adjoint B).
  simpl; intros. rewrite H0.
  apply cat_ident2.
Qed.


Lemma semvalue_le : forall Γ A (f f':Γ → U A),
  f ≤ f' -> semvalue f -> semvalue f'.
Proof.
  repeat intro.
  destruct (H0 g). exists x.
  apply H. auto.
Qed.

Lemma semvalue_equiv : forall Γ A (f f':Γ → U A),
  f ≈ f' -> semvalue f -> semvalue f'.
Proof.
  intros Γ A f f' H. apply semvalue_le; auto.
Qed.

Require Import Setoid.

Add Parametric Morphism Γ A :
  (@semvalue Γ A)
  with signature (eq_op _) ==> iff
    as semvalue_eq_morphism.
Proof.
  intros. split; apply semvalue_equiv; auto.
Qed.

Lemma eta_semvalue A B (f:A → B) :
  semvalue (η ∘ f).
Proof.
  repeat intro.
  destruct (PLT.hom_directed _ _ _ f g nil). hnf; auto.
  hnf. intros. apply nil_elem in H. elim H.
  destruct H. apply erel_image_elem in H0.
  exists x. 
  simpl NT.transform.
  simpl. apply compose_elem.
  apply PLT.hom_order.
  exists x. split; auto.
  apply adj_unit_rel_elem. auto.
Qed.

Lemma strict_curry'_semvalue Γ A B f :
  semvalue (@strict_curry' Γ A B f).
Proof.
  unfold strict_curry'.
  apply eta_semvalue.  
Qed.

Lemma strict_curry'_semvalue2 Γ A B C f (g:C → Γ) :
  semvalue (@strict_curry' Γ A B f ∘ g).
Proof.
  unfold strict_curry'.
  rewrite <- (cat_assoc PLT).
  apply eta_semvalue.  
Qed.


Lemma semvalue_strict_app_out1 A B C (f:C → U (A ⊸ B)) (x:C → U A) :
  semvalue (strict_app ∘ PLT.pair f x) ->
  semvalue f.
Proof.
  intros. red; intro.
  destruct (H g) as [a ?].
  rewrite (PLT.compose_hom_rel false _ _ _ _ strict_app g (Some a)) in H0.
  destruct H0 as [[f' x'] [??]].
  rewrite (PLT.pair_hom_rel _ _ _ _ f x) in H0.
  destruct H0.
  unfold strict_app in H1.
  rewrite (PLT.compose_hom_rel false _ _ _ η 
    (U·(PLT.app ∘ PLT.pair_map ε ε ∘ @lift_prod' (U (A ⊸ B)) (U A)))) in H1.
  destruct H1 as [q [??]].
  simpl in H1.
  apply adj_unit_rel_elem in H1.
  rewrite (U_hom_rel _ _ _ q (Some a)) in H3.
  destruct H3. discriminate.
  destruct H3 as [p' [q' [?[??]]]]. subst q. inversion H5; subst.
  apply PLT.compose_hom_rel in H3.
  destruct H3 as [[??][??]].
  simpl in H3. apply ident_elem in H3.
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [[??][??]].
  rewrite (hom_rel_pair_map _ _ _ _ _ _ _ c c0 c1 c2) in H4.
  destruct H4.
  simpl in H4. apply adj_counit_rel_elem in H4.
  destruct c. 2: elim H4.
  destruct H1. simpl in H1.
  destruct H3. simpl in H3.
  rewrite <- H3 in H1. destruct f'.
  exists c3. auto.
  elim H1.
Qed.

Lemma semvalue_strict_app_out2 A B C (f:C → U (A ⊸ B)) (x:C → U A) :
  semvalue (strict_app ∘ PLT.pair f x) ->
  semvalue x.
Proof.
  intros. red; intro.
  destruct (H g) as [a ?].
  rewrite (PLT.compose_hom_rel false _ _ _ _ strict_app g (Some a)) in H0.
  destruct H0 as [[f' x'] [??]].
  rewrite (PLT.pair_hom_rel _ _ _ _ f x) in H0.
  destruct H0.
  unfold strict_app in H1.
  rewrite (PLT.compose_hom_rel false _ _ _ η 
    (U·(PLT.app ∘ PLT.pair_map ε ε ∘ @lift_prod' (U (A ⊸ B)) (U A)))) in H1.
  destruct H1 as [q [??]].
  simpl in H1.
  apply adj_unit_rel_elem in H1.
  rewrite (U_hom_rel _ _ _ q (Some a)) in H3.
  destruct H3. discriminate.
  destruct H3 as [p' [q' [?[??]]]]. subst q. inversion H5; subst.
  apply PLT.compose_hom_rel in H3.
  destruct H3 as [[??][??]].
  simpl in H3. apply ident_elem in H3.
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [[??][??]].
  rewrite (hom_rel_pair_map _ _ _ _ _ _ _ c c0 c1 c2) in H4.
  destruct H4.
  simpl in H7. apply adj_counit_rel_elem in H7.
  destruct c0. 2: elim H7.
  destruct H1. simpl in H1.
  destruct H3. simpl in H3.
  rewrite <- H9 in H8. simpl in H8.
  destruct x'. exists c3. auto.
  elim H8.
Qed.

Lemma semvalue_app_out1' A B C (f:C → U (colift (A ⊸ B))) (x:C → U A) :
  semvalue (strict_app' ∘ PLT.pair f x) ->
  semvalue f.
Proof.
  intros.
  unfold strict_app' in H.
  rewrite <- (cat_assoc PLT) in H.
  rewrite <- (PLT.pair_map_pair false _ _ _ _ _ f (U·ε) x id) in H.
  apply semvalue_strict_app_out1 in H.
  red; intros.
  destruct (H g) as [a ?].
  rewrite (PLT.compose_hom_rel _ _ _ _ f (U·ε) g (Some a)) in H0.
  destruct H0 as [q [??]].
  rewrite (U_hom_rel _ _ _ q (Some a)) in H1.
  destruct H1. discriminate.
  destruct H1 as [?[?[?[??]]]]. subst.
  exists x0. auto.
Qed.

Lemma semvalue_app_out2' A B C (f:C → U (colift (A ⊸ B))) (x:C → U A) :
  semvalue (strict_app' ∘ PLT.pair f x) ->
  semvalue x.
Proof.
  intros.
  unfold strict_app' in H.
  rewrite <- (cat_assoc PLT) in H.
  rewrite <- (PLT.pair_map_pair false _ _ _ _ _ f (U·ε) x id) in H.
  apply semvalue_strict_app_out2 in H.
  rewrite (cat_ident2 PLT) in H. auto.
Qed.

Lemma flat_elem'_semvalue : forall (X:enumtype) Γ (x:X),
  @semvalue Γ (flat X) (flat_elem' x).
Proof.
  intros. intro a. exists x.
  unfold flat_elem'.
  apply (PLT.compose_hom_rel _ _ _ _ η (U·(flat_elem x ∘ PLT.terminate true (L Γ)))
    a (Some x)).
  exists (Some a).   split.
  simpl. apply adj_unit_rel_elem. auto.
  apply U_hom_rel.
  right. exists a. exists x. split; auto.
  apply (PLT.compose_hom_rel _ _ _ _ ).
  exists tt. split.
  simpl. apply eprod_elem. split.
  apply eff_complete. apply single_axiom; auto.
  simpl. apply single_axiom. auto.
Qed.

Lemma flat_elem_canon : forall (X:enumtype) (g:PLT.unit _ → U (flat X)),
  semvalue g -> exists x, g ≈ flat_elem' x.
Proof.
  intros. destruct (H tt).
  exists x. split; hnf; intros.
  unfold flat_elem'.
  destruct a.
  apply PLT.compose_hom_rel.
  exists (Some c). split.
  simpl. apply adj_unit_rel_elem. auto.
  apply U_hom_rel.
  destruct c0; auto.
  destruct c.
  right.
  exists tt. exists c0.
  split; auto.
  apply PLT.compose_hom_rel.
  exists tt. split.
  simpl. apply eprod_elem.
  split. apply eff_complete. apply single_axiom; auto.
  simpl. apply single_axiom.
  assert (c0 = x).
  destruct (PLT.hom_directed _ _ _ g tt (Some x::Some c0::nil)).
  hnf. auto.
  hnf; intros.
  apply cons_elem in H2. destruct H2. rewrite H2.
  apply erel_image_elem; auto.
  apply cons_elem in H2. destruct H2. rewrite H2.
  apply erel_image_elem; auto.
  apply nil_elem in H2. elim H2.
  destruct H2.  
  apply erel_image_elem in H3.
  assert (Some x ≤ x0). apply H2.
  apply cons_elem; auto.
  assert (Some c0 ≤ x0). apply H2.
  apply cons_elem; auto. right.
  apply cons_elem; auto.
  destruct x0. hnf in H4. hnf in H5. subst c; auto.
  elim H4.
  subst c0. auto.
  destruct a.

  unfold flat_elem' in H1.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [y [??]].
  simpl in H1. apply adj_unit_rel_elem in H1.
  apply U_hom_rel in H2.
  destruct c.
  destruct H2.
  subst c0.
  revert H0. apply (PLT.hom_order _ _ _ g). auto.
Transparent U. hnf. auto. Opaque U. 
  destruct H2 as [p [q [?[??]]]].
  subst y c0.
  destruct p.
  apply PLT.compose_hom_rel in H2.
  destruct H2 as [?[??]].
  simpl in H3.
  apply single_axiom in H3.
  destruct H3 as [[??][??]]. simpl in *.
  hnf in H6. subst q. auto.
Qed.
