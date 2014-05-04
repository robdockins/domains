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
Require Import flat.

(** * Strict functions and applications lifted into PLT

    We give operators for strict functions and applications
    in PLT.  This takes two forms: a direct one and another
    one with lifted functions.
  *)

Definition strict_app (A B:∂PLT) 
  : U (A ⊸ B) × U A → U B

  := U·(apply ∘ PLT.pair_map ε ε ∘ lift_prod') ∘ η.

Definition strict_curry (Γ:PLT) (A B:∂PLT)
  (f:Γ×U A → U B) : Γ → U (A ⊸ B) 

  := U·(Λ( ε ∘ L·f ∘ lift_prod ∘ PLT.pair_map id γ)) ∘ η.
  
Definition strict_app' (A B:∂PLT) 
  : U (colift (A ⊸ B)) × U A → U B 

  := strict_app A B ∘ PLT.pair_map (U·ε) id.

Definition strict_curry' (Γ:PLT) (A B:∂PLT)
  (f:Γ × U A → U B) : Γ → U (colift (A ⊸ B))

  := η ∘ strict_curry Γ A B f.

Arguments strict_app [A B].
Arguments strict_curry [Γ A B] f.

Arguments strict_app' [A B].
Arguments strict_curry' [Γ A B] f.

Definition semvalue (Γ:PLT) (A:∂PLT) (f:Γ → U A) :=
  forall g, exists a, (g,Some a) ∈ PLT.hom_rel f.
Arguments semvalue [Γ A] f.

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

(**  Bottom is not a semantic value. *)
Lemma plt_semvalue_bot (Γ:PLT) (A:∂PLT) (x:Γ) :
  semvalue (⊥ : Γ → U A) -> False.
Proof.  
  intros.
  red in H.
  destruct (H x).
  simpl in H0.
  unfold plt_hom_adj' in H0.
  rewrite (PLT.compose_hom_rel false _ _ _ η (U·(cppo_bot (PLT.homset_cpo true (L Γ) A)))) in H0.
  destruct H0 as [y [??]].
  simpl in H0. apply adj_unit_rel_elem in H0.
  rewrite (U_hom_rel _ _ (cppo_bot (PLT.homset_cpo true (L Γ) A))) in H1.
  destruct H1. discriminate.
  destruct H1 as [?[?[?[??]]]].
  simpl in H1.
  apply union_axiom in H1.
  destruct H1 as [?[??]].
  apply image_axiom2 in H1.
  destruct H1 as [?[??]]. apply empty_elem in H1. auto.
Qed.

Lemma strict_curry_app2 D (Γ:PLT) (A B:∂PLT) 
  (f : Γ×U A → U B) (g : D → U A) (h:D → Γ)
  (Hg : semvalue g) :

  strict_app ∘ 〈strict_curry f ∘ h, g〉 ≈ f ∘ 〈h, g〉.
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
  apply adj_inv_eq. apply Hg.
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



Lemma strict_curry_app_converse (Γ:PLT) (A:∂PLT) 
  (g : Γ → U A) :
  (forall B (f : Γ×U A → U B),
    strict_app ∘ 〈strict_curry f, g〉 ≈ f ∘ 〈id, g〉) ->
  semvalue g.
Proof.
  intros.
  generalize (H 1 (plt_const false (Γ × U A) (U 1) (Some tt))).
  intros.
  intro x.
  destruct (PLT.hom_directed false Γ (U A) g x nil).
  hnf; auto.
  hnf; intros. apply nil_elem in H1. elim H1.
  destruct H1. clear H1.
  apply erel_image_elem in H2.
  assert ((x, Some tt) ∈ PLT.hom_rel (plt_const false (Γ × U A) (U 1) (Some tt) ∘ 〈id,g〉)).
  rewrite (PLT.compose_hom_rel false _ _ (U 1) _ _ x (Some tt)).
  exists (x,x0). split.
  apply PLT.pair_hom_rel.
  split. simpl. apply ident_elem; auto.
  auto.
  rewrite (plt_const_rel_elem _ (Γ × U A) (U 1) (Some tt)).
  auto.
  destruct H0.
  apply H3 in H1.
  clear H0 H3.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [[??][??]].
  rewrite (PLT.pair_hom_rel false _ _ _ _ _ x c c0) in H0.
  destruct H0.
  unfold strict_app in H1.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [?[??]].
  simpl in H1.
  apply adj_unit_rel_elem in H1.
  apply U_hom_rel in H4.
  destruct H4. discriminate.
  destruct H4 as [?[?[?[??]]]]. subst x1. inversion H6. subst.
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [?[??]].
  simpl in H4. apply ident_elem in H4.
  apply PLT.compose_hom_rel in H5.
  destruct H5 as [?[??]].
  destruct x3.
  apply (PLT.pair_hom_rel true _ _ _ _ _ x1 c1 c2) in H5.
  destruct H5.
  destruct x2. destruct x1.
  apply PLT.compose_hom_rel in H8.
  destruct H8 as [?[??]].
  simpl in H8. 
  apply (pi2_rel_elem _ _ _ _ c5 c6 x1) in H8.
  simpl in H9.
  apply adj_counit_rel_elem in H9.
  rewrite H8 in H9.
  destruct H4. simpl in *.
  rewrite H10 in H9.
  destruct H1. simpl in *.
  rewrite H11 in H9.
  destruct c0. eauto.
  elim H9.
Qed.  
  


Lemma strict_curry_app (Γ:PLT) (A B:∂PLT) 
  (f : Γ×U A → U B) (g : Γ → U A)
  (Hg: semvalue g) :
  strict_app ∘ 〈strict_curry f, g〉 ≈ f ∘ 〈id, g〉.
Proof.
  generalize (strict_curry_app2 Γ Γ A B f g id Hg).
  rewrite (cat_ident1 PLT). auto.
Qed.

Lemma strict_curry_app2' D (Γ:PLT) (A B:∂PLT) 
  (f : Γ×U A → U B) (g : D → U A) (h:D → Γ) 
  (Hg : semvalue g) :

  strict_app' ∘ 〈strict_curry' f ∘ h, g〉 ≈ f ∘ 〈h, g〉.
Proof.
  unfold strict_curry'.
  unfold strict_app'.
  rewrite <- (cat_assoc PLT).
  rewrite <- (PLT.pair_map_pair false _ _ _ _ _ (η ∘ strict_curry f ∘ h) (U·ε) g id).
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

  strict_app' ∘ 〈strict_curry' f, g〉 ≈ f ∘ 〈id, g〉.
Proof.
  generalize (strict_curry_app2' Γ Γ A B f g id Hg).
  rewrite (cat_ident1 PLT). auto.
Qed.

Lemma strict_curry_monotone Γ A B (f f':Γ×U A → U B) :
  f ≤ f' -> strict_curry f ≤ strict_curry f'.
Proof.
  intros. unfold strict_curry.
  apply PLT.compose_mono; auto.
  apply U_mono.
  apply PLT.curry_mono.
  apply PLT.compose_mono; auto.
  apply PLT.compose_mono; auto.
  apply PLT.compose_mono; auto.
Qed.

Lemma strict_curry'_monotone Γ A B (f f':Γ×U A → U B) :
  f ≤ f' -> strict_curry' f ≤ strict_curry' f'.
Proof.
  intros. unfold strict_curry'.
  apply PLT.compose_mono. 2: auto.
  apply strict_curry_monotone. auto.
Qed.

Lemma strict_curry_eq Γ A B (f f':Γ×U A → U B) :
  f ≈ f' -> strict_curry f ≈ strict_curry f'.
Proof.
  intros [??]; split; apply strict_curry_monotone; auto.
Qed.

Lemma strict_curry'_eq Γ A B (f f':Γ×U A → U B) :
  f ≈ f' -> strict_curry' f ≈ strict_curry' f'.
Proof.
  intros [??]; split; apply strict_curry'_monotone; auto.
Qed.

Add Parametric Morphism Γ A B :
  (@strict_curry Γ A B)
    with signature (Preord.ord_op _) ==> (Preord.ord_op _)
    as strict_curry_le_morphism.
Proof.
  intros. apply strict_curry_monotone; auto.
Qed.  

Add Parametric Morphism Γ A B :
  (@strict_curry' Γ A B)
    with signature (Preord.ord_op _) ==> (Preord.ord_op _)
    as strict_curry'_le_morphism.
Proof.
  intros. apply strict_curry'_monotone; auto.
Qed.  

Add Parametric Morphism Γ A B :
  (@strict_curry Γ A B)
    with signature (eq_op _) ==> (eq_op _)
    as strict_curry_morphism.
Proof.
  intros. apply strict_curry_eq; auto.
Qed.  

Add Parametric Morphism Γ A B :
  (@strict_curry' Γ A B)
    with signature (eq_op _) ==> (eq_op _)
    as strict_curry'_morphism.
Proof.
  intros. apply strict_curry'_eq; auto.
Qed.  


Lemma strict_curry_compose_commute Γ Γ' A B (f:Γ×U A → U B) (h:Γ' → Γ) :
  strict_curry f ∘ h ≈ strict_curry (f ∘ PLT.pair_map h id).
Proof.
  unfold strict_curry.
  rewrite <- (cat_assoc PLT).
  rewrite (NT.axiom adj_unit h).
  rewrite (cat_assoc PLT).
  apply cat_respects; auto.
  symmetry. apply (Functor.compose U).
  symmetry.
  rewrite PLT.curry_compose_commute.
  unfold PLT.pair_map at 2.
  apply PLT.curry_eq.
  repeat rewrite <- (cat_assoc ∂PLT).
  apply cat_respects. auto.
  rewrite <- (PLT.pair_map_pair true).
  rewrite (cat_ident2 ∂PLT).
  rewrite (cat_ident2 ∂PLT).
  symmetry.
  rewrite (Functor.compose). 2: reflexivity.
  rewrite <- (cat_assoc ∂PLT).
  apply cat_respects. auto.
  rewrite (cat_assoc ∂PLT).
  unfold pair_map.

  rewrite <- (lift_prod_natural _ _ _ _ h id).
  rewrite <- (cat_assoc ∂PLT).
  apply cat_respects. auto.
  unfold PLT.pair_map at 2.
  rewrite <- (PLT.pair_map_pair true).
  apply PLT.pair_eq.
  rewrite (cat_ident2 ∂PLT). auto.
  rewrite (Functor.ident L). 2: auto.
  rewrite (cat_ident2 ∂PLT). auto.
Qed.

Lemma strict_curry_compose_commute' Γ Γ' A B (f:Γ×U A → U B) (h:Γ' → Γ) :
  strict_curry' f ∘ h ≈ strict_curry' (f ∘ PLT.pair_map h id).
Proof.
  unfold strict_curry'.
  rewrite <- (cat_assoc PLT).
  rewrite (strict_curry_compose_commute _ _ _ _ f h).
  auto.
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
  strict_app ∘ 〈f,⊥〉 ≈ ⊥.
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
  strict_app' ∘ 〈f, ⊥〉 ≈ ⊥.
Proof.
  unfold strict_app'.
  rewrite <- (cat_assoc PLT).
  transitivity (strict_app ∘ 〈U·ε ∘ f, id ∘ ⊥〉).
  apply cat_respects; auto.
  symmetry. apply PLT.pair_map_pair.
  rewrite (cat_ident2 PLT).
  apply strict_app_bot.
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
  semvalue (strict_app ∘ 〈f, x〉) ->
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
  semvalue (strict_app ∘ 〈f, x〉) ->
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
  semvalue (strict_app' ∘ 〈f, x〉) ->
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
  semvalue (strict_app' ∘ 〈f, x〉) ->
  semvalue x.
Proof.
  intros.
  unfold strict_app' in H.
  rewrite <- (cat_assoc PLT) in H.
  rewrite <- (PLT.pair_map_pair false _ _ _ _ _ f (U·ε) x id) in H.
  apply semvalue_strict_app_out2 in H.
  rewrite (cat_ident2 PLT) in H. auto.
Qed.

(**  Lift the case analysis and element function for flat domains into PLT.
  *)
Definition flat_cases' (X:enumtype) (Γ:PLT) (B:∂PLT) (f:X -> Γ → U B)
  : (Γ × U (flat X))%plt → U B
  := U·(flat_cases (fun x => ε ∘ L·(f x)) ∘ PLT.pair_map id ε ∘ lift_prod') ∘ η.
Arguments flat_cases' [X Γ B] f.

Definition flat_elem' (X:enumtype) (Γ:PLT) (x:X) : Γ → U (flat X)
  := U·(flat_elem x ∘ PLT.terminate _ _) ∘ η.
Arguments flat_elem' [X Γ] x.


Lemma flat_cases_elem' (X:enumtype) (Γ D:PLT) (B:∂PLT) 
  (f:X -> Γ → U B) (x:X) (h:D → Γ) :
  flat_cases' f ∘ 〈h, flat_elem' x〉 ≈ f x ∘ h.
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
  rewrite flat_cases_elem.
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

Lemma flat_cases'_strict (X:enumtype) (Γ:PLT) (B:∂PLT) 
  (f:X -> Γ → U B) a x b :
  (a,x,b) ∈ PLT.hom_rel (flat_cases' f) -> x = None -> b = None.
Proof.
  intros.
  unfold flat_cases' in H.
  apply (PLT.compose_hom_rel _ _ _ _
    η
    (U·(flat_cases (fun x : X => ε ∘ L·f x) ∘ PLT.pair_map id ε ∘
      lift_prod'))
    (a,x) b) in H.
  destruct H as [?[??]].
  simpl in H. apply adj_unit_rel_elem in H.
  subst x.
  apply (U_hom_rel
    _ _
    (flat_cases (fun x : X => ε ∘ L·f x) ∘ PLT.pair_map id ε ∘
      lift_prod')) in H1.
  destruct H1; auto.
  destruct H0 as [?[?[??]]].
  destruct H1; subst.
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [?[??]].
  simpl in H0. apply ident_elem in H0.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [?[??]]. destruct x2.
  destruct x0.
  unfold PLT.pair_map in H1.
  apply (PLT.pair_hom_rel true (L Γ) (flat X) (L Γ ⊗ L (U (flat X))) (id ∘ π₁)
    (ε ∘ π₂)) in H1.
  destruct H1.
  apply PLT.compose_hom_rel in H3.
  destruct H3 as [?[??]].
  simpl in H3. 
  rewrite (pi2_rel_elem _ _ _ _ c1 c2 x0) in H3.
  simpl in H4.
  apply adj_counit_rel_elem in H4.
  rewrite H3 in H4.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [?[??]].
  simpl in H1.
  rewrite (pi1_rel_elem _ _ _ _ c1 c2 x2) in H1.
  simpl in H5. apply ident_elem in H5.
  destruct x. destruct H0. simpl in *.
  rewrite H6 in H4.
  destruct H. simpl in *.
  rewrite H7 in H4.
  elim H4.
Qed.
  
Lemma flat_cases'_semvalue (X:enumtype) A (Γ:PLT) (B:∂PLT) 
  (f:X -> Γ → U B) (g : A → Γ) h :
  semvalue (flat_cases' f ∘ 〈g,h〉) ->
  semvalue h.
Proof.
  repeat intro.
  hnf in H.
  destruct (H g0) as [??].
  rewrite (PLT.compose_hom_rel _ _ _ _ 〈g,h〉 (flat_cases' f)) in H0.
  destruct H0 as [?[??]].
  destruct x0.
  rewrite (PLT.pair_hom_rel _ _ _ _ g h) in H0.
  destruct H0.
  destruct c0.
  eauto.
  assert (Some x = None).
  eapply flat_cases'_strict.
  apply H1. auto.
  discriminate.
Qed.


Lemma flat_cases_univ' (X:enumtype) (A:PLT) (B:∂PLT) (f:X -> A → U B) 
  (q: A × U (flat X) → U B) :
  (forall a x b, (a,x,b) ∈ PLT.hom_rel q -> x = None -> b = None) ->
  (forall x, f x ≈ q ∘ 〈 id, flat_elem' x 〉) ->
  flat_cases' f ≈ q.
Proof.
  intro Hq0.
  intros. unfold flat_cases'.
  rewrite PLT.pair_map_eq.
  split; repeat intro.
  destruct a as [[a x] b]. 
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [z [??]].
  apply U_hom_rel in H1.
  destruct H1. subst b.
  destruct (PLT.hom_directed _ _ _ q (a,x) nil).
  hnf; auto. red; intros. apply nil_elem in H1. elim H1.
  destruct H1. apply erel_image_elem in H2.
  revert H2. apply PLT.hom_order; auto.
  destruct x0; simpl.
  exact I. exact I.
  destruct H1 as [m [n [??]]].  
  destruct H2. subst z b.
  simpl in H0.
  apply adj_unit_rel_elem in H0.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [?[??]].
  destruct x0.
  simpl in H1. apply ident_elem in H1.
  apply PLT.compose_hom_rel in H2.
  destruct H2 as [?[??]].
  destruct x0.
  rewrite (pair_rel_elem' _ _ _ _ (PLT.hom_rel id) (PLT.hom_rel ε)
    (PLT.hom_order _ _ _ _) 
    (PLT.hom_order _ _ _ _) 
    c c0 c1 c2) in H2.
  destruct H2.
  simpl in H2. apply ident_elem in H2.
  simpl in H4. apply adj_counit_rel_elem in H4.
  destruct c0. 2: elim H4.
  simpl in H3.  
  rewrite <- (flat_cases_rel_elem X (L A) B _ c2 c1 n) in H3.
  simpl in H3.
  apply PLT.compose_hom_rel in H3.
  destruct H3 as [?[??]].
  apply L_hom_rel in H3.
  destruct (H c2).
  apply H6 in H3.
  rewrite (PLT.compose_hom_rel false _ _ _ 〈id,flat_elem' c2〉 q) in H3.
  destruct H3 as [?[??]].
  destruct x1.
  apply (PLT.pair_hom_rel _ _ _ _ id(_) (flat_elem' c2) c1 c3) in H3.
  destruct H3. simpl in H3. apply ident_elem in H3.
  unfold flat_elem' in H9.
  apply PLT.compose_hom_rel in H9.
  destruct H9 as [?[??]].
  simpl in H9. apply adj_unit_rel_elem in H9.
  apply U_hom_rel in H10.
  destruct m; simpl in *.
  revert H8. apply PLT.hom_order; auto.
  split; simpl.
  rewrite H3. destruct H1. simpl in *.
  rewrite H2. rewrite H1. destruct H0; auto.
  destruct H10. subst c4. exact I.
  destruct H8 as [?[?[?[??]]]].
  subst.
  apply PLT.compose_hom_rel in H8.
  destruct H8 as [?[??]].
  simpl in H10.
  apply single_axiom in H10.
  destruct H10 as [[??][??]]. simpl in *.
  hnf in H13. subst c2.
  rewrite H4. destruct H1. simpl in *.
  rewrite H13. destruct H0; auto.
  apply adj_counit_rel_elem in H5.
  auto.

  destruct a as [[a x] b].

  destruct x as [x|].
  assert ((a,b) ∈ PLT.hom_rel (q ∘ 〈 id, flat_elem' x 〉)).
  apply PLT.compose_hom_rel.
  exists (a,Some x).
  split.
  apply PLT.pair_hom_rel.
  split. simpl. apply ident_elem. auto.
  unfold flat_elem'.
  apply PLT.compose_hom_rel.
  exists (Some a).
  split. simpl.
  apply adj_unit_rel_elem. auto.
  apply U_hom_rel.
  right. exists a. exists x.
  split; auto.
  apply PLT.compose_hom_rel.
  exists tt. split.
  simpl. apply eprod_elem.
  split. apply eff_complete. apply single_axiom; auto.
  simpl. apply single_axiom. auto.
  auto.
  destruct (H x). apply H3 in H1.
  apply PLT.compose_hom_rel.
  exists (Some (a,Some x)).
  split. simpl.
  apply adj_unit_rel_elem. auto.
  apply U_hom_rel.
  destruct b; auto.
  right.
  exists (a,Some x). exists c.
  split; auto.
  apply PLT.compose_hom_rel.
  exists (a, Some x).
  split.
  unfold lift_prod; simpl.
  apply ident_elem. auto.
  apply PLT.compose_hom_rel.
  exists (a,x). split; auto.
  simpl.
  rewrite (pair_rel_elem' _ _ _ _ _ _ (ident_ordering _ _) 
    (adj_counit_hom_obligation_1 _) a (Some x) a x).
  split. apply ident_elem; auto.
  apply adj_counit_rel_elem. auto.
  simpl.
  apply flat_cases_rel_elem.
  apply PLT.compose_hom_rel.
  exists (Some c).
  split.
  apply L_hom_rel.
  auto.
  apply adj_counit_rel_elem. auto.
  
  apply PLT.compose_hom_rel.
  exists (Some (a,None)).
  split.
  simpl. apply adj_unit_rel_elem. auto.
  apply U_hom_rel.
  assert (b = None).
  eapply Hq0; eauto.
  auto.
Qed.

Lemma flat_cases_commute : forall (X : enumtype) (A C : PLT) (B:∂PLT)
  (f : X -> A → U B) (g:C → A) (h:C → U (flat X)),
  flat_cases' f ∘ 〈g, h〉 ≈ flat_cases' (fun x => f x ∘ g) ∘ 〈id, h〉.
Proof.
  intros.
  transitivity (flat_cases' f ∘ PLT.pair_map g id ∘ 〈id,h〉).
  rewrite <- (cat_assoc PLT).
  rewrite <- (PLT.pair_map_pair false).
  rewrite (cat_ident1 PLT). rewrite (cat_ident2 PLT). auto.
  apply cat_respects; auto.
  symmetry. apply flat_cases_univ'.
  intros.

  apply (PLT.compose_hom_rel false _ _ _ (PLT.pair_map g id) (flat_cases' f)) in H.
  destruct H as [?[??]].
  unfold PLT.pair_map in H.
  destruct x0.
  rewrite (PLT.pair_hom_rel false _ _ _ (g ∘ π₁) (id ∘ π₂) (a,x) c c0) in H.
  destruct H.
  apply PLT.compose_hom_rel in H2.
  destruct H2 as [?[??]].
  simpl in H3. apply ident_elem in H3.
  simpl in H2.
  apply (pi2_rel_elem _ _ _ _ a x x0) in H2.
  subst x. destruct x0.
  elim H2.
  destruct c0. elim H3.
  eapply flat_cases'_strict.
  apply H1. auto.
  
  intros. rewrite <- (cat_assoc PLT).
  rewrite <- (PLT.pair_map_pair false).
  rewrite (cat_ident1 PLT).
  rewrite (cat_ident2 PLT).
  rewrite flat_cases_elem'. auto.
Qed.

Lemma flat_elem'_ignores_arg (X:enumtype) A B (x:X) (h:A → B) : 
  flat_elem' x ≈ flat_elem' x ∘ h.
Proof.
  unfold flat_elem'.
  symmetry.
  rewrite <- (cat_assoc PLT).
  rewrite (NT.axiom adj_unit h).
  rewrite (cat_assoc PLT).
  simpl.
  rewrite <- (Functor.compose U). 2: reflexivity.
  rewrite <- (cat_assoc ∂PLT).
  apply cat_respects; auto.
  apply Functor.respects.
  apply cat_respects; auto.
  split; hnf; intros.
  destruct a; simpl.
  apply eprod_elem. split.
  apply eff_complete. destruct c0. apply single_axiom. auto.
  destruct a.
  apply PLT.compose_hom_rel.
  destruct (PLT.hom_directed false A B h c nil) as [z ?]; auto.
  hnf. auto.
  red; intros. apply nil_elem in H0. elim H0.
  destruct H0.
  apply erel_image_elem in H1.
  exists z. split. apply L_hom_rel.  auto.
  simpl. apply eprod_elem.
  split. apply eff_complete. destruct c0.
  apply single_axiom; auto.
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

Lemma flat_elem_canon : forall (X:enumtype) (g:1 → U (flat X)),
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
  exact I.
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


Lemma flat_elem'_inj (X:enumtype) (x x':X) (A:PLT) (a:A) :
  @flat_elem' X A x ≈ flat_elem' x' -> x = x'.
Proof.
  intros.
  unfold flat_elem' in H.
  assert ((a, Some x) ∈ PLT.hom_rel (U·(flat_elem x ∘ PLT.terminate true (L A)) ∘ η)).
  rewrite (PLT.compose_hom_rel _ _ _ _ η 
    (U·(flat_elem x ∘ PLT.terminate true (L A)))).
  exists (Some a). split.
  simpl. apply adj_unit_rel_elem. auto.
  apply U_hom_rel.
  right. exists a. exists x. split; auto.
  rewrite (PLT.compose_hom_rel _ _ _ _ (PLT.terminate true (L A))
    (flat_elem x)).
  exists tt. split.
  simpl. apply eprod_elem. split. apply eff_complete.
  apply single_axiom. auto.
  simpl. apply single_axiom. auto.
  destruct H.
  apply H in H0.
  rewrite (PLT.compose_hom_rel _ _ _ _ η 
    (U·(flat_elem x' ∘ PLT.terminate true (L A)))) in H0.
  destruct H0 as [y[??]].
  simpl in H0. apply adj_unit_rel_elem in H0.
  apply (U_hom_rel _ _ 
    (flat_elem x' ∘ PLT.terminate true (L A))) in H2.
  destruct H2. discriminate.
  destruct H2 as [p [q [?[??]]]]. subst y. inversion H4; subst.
  rewrite (PLT.compose_hom_rel _ _ _ _ (PLT.terminate true (L A))
    (flat_elem x')) in H2.
  destruct H2 as [?[??]].
  simpl in H3.
  apply single_axiom in H3.
  destruct H3 as [[??][??]]. simpl in *.
  hnf in H5. auto.
Qed.
