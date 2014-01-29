(* Copyright (c) 2014, Robert Dockins *)

Require Import List.

Require Import basics.
Require Import categories.
Require Import preord.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import plotkin.
Require Import profinite.
Require Import embed.
Require Import joinable.
Require Import directed.
Require Import cont_functors.
Require Import bilimit.
Require Import exp_functor.
Require Import profinite_adj.
Require Import cont_adj.

(**  * Models of untyped λ-calculi
  *)

Definition cbvLamF : functor (EMBED true) (EMBED true)
  := expF true ∘ pairF id id.

Definition cbnLamF : functor (EMBED true) (EMBED true)
  := forgetEMBED ∘ expF false ∘ pairF id id ∘ liftEMBED.

Lemma cbvLamF_continuous : continuous_functor cbvLamF.
Proof.
  unfold cbvLamF.
  apply composeF_continuous.
  apply expF_continuous.
  apply pairF_continuous.
  apply identF_continuous.
  apply identF_continuous.
Qed.

Lemma cbnLamF_continuous : continuous_functor cbnLamF.
Proof.
  unfold cbnLamF.
  apply composeF_continuous.
  apply composeF_continuous.
  apply composeF_continuous.
  apply forgetEMBED_continuous.
  apply expF_continuous.
  apply pairF_continuous.
  apply identF_continuous.
  apply identF_continuous.
  apply liftEMBED_continuous.
Qed.

Definition lamModelCBV : ∂PLT := fixpoint cbvLamF.

Definition lamModelCBN : ∂PLT := fixpoint cbnLamF.

Lemma lamModelCBV_iso : (PLT.exp lamModelCBV lamModelCBV : ob (EMBED true)) ↔ lamModelCBV.
Proof.
  apply (fixpoint_iso cbvLamF).
  apply cbvLamF_continuous.
Qed.

Lemma lamModelCBN_iso : 
  (forgetPLT (PLT.exp (liftPPLT lamModelCBN) (liftPPLT lamModelCBN)) : ob (EMBED true)) 
  ↔ lamModelCBN.
Proof.
  apply (fixpoint_iso cbnLamF).
  apply cbnLamF_continuous.
Qed.


(* We can also directly construct a model of lambdas in total PLT...
     but this seems to be the trivial one-point model.

Program Definition lamModelIn : PLT.unit false ⇀ lamF false (PLT.unit false) :=
  Embedding false (PLT.unit false) (lamF false (PLT.unit false)) 
    (fun x => exist _ ((tt,tt)::nil) _) _ _ _ _.
Next Obligation.
  repeat intro.
  hnf. split. hnf; auto.
  simpl. intros. exists tt.
  destruct x0. split; auto.
  apply cons_elem. auto.
  hnf; simpl; intros.
  hnf; auto.
Qed.
Next Obligation.
  hnf; simpl; intros.
  red. hnf. simpl. intros.
  exists tt. exists tt.
  split.
  apply cons_elem; auto.
  split; hnf; auto.
Qed.
Next Obligation.
  repeat intro; hnf; auto.
Qed.
Next Obligation.
  intros. exists tt.
  simpl. hnf; auto.
  simpl; intros.
  exists tt. exists tt.
  split.
  destruct y. simpl.
  destruct i.
  simpl in H1.
  destruct (H1 x) with tt; auto.
  hnf; auto.
  split.
  hnf. intros; hnf; auto.
  intros; hnf; auto.
  destruct H2. destruct x0; auto.
  split; hnf; auto.
Qed.
Next Obligation.
  hnf; simpl. intros.
  exists tt.
  split; hnf; auto.
  split; hnf; auto.
Qed.

Definition lamModelCBN : ob PLT
  := fixpoint_alt (lamF false) (PLT.unit false) lamModelIn.

Lemma lamModelCBN_iso : (PLT.exp lamModelCBN lamModelCBN : ob (EMBED false)) ↔ lamModelCBN.
Proof.
  apply (fixpoint_alt_iso (lamF false)).
  apply lamF_continuous.
Qed.
*)