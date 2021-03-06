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
Require Import embed.
Require Import joinable.
Require Import approx_rels.
Require Import profinite.
Require Import profinite_adj.
Require Import cont_functors.

(**  * Continuous adjoint functors

     Here we lift the lifting and forgetful adjoint functors into the
     category of embeddings and prove that they are continuous.
  *)

Definition forgetEMBED_map (A B:ob PLT) (f:A ⇀ B) : forgetPLT_ob A ⇀ forgetPLT_ob B :=
  Embedding true (forgetPLT_ob A) (forgetPLT_ob B) 
    (@embed_map false A B f)
    (@embed_mono false A B f)
    (@embed_reflects false A B f)
    (fun _ => I)
    (@embed_directed2 false A B f).

Program Definition forgetEMBED : functor (EMBED false) (EMBED true) :=
  Functor (EMBED false) (EMBED true) forgetPLT_ob forgetEMBED_map _ _ _.
Solve Obligations of forgetEMBED with auto.

Program Definition liftEMBED_map (A B:ob ∂PLT) (f:A ⇀ B) : liftPPLT_ob A ⇀ liftPPLT_ob B :=
  Embedding false (liftPPLT_ob A) (liftPPLT_ob B)
    (fun x => match x with None => None | Some a => Some (f a) end)
    _ _ _ _.
Next Obligation.
  simpl. intros.
  destruct a; destruct a'; simpl; auto.
  apply embed_mono. auto.
Qed.
Next Obligation.
  simpl. intros.
  destruct a; destruct a'; simpl; auto.
  apply embed_reflects with B f; auto.
Qed.
Next Obligation.
  intros. exists None. hnf. auto.
Qed.
Next Obligation.
  simpl. intros. 
  destruct a; destruct b.
  - destruct y. 
    + destruct embed_directed2 with true A B f c1 c c0 as [q [?[??]]]; auto.
      exists (Some q); auto.
    + elim H.
  - exists (Some c). auto.
  - exists (Some c). auto.
  - exists None. auto.
Qed.

Program Definition liftEMBED : functor (EMBED true) (EMBED false) :=
  Functor (EMBED true) (EMBED false) liftPPLT_ob liftEMBED_map _ _ _.
Next Obligation.
  intros. split; hnf; simpl; intros.
  - destruct x; simpl; auto.
    destruct H. apply H.
  - destruct x; simpl; auto.
    destruct H. apply H0.
Qed.
Next Obligation.
  intros. split; hnf; simpl; intros.
  - destruct x; auto. destruct H. apply H.
  - destruct x; auto. destruct H. apply H0.
Qed.
Next Obligation.
  intros. split; hnf; simpl; intros.
  - destruct x; auto. destruct H. apply H.
  - destruct x; auto. destruct H. apply H0.
Qed.

Require Import bilimit.

Lemma forgetEMBED_continuous : continuous_functor forgetEMBED.
Proof.
  hnf; intros.
  apply decompose_is_colimit; simpl.
  intros.
  destruct (colimit_decompose _ I DS CC X x) as [i [s H]].
  exists i. exists s. auto.
Qed.

Lemma liftEMBED_continuous : continuous_functor liftEMBED.
Proof.
  hnf; intros.
  apply decompose_is_colimit; simpl.
  intros.
  destruct x.
  - destruct (colimit_decompose _ I DS CC X c) as [i [s H]].
    exists i. exists (Some s). auto.
  - destruct (directed.choose_ub_set I nil) as [i0 ?].
    exists i0. exists None. auto.
Qed.
