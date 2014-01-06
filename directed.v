(* Copyright (c) 2014, Robert Dockins *)

Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import effective.

Definition inh {A:preord} (hf:bool) (X:finset A) := 
  if hf then exists x, x ∈ X else True.

Lemma inh_dec A hf (X:finset A) : { inh hf X } + {~inh hf X}.
Proof.
  destruct hf; simpl; auto.
  destruct X. right.
  intro. destruct H. apply nil_elem in H. auto.
  left. exists c. apply cons_elem; auto.
Qed.

Lemma inh_image A B hf (X:finset A) (f:A → B) :
  inh hf X <-> inh hf (image f X).
Proof.
  destruct hf; simpl; intuition.
  destruct H as [x ?].
  exists (f#x). apply image_axiom1. auto.
  destruct H as [x ?].
  apply image_axiom2 in H.
  destruct H as [y [??]].
  exists y. auto.
Qed.

Lemma inh_sub A hf (X Y:finset A) :
  X ⊆ Y -> inh hf X -> inh hf Y.
Proof.
  destruct hf; simpl; auto.
  intros. destruct H0 as [x ?].
  exists x. apply H; auto.
Qed.

Lemma inh_eq A hf (X Y:finset A) :
  X ≈ Y -> inh hf X -> inh hf Y. 
Proof.
  intros. apply inh_sub with X; auto.
  destruct H; auto.
Qed.

Lemma elem_inh A hf (X:finset A) x : x ∈ X -> inh hf X.
Proof.
  intros. destruct hf; simpl; eauto.
Qed.

Hint Resolve inh_sub elem_inh.

Lemma finset_sub_image (A B:preord) (T:set.theory) 
  (f:A → B) (X:set T A) (M:finset B) :
  M ⊆ image f X ->
  exists M', M ≈ image f M' /\ M' ⊆ X.
Proof.
  induction M; intros.
  exists nil. split; simpl; auto.
  hnf; simpl; intros. apply nil_elem in H0. elim H0.
  destruct IHM as [M' [??]].
  hnf; intros. apply H. apply cons_elem; auto.
  assert (a ∈ image f X). apply H. apply cons_elem. auto.
  apply image_axiom2 in H2.
  destruct H2 as [y [??]].
  exists (y::M')%list.
  split.
  split. hnf. simpl. intros.
  apply cons_elem in H4. destruct H4.
  apply cons_elem. left.
  rewrite H4; auto.
  apply cons_elem. right.
  rewrite H0 in H4. auto.
  hnf. simpl; intros.
  apply cons_elem in H4.
  apply cons_elem.
  destruct H4.
  left. rewrite H4; auto.
  right. rewrite H0. auto.
  hnf; simpl; intros.
  apply cons_elem in H4.
  destruct H4.
  rewrite H4; auto.
  apply H1; auto.
Qed.


Record directed_preord :=
  DirPreord
  { dir_preord :> preord
  ; dir_effective : effective_order dir_preord
  ; choose_ub_set : forall M:finset dir_preord, { k | upper_bound k M }
  }.
Arguments dir_preord _.
Arguments dir_effective _.
Arguments choose_ub_set _ _.

Lemma choose_ub (I:directed_preord) (i j:I) :
  { k | i ≤ k /\ j ≤ k }.
Proof.
  destruct (choose_ub_set I (i::j::nil)%list).
  exists x. split; apply u.
  apply cons_elem; auto.
  apply cons_elem; right.
  apply cons_elem; auto.
Qed.


Definition directed {T:set.theory} {A:preord} (hf:bool) (X:set T A) :=
  forall (M:finset A) (Hinh:inh hf M),
    M ⊆ X -> exists x, upper_bound x M /\ x ∈ X.

Lemma prove_directed (T:set.theory) (A:preord) (b:bool) (X:set T A) :
  (if b then True else exists x, x ∈ X) ->
  (forall x y, x ∈ X -> y ∈ X -> exists z, x ≤ z /\ y ≤ z /\ z ∈ X) ->
  directed b X.
Proof.
  intros. intro M.
  induction M.
  simpl; intros.
  destruct b; simpl in *.
  destruct Hinh. apply nil_elem in H2. elim H2.
  destruct H as [x ?]. exists x. split; auto.
  hnf. simpl; intros. apply nil_elem in H2. elim H2.
  intros.
  destruct M.
  exists a. split; auto.
  hnf; simpl; intros.
  apply cons_elem in H2. destruct H2.
  rewrite H2. auto.
  apply nil_elem in H2. elim H2.
  apply H1. apply cons_elem. auto.
  destruct IHM as [q [??]].
  destruct b; auto.
  hnf. exists c. apply cons_elem; auto.
  hnf; intros. apply H1; auto.
  apply cons_elem; auto.
  destruct (H0 a q) as [z [?[??]]]; auto.
  apply H1; auto. apply cons_elem; auto.
  exists z. split; auto.
  hnf; intros.
  apply cons_elem in H7.
  destruct H7. rewrite H7; auto.
  transitivity q; auto.
Qed.

Program Definition directed_hf_cl (hf:bool) : color :=
  Color (fun SL A X => @directed SL A hf X) _ _ _ _.
Next Obligation.    
  repeat intro.
  destruct (H0 M) as [x [??]]; auto.
  rewrite H; auto.
  exists x. split.
  hnf; intros.
  apply H2; auto.
  rewrite <- H; auto.
Qed.
Next Obligation.
  repeat intro.
  exists a. split; auto.
  hnf; intros. apply H in H0.
  apply single_axiom in H0. auto.
  apply single_axiom; auto.
Qed.
Next Obligation.
  repeat intro.
  destruct (finset_sub_image A B T f X M H0) as [M' [??]].
  destruct (H M') as [x [??]]; auto.
  rewrite (inh_image A B hf M' f).
  apply inh_eq with M; auto.
  exists (f#x); split; auto.
  hnf; intros.
  rewrite H1 in H5.
  apply image_axiom2 in H5.
  destruct H5 as [y [??]].
  rewrite H6.
  apply Preord.axiom.
  apply H3. auto.
  apply image_axiom1. auto.
Qed.
Next Obligation.
  intros.
  apply prove_directed.
  case_eq hf; auto. intros.
  destruct (H nil) as [X [??]].
  rewrite H1; hnf; auto.
  hnf; intros. apply nil_elem in H2. elim H2.
  destruct (H0 X H3 nil) as [x [??]].
  rewrite H1; hnf; auto.
  hnf; intros. apply nil_elem in H4. elim H4.
  exists x. apply union_axiom; eauto.
  intros.
  apply union_axiom in H1.
  apply union_axiom in H2.
  destruct H1 as [X1 [??]].
  destruct H2 as [X2 [??]].
  destruct (H (X1::X2::nil)%list) as [X [??]]; auto.
  apply elem_inh with X1; auto.
  apply cons_elem; auto.
  hnf; intros.
  apply cons_elem in H5. destruct H5.
  rewrite H5; auto.
  apply cons_elem in H5. destruct H5.
  rewrite H5; auto.
  apply nil_elem in H5; elim H5.
  destruct (H0 X H6 (x::y::nil)%list) as [z [??]]; auto.
  apply elem_inh with x; auto.
  apply cons_elem; auto.
  hnf; intros.
  apply cons_elem in H7. destruct H7.
  rewrite H7; auto.
  assert (X1 ≤ X).
  apply H5. apply cons_elem; auto.
  apply H8. auto.
  apply cons_elem in H7. destruct H7.
  rewrite H7; auto.
  assert (X2 ≤ X).
  apply H5.
  apply cons_elem; right.
  apply cons_elem; auto.
  apply H8. auto.
  apply nil_elem in H7. elim H7.
  exists z. split.
  apply H7. apply cons_elem; auto.
  split.
  apply H7.
  apply cons_elem; right.
  apply cons_elem; auto.
  apply union_axiom.
  exists X; split; auto.
Qed.

Definition semidirected_cl := directed_hf_cl true.
Definition directed_cl := directed_hf_cl false.


(**  The preorder of natural numbers with their arithmetic ordering
     is an effective, directed preorder.
  *)
Require Import Arith.
Require Import NArith.

Program Definition nat_ord := Preord.Pack nat (Preord.Mixin nat le _ _).
Solve Obligations using eauto with arith.
  
Program Definition nat_eff : effective_order nat_ord :=
  EffectiveOrder nat_ord le_dec (fun x => Some (N.to_nat x)) _.
Next Obligation.
  intros. exists (N.of_nat x).
  rewrite Nat2N.id. auto.
Qed.

Program Definition nat_dirord : directed_preord :=
  DirPreord nat_ord nat_eff _.
Next Obligation.  
  induction M.
  exists 0. hnf; intros. apply nil_elem in H. elim H.
  destruct IHM as [k ?].
  exists (max a k).
  hnf; intros.
  apply cons_elem in H. destruct H.
  rewrite H.
  red; simpl.
  apply Max.le_max_l.
  transitivity k.
  apply u. auto.
  red; simpl.
  apply Max.le_max_r.
Qed.
