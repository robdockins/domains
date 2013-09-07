Require Import Setoid.
Require Import NArith.
Require Import List.

Require Import basics.
Require Import categories.
Require Import preord.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import plotkin.

(* FIXME move this *)
Lemma conj_dec (P Q:Prop) :
  {P}+{~P} -> 
  {Q}+{~Q} -> 
  { P /\ Q } + { ~(P /\ Q) }.
Proof.
  intros. destruct H. destruct H0.
  left; split; auto.
  right; intros [??]; auto.
  right; intros [??]; auto.
Qed.  


Local Open Scope N_scope.

Lemma N2_eq_dec : forall (x y:N*N), { x = y }+{x <> y}.
Proof.
  decide equality; apply N_eq_dec.
Qed.

Definition N2 := Ndisc_ord × Ndisc_ord.

Canonical Structure N2dec := OrdDec N2
  (eff_ord_dec _ (effective_prod effective_Nord effective_Nord)).

Lemma N2in : forall (l:finset N2) x y, In (x,y) l <-> (x,y) ∈ l.
Proof.
  intuition.
  exists (x,y). split; auto.
  destruct H as [q [??]].
  replace (x,y) with q; auto.
  destruct q.
  destruct H0.
  destruct H0.
  hnf in H0. hnf in H2. simpl in *.
  subst. auto.
Qed.

Notation N := Ndisc_ord.

Lemma finord_ord_dec1 (Y:finset N2) : forall (X:finset N2),
  { forall a b, (a,b) ∈ X -> (a,b) ∈ Y } +
  { exists a b, (a,b) ∈ X /\ ~(a,b) ∈ Y }.
Proof. 
  induction X; intros.
  left; simpl; intuition.
  apply nil_elem in H. elim H.
  destruct IHX.
  destruct a.
  destruct (in_dec N2_eq_dec (c,c0) Y).
  left; simpl; intuition.
  apply cons_elem in H.
  destruct H. rewrite H.
  apply N2in. auto.
  apply m; auto.
  right; eauto.  
  exists c. exists c0. split; simpl; auto.
  apply cons_elem; auto.
  intro. apply n. apply N2in. auto.
  right. destruct e as [p [q [??]]]; simpl; eauto.
  exists p. exists q. split; auto.
  apply cons_elem; auto.
Qed.

Lemma finord_ord_dec2 (Y:finset N2) : forall (X:finset N2),
  { forall a b, (a,b) ∈ X -> (a,a) ∈ Y -> (b,b) ∈ Y -> (a,b) ∈ Y } +
  { exists a b, (a,b) ∈ X /\ (a,a) ∈ Y /\ (b,b) ∈ Y /\ (a,b) ∉ Y }.
Proof. 
  induction X; intros.
  left; simpl; intuition.
  apply nil_elem in H. elim H.
  destruct IHX.
  destruct a.
  destruct (in_dec N2_eq_dec (c,c0) Y).
  left.
  simpl; intuition.
  apply cons_elem in H. destruct H.
  rewrite H; auto. apply N2in; auto.
  apply m; auto.
  destruct (in_dec N2_eq_dec (c,c) Y).
  destruct (in_dec N2_eq_dec (c0,c0) Y).
  right.
  exists c. exists c0.
  split.
  apply cons_elem; auto.
  split. apply N2in; auto.
  split. apply N2in; auto.
  intro. apply n. apply N2in; auto.
  left; intros.
  apply cons_elem in H. destruct H.
  elim n0.
  apply N2in.
  apply member_eq with (b,b); auto.
  destruct H as [[??][??]]; split; split; simpl in *; auto.
  apply m; auto.
  left; intros.
  apply cons_elem in H. destruct H.
  elim n0.
  apply N2in.
  apply member_eq with (a,a); auto.
  destruct H as [[??][??]]; split; split; simpl in *; auto.
  apply m; auto.
  right.
  destruct e as [p [q [?[??]]]].
  exists p. exists q; intuition.
  apply cons_elem; auto.
Qed.

Lemma preord_graph_dec1 : forall (G H:list (N*N)),
  { forall x y, In (x,y) G -> In (x,x) H }
  +
  { ~forall x y, In (x,y) G -> In (x,x) H }.
Proof.
  induction G; simpl; intros.
  left; intuition.
  destruct (IHG H).
  destruct a as [x y].
  destruct (in_dec N2_eq_dec (x,x) H).
  left; simpl; intuition.
  inversion H1; subst; auto.
  eapply i; eauto.
  right; repeat intro.
  apply n. eapply H0; eauto.
  right; repeat intro.  
  apply n; intros.
  eapply H0; eauto.
Qed.

Lemma preord_graph_dec2 : forall (G H:list (N*N)),
  { forall x y, In (x,y) G -> In (y,y) H }
  +
  { ~forall x y, In (x,y) G -> In (y,y) H }.
Proof.
  induction G; simpl; intros.
  left; intuition.
  destruct (IHG H).
  destruct a as [x y].
  destruct (in_dec N2_eq_dec (y,y) H).
  left; simpl; intuition.
  inversion H1; subst; auto.
  eapply i; eauto.
  right; repeat intro.
  apply n. eapply H0; eauto.
  right; repeat intro.  
  apply n; intros.
  eapply H0; eauto.
Qed.

Lemma preord_graph_dec3 : forall (G H I:list (N*N)),
  { forall x y z, In (x,y) G -> In (y,z) H -> In (x,z) I }
  +
  { ~forall x y z, In (x,y) G -> In (y,z) H -> In (x,z) I }.
Proof.
  induction G.
  left; simpl; intuition.
  induction H.
  left; simpl; intuition.
  intro I.
  destruct (IHG (a0::H) I).
  clear IHG.
  destruct (IHlist I).
  destruct a as [x y].  
  destruct a0 as [y' z].
  destruct (in_dec N2_eq_dec (x,z) I).
  left.
  simpl; intuition. inversion H2; inversion H0; subst; auto.
  eapply i0; simpl; eauto.
  eapply i; simpl; eauto.
  eapply i; simpl; eauto.
  destruct (N_eq_dec y y'). subst y'.
  right; repeat intro.
  apply n. eapply H0; simpl; eauto.
  left. simpl; intuition.
  inversion H2; inversion H0; subst.
  elim n0; auto.
  eapply i0; simpl; eauto.
  eapply i; simpl; eauto.
  eapply i0; simpl; eauto.
  right; repeat intro.
  apply n.
  intros. eapply H0; simpl; eauto.
  right; repeat intro.
  apply n.
  intros. eapply H0; simpl; eauto.
Qed.    

Lemma preord_graph_dec4 : forall (hf:bool) (G:list (N*N)),
  { if hf then G <> nil else True }
  +
  { ~if hf then G <> nil else True }.
Proof.
  destruct hf; auto.
  destruct G; simpl; auto.
  left. discriminate.
Qed.

Definition preord_graph (hf:bool) (G:finset N2) :=
  (forall x y, (x,y) ∈ G -> (x,x) ∈ G) /\
  (forall x y, (x,y) ∈ G -> (y,y) ∈ G) /\
  (forall x y z, (x,y) ∈ G -> (y,z) ∈ G -> (x,z) ∈ G) /\
  (if hf then exists x y, (x,y) ∈ G else True).
  
Lemma preord_graph_dec : forall hf G, { preord_graph hf G } + { ~preord_graph hf G }.
Proof.
  intros hf G.
  destruct (preord_graph_dec1 G G).
  destruct (preord_graph_dec2 G G).
  destruct (preord_graph_dec3 G G G).
  destruct (preord_graph_dec4 hf G).
  left. red; auto.
  split; intros.
  apply N2in. eapply i. apply N2in. eauto.
  split; intros.
  apply N2in. eapply i0. apply N2in. eauto.
  split; intros.
  apply N2in. eapply i1; apply N2in; eauto.
  destruct hf; auto.
  destruct G. elim y; auto.
  destruct c.
  exists c. exists c0. apply cons_elem; auto.
  right; intros [?[?[??]]]; apply n; auto.
  destruct hf; auto. destruct G; auto.
  destruct H2 as [p [q ?]]. apply nil_elem in H2. auto.
  discriminate.
  right; intros [?[?[??]]]; apply n; auto.
  intros. apply N2in. eapply H1; apply N2in; eauto.
  right; intros [?[?[??]]]; apply n; auto.
  intros. apply N2in. eapply H0; apply N2in; eauto.
  right; intros [?[?[??]]]; apply n; auto.
  intros. apply N2in. eapply H; apply N2in; eauto.
Qed.

Lemma preord_graph_intersect (hf:bool) (X Y:finset N2) :
  (if hf then exists a, a ∈ X /\ a ∈ Y else True) ->
  preord_graph hf X -> preord_graph hf Y ->
  preord_graph hf (fin_intersect N2 N2dec X Y).
Proof.
  repeat intro.
  destruct H0 as [?[?[??]]].
  destruct H1 as [?[?[??]]].
  split; intros.
  apply fin_intersect_elem in H8.
  apply fin_intersect_elem. destruct H8; split; auto.
  eapply H0; eauto.
  eapply H1; eauto.
  split; intros.
  apply fin_intersect_elem in H8.
  apply fin_intersect_elem. destruct H8; split; auto.
  eapply H2; eauto.
  eapply H5; eauto.
  split.
  intros.
  apply fin_intersect_elem in H8.
  apply fin_intersect_elem in H9.
  apply fin_intersect_elem.
  destruct H8. destruct H9.
  split; eauto.
  destruct hf; auto.
  destruct H as [a ?].
  destruct a.
  exists c. exists c0.
  apply fin_intersect_elem.
  destruct H. split; auto.
Qed.

Lemma preord_graph_ok hf : forall x y:finset N2, x ≈ y -> preord_graph hf x -> preord_graph hf y.
Proof.
  unfold preord_graph.
  intros. destruct H0 as [?[?[??]]].
  repeat split; intros.
  rewrite <- H. eapply H0. rewrite H. eauto.
  rewrite <- H. eapply H1. rewrite H. eauto.
  rewrite <- H. eapply H2; rewrite H; eauto.
  destruct hf; auto.
  destruct H3 as [p [q ?]]. exists p. exists q. rewrite <- H; auto.
Qed.

Definition finrel_image (R:finset N2) (x:N) : finset N :=
  image π₂ (finsubset N2 (fun q => π₁#q = x) (fun q => N_eq_dec (π₁#q) x) R).

Definition finrel_inv_image (R:finset N2) (y:N) : finset N :=
  image π₁ (finsubset N2 (fun q => π₂#q = y) (fun q => N_eq_dec (π₂#q) y) R).

Lemma finrel_image_elem : forall R x y,
  y ∈ finrel_image R x <-> (x,y) ∈ R.
Proof.  
  unfold finrel_image. intros.
  split; intros.
  apply image_axiom2 in H. destruct H as [[p q] [??]].
  apply finsubset_elem in H.
  destruct H. simpl in *.
  subst x.
  apply member_eq with (p,q); auto.
  split; split; auto.
  simpl; intros.
  subst x.
  destruct H1 as [[??][??]]; auto.
  apply image_axiom1'.
  exists (x,y). split; simpl; auto.
  apply finsubset_elem.
  simpl; intros. subst x.
  destruct H0 as [[??][??]]; auto.
  split; auto.
Qed.

Lemma finrel_inv_image_elem : forall R x y,
  x ∈ finrel_inv_image R y <-> (x,y) ∈ R.
Proof.  
  unfold finrel_inv_image. intros.
  split; intros.
  apply image_axiom2 in H. destruct H as [[p q] [??]].
  apply finsubset_elem in H.
  destruct H. simpl in *.
  subst y.
  apply member_eq with (p,q); auto.
  split; split; auto.
  simpl; intros.
  subst y.
  destruct H1 as [[??][??]]; auto.
  apply image_axiom1'.
  exists (x,y). split; simpl; auto.
  apply finsubset_elem.
  simpl; intros. subst y.
  destruct H0 as [[??][??]]; auto.
  split; auto.
Qed.

Definition finapprox_rel (hf:bool) (G1 G2 R:finset N2) :=
  (forall x y, (x,y) ∈ R -> (x,x) ∈ G1 /\ (y,y) ∈ G2) /\
  (forall x x' y y', (x,x') ∈ G1 -> (y',y) ∈ G2 -> (x,y) ∈ R -> (x',y') ∈ R) /\
  (forall x y1 y2, (x,y1) ∈ R -> (x,y2) ∈ R -> 
    exists y3, (y1,y3) ∈ G2 /\ (y2,y3) ∈ G2 /\ (x,y3) ∈ R) /\
  (if hf then True else forall x, (x,x) ∈ G1 -> exists y, (x,y) ∈ R).

Definition finrel_compose (G2 S R:finset N2) : finset N2 :=
  image (mk_pair (π₁ ∘ π₁) (π₂ ∘ π₂))
  (finsubset (N2×N2) (fun q => (fst (snd q),snd (fst q)) ∈ G2)
                     (fun q => finset_in_dec _ (OrdDec _ (eff_ord_dec _ 
   (effective_prod effective_Nord effective_Nord)))
                                G2 (fst (snd q),snd (fst q)))
   (finprod R S)).

Lemma finrel_compose_elem hf (G1 G2 G3 S R:finset N2) :
  finapprox_rel hf G1 G2 R ->
  finapprox_rel hf G2 G3 S ->
  forall x z,
    (x,z) ∈ finrel_compose G2 S R
    <->
    (exists y,
      (x,y) ∈ R /\ (y,z) ∈ S).
Proof.
  intros; split; intros.
  unfold finrel_compose in H1.
  apply image_axiom2 in H1.
  destruct H1 as [[p q] [??]].
  simpl in H2.
  apply finsubset_elem in H1.
  destruct H1 as [??]. simpl in H3. 
  apply finprod_elem in H1.
  destruct H1.
  exists (fst q).
  split.
  destruct H as [?[??]].
  apply H5 with (fst p) (snd p).
  replace x with (fst p).
  destruct p.
  apply H in H1. simpl. destruct H1; auto.
  destruct H2 as [[??][??]]; auto.
  auto.
  destruct p; auto.
  destruct H0 as [?[??]].
  apply H5 with (fst q) (snd q).
  destruct q. simpl in *.
  apply H0 in H4.
  destruct H4; auto.
  replace z with (snd q).
  destruct q. simpl in *.
  apply H0 in H4.
  destruct H4; auto.
  destruct H2 as [?[??]]; auto.
  destruct q; auto.
  simpl; intros.
  eapply member_eq. 2: apply H4.
  destruct H3 as [[[??][??]][[??][??]]]; split; split; auto.
  destruct H1 as [y [??]].  
  unfold finrel_compose.
  apply image_axiom1'.
  exists ((x,y),(y,z)).
  split; auto.
  apply finsubset_elem.
  simpl; intros.
  eapply member_eq. 2: apply H4.
  destruct H3 as [[[??][??]][[??][??]]]; split; split; auto.
  split; simpl.
  apply finprod_elem. split; auto.
  destruct H as [?[??]].
  apply H in H1. destruct H1; auto.
Qed.

Lemma finapprox_compose hf (G1 G2 G3 S R:finset N2) :
  finapprox_rel hf G1 G2 R ->
  finapprox_rel hf G2 G3 S ->
  finapprox_rel hf G1 G3 (finrel_compose G2 S R). 
Proof.
  intros.
  generalize H; intro H'.
  generalize H0; intro H0'.
  destruct H as [HR1 [HR2 [HR3 HR4]]].
  destruct H0 as [HS1 [HS2 [HS3 HS4]]].
  split; intros.
  rewrite finrel_compose_elem in H; eauto.
  destruct H as [y' [??]].
  apply HR1 in H.
  apply HS1 in H0.
  intuition.
  split; intros.
  rewrite finrel_compose_elem in H1; eauto.
  rewrite finrel_compose_elem; eauto.
  destruct H1 as [q [??]].
  exists q; split; auto.
  eapply HR2; eauto.
  apply HR1 in H1. destruct H1; auto.
  eapply HS2; eauto.
  apply HR1 in H1. destruct H1; auto.
  
  split; intros.
  rewrite finrel_compose_elem in H; eauto.
  rewrite finrel_compose_elem in H0; eauto.
  destruct H as [q1 [??]].
  destruct H0 as [q2 [??]].
  destruct (HR3 x q1 q2) as [q3 [?[??]]]; auto.
  destruct (HS3 q3 y1 y2) as [y3 [?[??]]]; auto.
  apply HS2 with q1 y1; auto.
  apply HS1 in H1. destruct H1; auto.
  apply HS2 with q2 y2; auto.
  apply HS1 in H2. destruct H2; auto.
  exists y3. split; auto. split; auto.
  rewrite finrel_compose_elem; eauto.
  
  destruct hf; auto.
  intros.
  destruct (HR4 x) as [y ?]; auto.
  destruct (HS4 y) as [z ?]; auto.
  apply HR1 in H0.   destruct H0; auto.
  exists z.
  rewrite finrel_compose_elem; eauto.
Qed.

Record fin_ep_pair hf (G1 G2 E P:finset N2) :=
  FinEP
  { finep_approx1 : finapprox_rel hf G1 G2 E
  ; finep_approx2 : finapprox_rel hf G2 G1 P
  ; finep_id1 : forall x y, (x,y) ∈ finrel_compose G2 P E <-> (y,x) ∈ G1
  ; finep_id2 : forall x y, (x,y) ∈ finrel_compose G1 E P  -> (y,x) ∈ G2
  }.


Definition finord hf := { G:finset N2 | preord_graph hf G }.

Definition finord_ord hf (X Y:finord hf) : Prop :=
  exists E P, fin_ep_pair hf (proj1_sig X) (proj1_sig Y) E P.

Definition finrel_inv (G:finset N2) : finset N2 :=
  image (mk_pair π₂ π₁) G.

Lemma finrel_inv_elem G : forall x y, (x,y) ∈ finrel_inv G <-> (y,x) ∈ G.
Proof.
  intros; split; intros.
  unfold finrel_inv in H.
  apply image_axiom2 in H. destruct H as [q [??]].
  destruct q. simpl in H0.
  apply member_eq with (c,c0); auto.
  destruct H0 as [[??][??]]; split; split; auto.  
  unfold finrel_inv.
  apply image_axiom1'. 
  exists (y,x). split; auto.
Qed.

Lemma finapprox_rel_dec hf G1 G2 R :
  { finapprox_rel hf G1 G2 R }+{ ~finapprox_rel hf G1 G2 R }.
Proof.
  unfold finapprox_rel. apply conj_dec.
  destruct (finset_find_dec' N2 (fun q => (fst q, fst q) ∈ G1 /\ (snd q, snd q) ∈ G2)) with R.
  intros.
  destruct H as [[??][??]].
  destruct H0; split; auto.
  apply member_eq with (fst x, fst x); auto.
  split; split; auto.
  apply member_eq with (snd x, snd x); auto.
  split; split; auto.

  intros. apply conj_dec; apply eff_in_dec; apply effective_prod; apply effective_Nord.
  destruct s as [z [??]].
  right; repeat intro.
  apply H0. auto.
  left; intros.
  apply (a (x,y)); auto.
  
  apply conj_dec.
  destruct (finset_find_dec' N2 (fun q => forall y' y, (y',y) ∈ G2 -> (fst q, y) ∈ R ->
     (snd q, y') ∈ R)) with G1.
  intros. apply member_eq with (snd x, y'); auto.
  destruct H as [[??][??]]; split; split; auto.
  apply H0 with y0; auto.
  apply member_eq with (fst y, y0); auto.
  destruct H as [[??][??]]; split; split; auto.
  intros [x x']. simpl.
  destruct (finset_find_dec' N2 (fun q => (x, snd q) ∈ R -> (x', fst q) ∈ R)) with G2.
  intros.
  apply member_eq with (x',fst x0).
  destruct H as [[??][??]]; split; split; auto.
  apply H0.
  apply member_eq with (x,snd y); auto.
  destruct H as [[??][??]]; split; split; auto.
  intros.  
  destruct (finset_in_dec N2 N2dec R (x, snd x0)).
  destruct (finset_in_dec N2 N2dec R (x',fst x0)).
  left; auto.
  right. repeat intro.
  apply n. apply H; auto.
  left. intro. contradiction.
  destruct s as [z [??]].   
  right; repeat intro.
  apply H0; intros.
  eapply H1; eauto.
  destruct z; auto.
  left; intros.  
  apply (m (y',y)); auto.
  destruct s as [z [??]].
  right; repeat intro. apply H0; intros.
  eapply H1; eauto.
  destruct z; auto.
  left; intros.
  eapply (m (x,x')); eauto.
  
  apply conj_dec.  
  destruct (finset_find_dec' N2 (fun q => forall y2, (fst q, y2) ∈ R ->
    exists y3, (snd q, y3) ∈ G2 /\ (y2,y3) ∈ G2 /\ (fst q, y3) ∈ R)) with R.
  intros.
  destruct (H0 y2) as [y3 [?[??]]].
  apply member_eq with (fst y,y2); auto.
  destruct H as [[??][??]]; split; split; auto.
  exists y3. split; auto.
  apply member_eq with (snd x,y3); auto.
  destruct H as [[??][??]]; split; split; auto.
  split; auto.  
  apply member_eq with (fst x,y3); auto.
  destruct H as [[??][??]]; split; split; auto.
  intros [x y1]. simpl.
  destruct (finset_find_dec' N 
    (fun y2 => exists y3, (y1,y3) ∈ G2 /\ (y2,y3) ∈ G2 /\ (x,y3) ∈ R)) with (finrel_image R x).
  intros.
  destruct H0 as [y3 [?[??]]]. exists y3; split; auto. split; auto.
  apply member_eq with (x0,y3); auto.
  destruct H; split; split; auto.
  intros y2.
  destruct (finset_find_dec N 
    (fun y3 => (y2,y3) ∈ G2 /\ (x,y3) ∈ R)) with (finrel_image G2 y1).
  intros.  
  destruct H0; split; auto.
  apply member_eq with (y2,x0); auto.
  destruct H; split; split; auto.
  apply member_eq with (x,x0); auto.
  destruct H; split; split; auto.
  intro y3.
  destruct (finset_in_dec N2 N2dec G2 (y2,y3)).
  destruct (finset_in_dec N2 N2dec R (x,y3)).
  left; auto.
  right; intros [??]; auto.
  right; intros [??]; auto.
  destruct s as [y3 [?[??]]].
  left. exists y3. split; auto.
  apply finrel_image_elem in H. auto.
  right; repeat intro.
  destruct H as [y3 [?[??]]].
  apply (n y3); auto.
  apply finrel_image_elem; auto.
  destruct s as [z [??]].
  right. repeat intro.
  apply H0; intros.
  apply H1. apply finrel_image_elem in H. auto.
  left. intros.
  apply (e y2). apply finrel_image_elem; auto.
  destruct s as [z [??]].
  right; repeat intro.
  apply H0. intros.
  eapply H1; eauto.
  left; intros.
  apply (e (x,y1)); auto.

  destruct hf; auto.
  destruct (finset_find_dec' N2
    (fun q => fst q ≈ snd q -> exists y, (fst q, y) ∈ R)) with G1.
  intros. destruct H0 as [q ?].
  destruct H as [[??][??]]; destruct H1; split; eauto.
  exists q.
  apply member_eq with (fst x, q); auto.
  destruct H as [[??][??]].
  destruct H1; split; split; simpl; auto.
  intros [x x'].  
  destruct (N_eq_dec x x').
  subst x'.
  destruct (finset_find_dec N
    (fun q => True)) with (finrel_image R x); auto.
  destruct s as [z [??]].
  left; simpl; intros.
  exists z. apply finrel_image_elem in H. auto.
  right; repeat intro.
  destruct H; auto.
  simpl in H.
  apply (n x0); auto. apply finrel_image_elem; auto.
  left; intros.
  simpl in H. elim n. destruct H; auto.
  destruct s as [z [??]].
  right. repeat intro. apply H0.
  intros. apply (H1 (fst z)).
  apply member_eq with z; auto.
  destruct H2. split; split; auto.
  left. intros.
  apply (e (x,x)); auto.
Qed.

Lemma fin_ep_pair_dec hf G1 G2 E P :
  { fin_ep_pair hf G1 G2 E P } + { ~fin_ep_pair hf G1 G2 E P }.
Proof.
  destruct (finapprox_rel_dec hf G1 G2 E).
  destruct (finapprox_rel_dec hf G2 G1 P).
  destruct (finord_ord_dec1 (finrel_inv G1) (finrel_compose G2 P E)).
  destruct (finord_ord_dec1 (finrel_compose G2 P E) (finrel_inv G1)).
  destruct (finord_ord_dec1 (finrel_inv G2) (finrel_compose G1 E P)).
  left.
  constructor; auto.
  intros. split; intros.
  apply finrel_inv_elem.
  apply m; auto.
  apply m0.
  apply finrel_inv_elem. auto.
  intros.
  apply finrel_inv_elem. apply m1. auto.
  right; intros [????].
  destruct e as [a [b [??]]].
  apply H0. 
  apply finrel_inv_elem. auto.
  right; intros [????].
  destruct e as [a [b [??]]].
  apply H0. 
  apply finep_id3; auto.
  apply finrel_inv_elem. auto.
  right; intros [????].
  destruct e as [a [b [??]]].
  apply H0. apply finrel_inv_elem.
  apply finep_id3; auto.
  right; intros [????]. auto.
  right; intros [????]. auto.
Qed.  

Lemma finapprox_rel_ok hf X Y a b :
  a ≈ b -> finapprox_rel hf X Y a -> finapprox_rel hf X Y b.
Proof.
  unfold finapprox_rel; intros.
  destruct H0 as [?[?[??]]].
  split; intros.
  apply H0; auto. rewrite H; auto.
  split; intros.
  rewrite <- H. eapply H1; eauto.
  rewrite H; auto.
  split; intros.
  destruct (H2 x y1 y2) as [y3 [?[??]]].
  rewrite H; auto.
  rewrite H; auto.
  exists y3. intuition.
  rewrite <- H; auto.
  destruct hf; auto.
  intros. destruct (H3 x); auto.
  exists x0. rewrite <- H; auto.
Qed.

Lemma fin_ep_pair_ok : forall hf X Y E E' P P',
  P ≈ P' -> E ≈ E' ->
  fin_ep_pair hf X Y E P ->
  fin_ep_pair hf X Y E' P'.
Proof.
  intros.
  destruct H1; constructor.
  apply finapprox_rel_ok with E; auto.
  apply finapprox_rel_ok with P; auto.
  intros.
  split; intros.
  rewrite <- finep_id3.
  rewrite finrel_compose_elem in H1; eauto.
  rewrite finrel_compose_elem; eauto.
  destruct H1 as [q [??]]. exists q; split; auto.
  rewrite H0; auto.
  rewrite H; auto.
  apply finapprox_rel_ok with E; eauto.
  apply finapprox_rel_ok with P; eauto.
  rewrite <- finep_id3 in H1.
  rewrite finrel_compose_elem in H1; eauto.
  rewrite finrel_compose_elem; eauto.
  destruct H1 as [q [??]]. exists q; split; auto.
  rewrite <- H0; auto.
  rewrite <- H; auto.
  apply finapprox_rel_ok with E; eauto.
  apply finapprox_rel_ok with P; eauto.
  intros.
  apply finep_id4.
  rewrite finrel_compose_elem in H1; eauto.
  rewrite finrel_compose_elem; eauto.
  destruct H1 as [q [??]]. exists q; split; auto.
  rewrite H; auto.
  rewrite H0; auto.
  apply finapprox_rel_ok with P; eauto.
  apply finapprox_rel_ok with E; eauto.
Qed.  

Lemma finord_ord_dec hf (X Y:finord hf) :
  { finord_ord hf X Y } + { ~finord_ord hf X Y }.
Proof.
  unfold finord_ord.
  destruct (finset_find_dec (finset N2)
    (fun E => exists P, fin_ep_pair hf (proj1_sig X) (proj1_sig Y) E P))
    with (list_finsubsets (finprod (image π₁ (proj1_sig X)) (image π₂ (proj1_sig Y)))).
  intros. destruct H0 as [P ?]. exists P. 
  apply fin_ep_pair_ok with x P; auto.
  intro E.
  destruct (finset_find_dec (finset N2)
    (fun P => fin_ep_pair hf (proj1_sig X) (proj1_sig Y) E P))
    with (list_finsubsets (finprod (image π₂ (proj1_sig Y)) (image π₁ (proj1_sig X)))).
  intros.
  apply fin_ep_pair_ok with E x; auto.
  intro P.
  apply fin_ep_pair_dec.
  destruct s as [P [??]].  
  left. exists P. auto.
  right; intro.
  destruct H as [P ?].
  apply (n P); auto.
  apply list_finsubsets_complete; auto.
  apply N2dec.
  red; intros.
  destruct H.
  destruct finep_approx4 as [?[?[??]]].
  destruct a.
  apply H in H0.
  apply finprod_elem.
  destruct H0.
  split; apply image_axiom1'.
  exists (c,c). split; auto.
  exists (c0,c0). split; auto.

  destruct s as [E [??]].
  left. exists E. auto.
  right; intro.
  destruct H as [E [P ?]].
  apply (n E); eauto.
  apply list_finsubsets_complete; auto.
  apply N2dec.
  red; intros.
  destruct H.
  destruct finep_approx3 as [?[?[??]]].
  destruct a.
  apply H in H0.
  apply finprod_elem.
  destruct H0.
  split; apply image_axiom1'.
  exists (c,c). split; auto.
  exists (c0,c0). split; auto.
Qed.


Lemma fin_ep_pair_compose hf (G1 G2 G3 E E' P P':finset N2) :
  preord_graph hf G1 ->
  preord_graph hf G2 ->
  preord_graph hf G3 ->
  fin_ep_pair hf G1 G2 E P ->
  fin_ep_pair hf G2 G3 E' P' ->
  fin_ep_pair hf G1 G3 (finrel_compose G2 E' E) (finrel_compose G2 P P').
Proof.
  intros HG1 HG2 HG3 HEP1 HEP2.
  split.
  apply finapprox_compose; auto.
  destruct HEP1; auto.
  destruct HEP2; auto.
  apply finapprox_compose; auto.
  destruct HEP2; auto.
  destruct HEP1; auto.
  
  intros. split; intros.
  destruct HEP1; destruct HEP2.
  rewrite finrel_compose_elem in H; eauto.
  2: eapply finapprox_compose; eauto.
  2: eapply finapprox_compose; eauto.
  destruct H as [q [??]].
  rewrite finrel_compose_elem in H; eauto.
  destruct H as [m [??]].
  rewrite finrel_compose_elem in H0; eauto.
  destruct H0 as [n [??]].
  assert ((n,m) ∈ G2).
  apply finep_id5.
  rewrite finrel_compose_elem; eauto.
  apply finep_id3.
  rewrite finrel_compose_elem; eauto.
  exists m. split; auto.
  destruct finep_approx4 as [?[?[??]]].
  apply H5 with n y; auto.
  apply H4 in H2. destruct H2; auto.
  
  destruct HEP1; destruct HEP2.
  rewrite finrel_compose_elem; eauto.
  2: eapply finapprox_compose; eauto.
  2: eapply finapprox_compose; eauto.
  apply finep_id3 in H.
  rewrite finrel_compose_elem in H; eauto.
  destruct H as [q [??]].
  assert ((q,q) ∈ G2).
  destruct finep_approx3 as [?[?[??]]].
  apply H1 in H. destruct H. auto.
  apply finep_id5 in H1.
  rewrite finrel_compose_elem in H1; eauto.
  destruct H1 as [p [??]].
  exists p. split.
  rewrite finrel_compose_elem; eauto.
  rewrite finrel_compose_elem; eauto.

  intros.
  destruct HEP1; destruct HEP2.
  rewrite finrel_compose_elem in H; eauto.
  2: eapply finapprox_compose; eauto.
  2: eapply finapprox_compose; eauto.
  destruct H as [q [??]].
  apply finep_id6.
  rewrite finrel_compose_elem in H; eauto.
  rewrite finrel_compose_elem in H0; eauto.
  destruct H as [m [??]].
  destruct H0 as [n  [??]].
  rewrite finrel_compose_elem; eauto.
  exists n. split; auto.
  destruct finep_approx6 as [?[?[??]]].
  apply H4 with x m.
  apply H3 in H. destruct H; auto.
  apply finep_id4.
  rewrite finrel_compose_elem; eauto.
  auto.
Qed.

Lemma fin_ep_pair_refl hf (G:finset N2) :
  preord_graph hf G ->
  fin_ep_pair hf G G (finrel_inv G) (finrel_inv G).
Proof.
  intros [?[?[??]]].

  assert (finapprox_rel hf G G (finrel_inv G)).

  repeat split; intros; eauto.
  apply -> finrel_inv_elem in H3.
  eapply H0; eauto.
  apply -> finrel_inv_elem in H3.
  eapply H; eauto.
  apply -> finrel_inv_elem in H5.
  apply <- finrel_inv_elem.
  apply H1 with y; auto.  
  apply H1 with x; auto.  
  apply -> finrel_inv_elem in H3.
  apply -> finrel_inv_elem in H4.
  exists x. split; auto. split; auto.
  apply <- finrel_inv_elem.
  eapply H0; eauto.
  destruct hf; auto.
  intros.
  exists x.
  apply <- finrel_inv_elem. auto.

  assert (forall x y : N,
   (x, y) ∈ finrel_compose G (finrel_inv G) (finrel_inv G) <-> (y, x) ∈ G).
  
  intros; split; intros.  
  rewrite finrel_compose_elem in H4; eauto.
  destruct H4 as [q [??]].
  apply -> finrel_inv_elem in H4.
  apply -> finrel_inv_elem in H5.
  apply H1 with q; auto.
  rewrite finrel_compose_elem; eauto.
  exists y. split.
  apply <- finrel_inv_elem. auto.
  apply <- finrel_inv_elem. 
  eapply H; eauto.

  apply FinEP; auto.
  intros. apply H4; auto.
Qed.

Program Definition finord_preord_mixin hf : Preord.mixin_of (finord hf) :=
  Preord.Mixin (finord hf) (finord_ord hf) _ _.
Next Obligation.
  intros.
  exists (finrel_inv (proj1_sig x)).
  exists (finrel_inv (proj1_sig x)).
  apply fin_ep_pair_refl.
  apply proj2_sig.
Qed.
Next Obligation.
  intros.
  destruct H as [E [P ?]].
  destruct H0 as [E' [P' ?]].
  exists (finrel_compose (proj1_sig y) E' E).
  exists (finrel_compose (proj1_sig y) P P').
  apply fin_ep_pair_compose; auto.
  apply proj2_sig.
  apply proj2_sig.
  apply proj2_sig.
Qed.

Canonical Structure finord_preord hf := Preord.Pack (finord hf) (finord_preord_mixin hf).

Definition finord_enum hf : eset (finord_preord hf) :=
  fun n =>
  let X := finsubsets _ (eff_enum _ (effective_prod effective_Nord effective_Nord)) in
  match X n with
  | None => None
  | Some G => match preord_graph_dec hf G with
              | left H => Some (exist _ G H)
              | right _ => None
              end
  end.

Lemma finapprox_rel_ok' hf X Y X' Y' a :
  X ≈ X' -> Y ≈ Y' -> finapprox_rel hf X Y a -> finapprox_rel hf X' Y' a.
Proof.
  intros.
  destruct H1 as [?[?[??]]].
  repeat split; intros.
  apply H1 in H5. destruct H5.
  rewrite <- H. auto.
  apply H1 in H5. destruct H5.
  rewrite <- H0. auto.
  apply H2 with x y; auto.
  rewrite H; auto. rewrite H0; auto.
  destruct (H3 x y1 y2) as [y3 [?[??]]]; auto.
  exists y3.
  split. rewrite <- H0; auto.
  split. rewrite <- H0; auto.
  auto.
  destruct hf; auto.
  intros. destruct (H4 x).
  rewrite H; auto.
  exists x0. auto.
Qed.

Lemma fin_ep_pair_ok' : forall hf X X' Y Y' E P,
  X ≈ X' -> Y ≈ Y' ->
  fin_ep_pair hf X Y E P ->
  fin_ep_pair hf X' Y' E P.
Proof.
  repeat intro.
  destruct H1; split.
  eapply finapprox_rel_ok'; eauto.
  eapply finapprox_rel_ok'; eauto.
  intros. 
  rewrite <- H.
  rewrite <- finep_id3.
  split; intros.
  rewrite finrel_compose_elem in H1; eauto.
  rewrite finrel_compose_elem; eauto.
  eapply finapprox_rel_ok'. 3: apply finep_approx3.
  eauto. eauto.
  eapply finapprox_rel_ok'. 3: apply finep_approx4.
  auto. eauto.
  rewrite finrel_compose_elem in H1; eauto.
  rewrite finrel_compose_elem; eauto.
  eapply finapprox_rel_ok'. 3: apply finep_approx3.
  eauto. eauto.
  eapply finapprox_rel_ok'. 3: apply finep_approx4.
  auto. eauto.
  intros.  
  rewrite finrel_compose_elem in H1; eauto.
  destruct H1 as [q [??]].
  rewrite <-  H0. apply finep_id4.
  rewrite finrel_compose_elem; eauto.
  eapply finapprox_rel_ok'. 3: apply finep_approx4.
  eauto. eauto.
  eapply finapprox_rel_ok'. 3: apply finep_approx3.
  auto. eauto.
Qed.

Program Definition finord_preord_eff hf : effective_order (finord_preord hf) :=
  EffectiveOrder (finord_preord hf) (finord_ord_dec hf) (finord_enum hf) _.
Next Obligation.
  intros.
  unfold finord_enum.
  destruct x as [x Hx].
  assert (x ∈ finsubsets (N × N)
                (eff_enum _ (effective_prod effective_Nord effective_Nord))).
  apply finsubsets_complete.
  red; intros. apply eff_complete.
  destruct H as [n ?].
  exists n.
  destruct (finsubsets _ (eff_enum _ (effective_prod effective_Nord effective_Nord)) n); auto.
  destruct (preord_graph_dec hf c); auto.
  split; hnf; simpl.
  exists (finrel_inv x).
  exists (finrel_inv x).
  eapply fin_ep_pair_ok'. 3: apply fin_ep_pair_refl; auto.
  auto. auto.
  exists (finrel_inv x).
  exists (finrel_inv x).
  eapply fin_ep_pair_ok'. 3: apply fin_ep_pair_refl; auto.
  auto. auto.
  apply n0.
  apply preord_graph_ok with x; auto.
Qed.

Definition finord_elem hf (X:finord hf) := { n:N | (n,n) ∈ proj1_sig X }.
Definition finord_elem_ord hf (X:finord hf) (a b:finord_elem hf X) :=
  (proj1_sig a, proj1_sig b) ∈ proj1_sig X.

Program Definition finord_to_preord_mixin hf (X:finord hf) 
  : Preord.mixin_of (finord_elem hf X) :=
  Preord.Mixin (finord_elem hf X) (finord_elem_ord hf X) _ _.
Next Obligation.
  intros. red. destruct x. simpl. auto.
Qed.
Next Obligation.
  unfold finord_elem_ord; intros. 
  destruct x as [x Hx].
  destruct y as [y Hy].
  destruct z as [z Hz].
  simpl in *.
  destruct X as [X HX]. simpl in *.
  destruct HX as [?[?[??]]].
  apply H3 with y; auto.
Qed.

Canonical Structure finord_to_preord hf (X:finord hf) : preord 
  := Preord.Pack (finord_elem hf X) (finord_to_preord_mixin hf X).

Coercion finord_to_preord : finord >-> preord.


Definition enum_finord hf (X:finord hf) : eset (finord_to_preord hf X) :=
  fun n =>
    match finset_dec _ N2dec (n,n) (proj1_sig X) with
    | left H => Some (exist _ n H)
    | right _ => None
    end.

Program Definition finord_effective hf (X:finord hf) : effective_order (finord_to_preord hf X) :=
  EffectiveOrder _ 
     (fun x y => finset_dec _ N2dec (x,y) (proj1_sig X))
     (enum_finord hf X)
     _.
Next Obligation.
  intros.
  hnf.
  unfold enum_finord.
  exists (proj1_sig x).
  simpl.
  match goal with [ |- appcontext[ finset_dec_obligation_1 N2 N2dec ?X ?Y ] ] =>
    destruct (finset_dec_obligation_1 N2 N2dec X Y)
  end.
  split; hnf; simpl; eauto.
  apply n. apply proj2_sig.
Qed.  


Section finite_limit.
  Variable hf:bool.

  Lemma fin_ep_pair_embed_eq_proj_eq : forall X Y e e' p p',
    fin_ep_pair hf X Y e p -> 
    fin_ep_pair hf X Y e' p' ->
    e ≈ e' -> p ≈ p'.
  Proof.
    intros X Y e e' p p'.
    intros.
    split.
    destruct H.
    destruct H0.
    hnf. intros [y x] ?.
    assert ((x,x) ∈ X /\ (y,y) ∈ Y).
    destruct finep_approx4.
    apply H0 in H. destruct H; split; auto.
    destruct H0.
    generalize H0; intros.
    rewrite <- finep_id5 in H3.
    rewrite finrel_compose_elem in H3; eauto.
    destruct H3 as [q [??]].
    destruct finep_approx6 as [?[?[??]]].
    apply H6 with q x; auto.
    apply finep_id4.
    rewrite finrel_compose_elem; eauto.
    exists x. split; auto.
    rewrite H1; auto.

    destruct H.
    destruct H0.
    hnf. intros [y x] ?.
    assert ((x,x) ∈ X /\ (y,y) ∈ Y).
    destruct finep_approx6.
    apply H0 in H. destruct H; split; auto.
    destruct H0.
    generalize H0; intros.
    rewrite <- finep_id3 in H3.
    rewrite finrel_compose_elem in H3; eauto.
    destruct H3 as [q [??]].
    destruct finep_approx4 as [?[?[??]]].
    apply H6 with q x; auto.
    apply finep_id6.
    rewrite finrel_compose_elem; eauto.
    exists x. split; auto.
    rewrite <- H1; auto.
  Qed.    


  Record finite_directed_system (I:preord) :=
  FinDirSys
  { fds_eff : effective_order I
  ; fds_dir : directed hf (eff_enum I fds_eff)
  ; fds_F   : I -> finord hf
  ; fds_embed   : forall i j:I, i≤j -> finset N2
  ; fds_project : forall i j:I, i≤j -> finset N2
  ; fds_ep_pair : forall (i j:I) (H:i≤j),
       fin_ep_pair hf (proj1_sig (fds_F i)) (proj1_sig  (fds_F j))
                    (fds_embed i j H) (fds_project i j H)
  ; fds_ident : forall i (Hii:i≤i), fds_embed i i Hii ≈ (finrel_inv (proj1_sig (fds_F i)))
  ; fds_compose : forall i j k (Hij:i≤j) (Hjk:j≤k) (Hik:i≤k),
          finrel_compose (proj1_sig (fds_F j)) (fds_embed j k Hjk) (fds_embed i j Hij)
          ≈ 
          fds_embed i k Hik
  }.

  Lemma fds_ident' I (FDS:finite_directed_system I) :
    forall i (Hii:i≤i),
      fds_project I FDS i i Hii ≈ finrel_inv (proj1_sig (fds_F I FDS i)).
  Proof.
    intros.
    generalize (fds_ident I FDS i Hii).
    intro.
    apply (fin_ep_pair_embed_eq_proj_eq 
      (proj1_sig (fds_F I FDS i)) (proj1_sig (fds_F I FDS i))
      (fds_embed I FDS i i Hii)
      (finrel_inv (proj1_sig (fds_F I FDS i)))); auto.
    apply fds_ep_pair.
    apply fin_ep_pair_refl.
    apply proj2_sig.
  Qed.

  Lemma fds_compose' I (FDS:finite_directed_system I) :
    forall i j k (Hij:i≤j) (Hjk:j≤k) (Hik:i≤k),
      finrel_compose (proj1_sig (fds_F I FDS j))
           (fds_project I FDS i j Hij) (fds_project I FDS j k Hjk) 
      ≈
      (fds_project I FDS i k Hik).
  Proof.
    intros.
    generalize (fds_compose I FDS i j k Hij Hjk Hik). intros.
    apply (fin_ep_pair_embed_eq_proj_eq 
      (proj1_sig (fds_F I FDS i)) (proj1_sig (fds_F I FDS k))
      (finrel_compose (proj1_sig (fds_F I FDS j))
        (fds_embed I FDS j k Hjk)
        (fds_embed I FDS i j Hij))
      (fds_embed I FDS i k Hik)); auto.
    apply fin_ep_pair_compose; auto.
    apply proj2_sig.
    apply proj2_sig.
    apply proj2_sig.
    apply fds_ep_pair.
    apply fds_ep_pair.
    apply fds_ep_pair.
  Qed.      

  Section bilimit.
    Variable I:preord.
    Variable FDS : finite_directed_system I.
    
    Lemma choose_ub_set (M:finset I) (HM:inh hf M) : { k:I | upper_bound k M }.
    Proof.
      set (M' := esubset_dec I (fun x => upper_bound x M)
                (upper_bound_dec I (fds_eff I FDS) M)
                (eff_enum I (fds_eff I FDS))).
      assert (einhabited M').
      apply member_inhabited.
      destruct (fds_dir I FDS M) as [k [??]]; auto.
      hnf; intros. apply eff_complete.
      exists k.
      unfold M'.
      apply esubset_dec_elem.
      apply upper_bound_ok.
      split; auto.
      destruct (find_inhabitant I M' H) as [k ?].
      exists k.
      destruct s as [n [??]].
      assert (k ∈ M').
      exists n. rewrite H0. auto.
      unfold M' in H2.
      apply esubset_dec_elem in H2.
      destruct H2; auto.
      apply upper_bound_ok.
    Qed.

    Lemma choose_ub (i j:I) : { k:I | i ≤ k /\ j ≤ k }.
    Proof.
      destruct (choose_ub_set (i::j::nil)%list).
      destruct hf; simpl; auto.
      exists i. apply cons_elem. auto.
      exists x.
      split; apply u.
      apply cons_elem; auto.
      apply cons_elem; right.
      apply cons_elem; auto.
    Qed.

    Record lim_set :=
      LimSet
      { lim_idx : I
      ; lim_elem : N
      ; lim_ok : (lim_elem,lim_elem) ∈ proj1_sig (fds_F I FDS lim_idx)
      }.

    Definition lim_ord_rel (x y:lim_set) := 
       exists k (Hxk:lim_idx x ≤ k) (Hyk:lim_idx y ≤ k),
         forall z, (lim_elem x, z) ∈ fds_embed I FDS _ _ Hxk ->
                   (lim_elem y, z) ∈ fds_embed I FDS _ _ Hyk.

    Lemma lim_ord_rel_forall_exists : forall x y,
      lim_ord_rel x y <->
      forall k (Hxk:lim_idx x ≤ k) (Hyk:lim_idx y ≤ k),
         forall z, (lim_elem x, z) ∈ fds_embed I FDS _ _ Hxk ->
                   (lim_elem y, z) ∈ fds_embed I FDS _ _ Hyk.
    Proof.
      intros. split; intro.
      destruct H as [k [Hxk [Hyk ?]]].
      intros k' Hxk' Hyk' z Hz.
      destruct (choose_ub k k') as [q [Hkq Hkq']].
      assert (Hxq : lim_idx x ≤ q). etransitivity; eauto.
      assert (Hyq : lim_idx y ≤ q). etransitivity; eauto.
      assert ((lim_elem x, lim_elem x) ∈ proj1_sig (fds_F I FDS (lim_idx x))
               /\  (z,z) ∈ proj1_sig (fds_F I FDS k')).
      generalize (fds_ep_pair I FDS _ _ Hxk').
      intros. destruct H0.
      destruct finep_approx3 as [?[?[??]]].
      apply H0 in Hz. auto.
      destruct H0.
      generalize (fds_ep_pair I FDS _ _ Hkq').
      intros [????].
      rewrite <- finep_id3 in H1. clear finep_id3.
      rewrite finrel_compose_elem in H1; eauto.
      destruct H1 as [w [??]].
      clear finep_approx3 finep_approx4 finep_id4.
      assert ((lim_elem x, w) ∈ fds_embed I FDS (lim_idx x) q Hxq).
      generalize (fds_compose I FDS _ _ _ Hxk' Hkq' Hxq).
      intros [??]. apply H3. clear H3 H4.
      rewrite finrel_compose_elem; eauto.
      generalize (fds_ep_pair I FDS _ _ Hxk').
      intros [????]. eauto.
      generalize (fds_ep_pair I FDS _ _ Hkq').
      intros [????]. eauto.
      generalize (fds_compose I FDS _ _ _ Hxk Hkq Hxq).
      intros [??]. apply H5 in H3. clear H4 H5.
      rewrite finrel_compose_elem in H3.
      destruct H3 as [t [??]].
      apply H in H3.      
      assert ((lim_elem y, w) ∈ fds_embed I FDS (lim_idx y) q Hyq).
      generalize (fds_compose I FDS _ _ _ Hyk Hkq Hyq).
      intros [??]. apply H5. clear H5 H6.
      rewrite finrel_compose_elem; eauto.
      generalize (fds_ep_pair I FDS _ _ Hyk).
      intros [????]. eauto.
      generalize (fds_ep_pair I FDS _ _ Hkq).
      intros [????]. eauto.
      generalize (fds_compose I FDS _ _ _ Hyk' Hkq' Hyq).
      intros [??]. apply H7 in H5. clear H6 H7.
      rewrite finrel_compose_elem in H5; eauto.
      destruct H5 as [t' [??]].
      assert ((z, t') ∈ proj1_sig (fds_F I FDS k')).
        generalize (fds_ep_pair I FDS _ _ Hkq').
        intros [????].
        apply finep_id3.
        rewrite finrel_compose_elem; eauto.

      generalize (fds_ep_pair I FDS _ _ Hyk').
      intros [????].
      destruct finep_approx3 as [?[?[??]]].
      apply H9 with (lim_elem y) t'; auto.
      apply H8 in H5. destruct H5; auto.
      
      generalize (fds_ep_pair I FDS _ _ Hyk').
      intros [????]. eauto.
      generalize (fds_ep_pair I FDS _ _ Hkq').
      intros [????]. eauto.
      generalize (fds_ep_pair I FDS _ _ Hxk).
      intros [????]. eauto.
      generalize (fds_ep_pair I FDS _ _ Hkq).
      intros [????]. eauto.
            
      red; intros.      
      destruct (choose_ub (lim_idx x) (lim_idx y)) as [q [??]].
      exists q. exists H0. exists H1.
      apply H.
    Qed.

    Lemma lim_ord_rel_refl : forall x, lim_ord_rel x x.
    Proof.
      intros. exists (lim_idx x). exists (ord_refl _ _). exists (ord_refl _ _).
      auto.
    Qed.

    Lemma lim_ord_rel_trans : forall x y z, lim_ord_rel x y -> lim_ord_rel y z -> lim_ord_rel x z.
    Proof.
      intros.
      destruct (fds_dir I FDS (lim_idx x::lim_idx y::lim_idx z::nil)%list) as [k [??]].
      destruct hf; simpl; auto.
      exists (lim_idx x). apply cons_elem; auto.
      hnf; intros. apply eff_complete.
      clear H2.
      rewrite lim_ord_rel_forall_exists in H.
      rewrite lim_ord_rel_forall_exists in H0.
      assert (Hxk : lim_idx x ≤ k). apply H1. apply cons_elem; auto.
      assert (Hyk : lim_idx y ≤ k). apply H1. apply cons_elem. right. apply cons_elem; auto.
      assert (Hzk : lim_idx z ≤ k). apply H1. apply cons_elem. right.
      apply cons_elem; right. apply cons_elem; auto.
      exists k. exists Hxk. exists Hzk.
      intros.
      apply H0 with Hyk. apply H with Hxk. auto.
    Qed.

    Definition lim_ord_mixin : Preord.mixin_of lim_set :=
      Preord.Mixin lim_set lim_ord_rel lim_ord_rel_refl lim_ord_rel_trans.
    
    Canonical Structure lim_ord : preord := Preord.Pack lim_set lim_ord_mixin.

    Definition lim_set_enum : eset lim_ord :=
      fun n => let (n1,n2) := pairing.unpairing n in
        match eff_enum I (fds_eff I FDS) n1 with
               | Some i =>
                          match finset_in_dec N2 N2dec (proj1_sig (fds_F I FDS i)) (n2,n2) with
                          | left H => Some (LimSet i n2 H)
                          | right _ => None
                          end
               | None => None
               end.

    Lemma lim_ord_rel_aux_dec x y k (Hxk:lim_idx x ≤ k) (Hyk:lim_idx y ≤ k) :
         { forall z, (lim_elem x, z) ∈ fds_embed I FDS _ _ Hxk ->
                   (lim_elem y, z) ∈ fds_embed I FDS _ _ Hyk }
         +
         { ~forall z, (lim_elem x, z) ∈ fds_embed I FDS _ _ Hxk ->
                   (lim_elem y, z) ∈ fds_embed I FDS _ _ Hyk }.
    Proof.
      destruct (finset_find_dec' N (fun z => (lim_elem y, z) ∈ fds_embed I FDS (lim_idx y) k Hyk))
        with (finrel_image (fds_embed I FDS (lim_idx x) k Hxk) (lim_elem x)).
      intros.
      apply member_eq with (lim_elem y, x0); auto.
      destruct H; split; split; auto.
      intro z.
      apply eff_in_dec. apply effective_prod; apply effective_Nord.
      destruct s as [z [??]].
      right; intro.
      apply H0. apply H1; auto.
      apply finrel_image_elem in H; auto.
      left; intros. apply m.
      apply finrel_image_elem. auto.
    Qed.

    Lemma lim_ord_rel_dec x y : { lim_ord_rel x y }+{ ~lim_ord_rel x y }.
    Proof.
      destruct (choose_ub (lim_idx x) (lim_idx y)) as [k [Hxk Hyk]].
      destruct (lim_ord_rel_aux_dec x y k Hxk Hyk).
      left. exists k. exists Hxk. exists Hyk. auto.
      right.
      intro. apply n.
      apply lim_ord_rel_forall_exists; auto.
    Qed.

    Program Definition lim_ord_effective : effective_order lim_ord :=
      EffectiveOrder lim_ord lim_ord_rel_dec lim_set_enum _.
    Next Obligation.
      intros. unfold lim_set_enum.
      assert (lim_idx x ∈ eff_enum I (fds_eff I FDS)).
      apply eff_complete.
      destruct H as [n1 ?].
      revert H.
      case_eq (eff_enum I (fds_eff I FDS) n1); intros.
      destruct H0.
      destruct x as [i x Hx]. simpl in H0, H1.
      generalize (fds_ep_pair I FDS _ _ H0).
      intros [????].
      generalize Hx.
      rewrite <- finep_id3 in Hx.
      rewrite finrel_compose_elem in Hx; eauto.
      destruct Hx as [y [??]].
      assert ((y,y) ∈ proj1_sig (fds_F I FDS c)).
      destruct finep_approx3 as [?[?[??]]].
      apply H4 in H2.
      destruct H2; auto.
      destruct (fds_ep_pair I FDS _ _ H1).
      
      generalize H4.
      rewrite <- finep_id5 in H4.
      rewrite finrel_compose_elem in H4.
      destruct H4 as [w [??]].
      
      assert ((x,w) ∈ finrel_inv (proj1_sig (fds_F I FDS i))).
      destruct (fds_ident I FDS i (ord_refl I i)).
      apply H6. clear H6 H7.
      destruct (fds_compose I FDS i c i H0 H1 (ord_refl I i)).
      apply H6. clear H6 H7.
      rewrite finrel_compose_elem; eauto.
      rewrite finrel_inv_elem in H6.
      
      intro.
      exists (pairing.pairing (n1,y)).
      rewrite pairing.unpairing_pairing.
      rewrite H.
      match goal with [ |- match match ?X with | left _ => _ | right _ => _ end
                    with Some a' => _ | None => _ end ] => set (Q := X) end.
      destruct Q; auto.
      split; red; simpl.
      red. simpl.
      exists i. exists (ord_refl _ _). exists H1.
      intros.
      destruct (fds_ident I FDS i (ord_refl I i)).
      apply H9 in H8. clear H9 H10.
      destruct finep_approx5 as [?[?[??]]].
      apply H10 with y w; auto.
      rewrite finrel_inv_elem in H8.
      destruct (fds_ident' I FDS i (ord_refl I i)).
      apply finrel_inv_elem. apply H13. clear H13 H14.
      destruct (fds_compose' I FDS i c i H0 H1 (ord_refl I i)).
      apply H13. clear H13 H14.
      rewrite finrel_compose_elem; eauto.
      exists y. split; auto.
      destruct finep_approx4 as [?[?[??]]].
      apply H14 with y x; auto.

      red; simpl; intros.
      exists i. exists H1. exists (ord_refl I i).
      intros.
      destruct (fds_compose I FDS i c i H0 H1 (ord_refl I i)).
      apply H9. clear H9 H10.
      rewrite finrel_compose_elem; eauto.
      eauto. eauto.
      elim H0.
    Qed.

    Lemma lim_embed_eq : forall i k (Hik:i≤k) x y Xok Yok,
      (x,y) ∈ fds_embed I FDS i k (Hik) ->
      (y,x) ∈ fds_project I FDS i k (Hik) ->
      (LimSet i x Xok : lim_ord) ≈ LimSet k y Yok.
    Proof.
      intros; split. hnf. simpl.
      exists k. exists Hik. exists (ord_refl _ _).
      intros.
      rewrite fds_ident.
      apply finrel_inv_elem.
      generalize (fds_ep_pair I FDS i k Hik).
      intros [????].
      apply finep_id4.
      rewrite finrel_compose_elem; eauto.
      
      hnf. simpl. exists k. exists (ord_refl _ _). exists Hik.
      intros.
      rewrite fds_ident in H1.
      rewrite finrel_inv_elem in H1.
      generalize (fds_ep_pair I FDS i k Hik).
      intros [????].
      destruct finep_approx3 as [?[?[??]]].
      apply H3 with x y; auto.
    Qed.

    Lemma lim_embed_upwards : forall (x:lim_ord) k (Hxk: lim_idx x ≤ k),
      exists y, lim_idx y = k /\ x ≈ y.
    Proof.
      intros.
      generalize (fds_ep_pair I FDS _ _ Hxk).
      intros [????].
      generalize (lim_ok x). intro.
      apply finep_id3 in H.      
      rewrite finrel_compose_elem in H; eauto.
      destruct H as [y [??]].
      assert ((y,y) ∈ proj1_sig (fds_F I FDS k)).
      destruct finep_approx3 as [? _].
      apply H1 in H. destruct H; auto.
      exists (LimSet k y H1).
      split. simpl. auto.
      destruct x as [i x Hx]; simpl in *.
      apply lim_embed_eq with Hxk; auto.
    Qed.

    Lemma build_lim_set_aux k :
      forall 
        (X:list N)
        (Z:finset lim_ord) 
        (HXZ : forall n,
                (n,n) ∈ proj1_sig (fds_F I FDS k) ->
                In n X \/ exists z, In z Z /\ lim_elem z = n)
        (HX : forall n, In n X -> (n,n) ∈ (proj1_sig (fds_F I FDS k)))
        (HZ : forall z, In z Z -> lim_idx z = k),
        { Z : finset lim_ord | 
                (forall z, In z Z -> lim_idx z = k) /\
                forall n,
                   (n,n) ∈ proj1_sig (fds_F I FDS k) ->
                     exists z, In z Z /\ lim_elem z = n }. 
    Proof.
      induction X; simpl; intros.
      exists Z.
      intros; split; intros.
      apply HZ; auto.
      apply HXZ in H.
      destruct H; auto. elim H.
      
      assert (Ha : (a,a) ∈ (proj1_sig (fds_F I FDS k))).
      apply HX. auto.
      set (z := LimSet k a Ha).
      apply (IHX (z::Z)).
      intros. apply HXZ in H.
      intuition. subst n.
      right.
      exists z. split; simpl; auto.
      destruct H0 as [z' [??]].
      right. exists z'; split; simpl; auto.
      intros.
      apply HX; auto.
      intros. destruct H.
      subst z0. simpl; auto.
      apply HZ; auto.
    Qed.

    Lemma build_lim_set k :
        { Z : finset lim_ord | 
                (forall z, In z Z -> lim_idx z = k) /\
                forall n,
                   (n,n) ∈ proj1_sig (fds_F I FDS k) ->
                     exists z, In z Z /\ lim_elem z = n }. 
    Proof.
      apply build_lim_set_aux with
        (map (@fst _ _) (proj1_sig (fds_F I FDS k))) nil.
      intros. left.
      apply in_map_iff.
      exists (n,n). split; auto.
      apply N2in. auto.
      intros.
      apply in_map_iff in H.
      destruct H as [x [??]].
      destruct x as [x y].
      simpl in H. subst x.
      destruct (fds_F I FDS k). simpl in *.
      destruct p as [?[??]].
      apply H with y; auto.
      apply N2in; auto.
      simpl; intuition.
    Qed.

    Lemma find_largest_projection_aux (X Y:finord hf) (R:finset N2) x 
      (HR:finapprox_rel hf (proj1_sig Y) (proj1_sig X) R) :
      forall (Q:finset N) z,
        ((z,z) ∈ proj1_sig X) ->
        ((x,z) ∈ R) ->
        (forall y, In y Q -> (y,y) ∈ proj1_sig X) ->
        (forall y, (x,y) ∈ R -> In y Q \/ (y,z) ∈ proj1_sig X) ->
      exists y : N,
        (y, y) ∈ proj1_sig X /\
        (x, y) ∈ R /\ (forall q : N, (x, q) ∈ R -> (q, y) ∈ proj1_sig X).
    Proof.
      induction Q. simpl; intros.
      exists z. intuition.
      destruct (H2 q); auto. elim H4.
      intros.
      destruct (finset_dec N2 N2dec (x,a) R).
      assert (exists q,
        (x,q) ∈ R /\ (z,q) ∈ proj1_sig X /\ (a,q) ∈ proj1_sig X).
      destruct HR as [?[?[??]]].
      destruct (H5 x a z) as [q [?[??]]]; eauto.
      destruct H3 as [q [?[??]]].
      apply (IHQ q); auto.
      destruct (proj2_sig X) as [?[??]].
      apply H7 in H4. auto.
      intros.
      apply H1; simpl; auto.
      intros.
      destruct (H2 y); auto.
      simpl in H7. destruct H7.
      subst y.
      right. auto. auto.
      right.
      destruct (proj2_sig X) as [?[?[??]]].
      apply H10 with z; auto.
      apply (IHQ z); auto.
      intros. apply H1; simpl; auto.
      intros.
      generalize H3; intros.
      apply H2 in H3.
      simpl in H3; intuition. subst.
      elim n; auto.
    Qed.

    Lemma find_largest_projection : forall k k' (Hk:k≤k') x,
      (exists m, (x,m) ∈ fds_project I FDS k k' Hk) ->
      exists y,
        (y,y) ∈ proj1_sig (fds_F I FDS k) /\
        (x,y) ∈ fds_project I FDS k k' Hk /\
        forall q,
          (x,q) ∈ fds_project I FDS k k' Hk ->
          (q,y) ∈ proj1_sig (fds_F I FDS k).
    Proof.
      intros. generalize (fds_ep_pair I FDS k k' Hk).
      intros [????].
      destruct H as [m ?].
      apply find_largest_projection_aux with
        (fds_F I FDS k')
        (map (@fst _ _) (proj1_sig (fds_F I FDS k)))
        m; auto.
      destruct finep_approx4 as [?[?[??]]].
      apply H0 in H. destruct H; auto.
      intros.
      apply in_map_iff in H0.
      destruct H0 as [[a b] [??]].
      simpl in H0. subst a.
      destruct (proj2_sig (fds_F I FDS k)).
      apply N2in in H1.
      apply H0 in H1. auto.
      intros.
      left.
      apply in_map_iff.
      exists (y,y); split; simpl; auto.
      destruct finep_approx4 as [?[?[??]]].
      apply H1 in H0. destruct H0; auto.
      apply N2in; auto.
    Qed.

    Lemma lim_ord_has_normals : has_normals lim_ord lim_ord_effective hf.
    Proof.
      hnf; intros X Hinh.
      set (IS := map lim_idx X : finset I).
      destruct (choose_ub_set IS) as [k Hk].
      unfold IS.
      destruct hf; auto.
      destruct Hinh.
      destruct H.
      destruct H.
      destruct X; simpl.
      elim H.
      exists (lim_idx c).
      apply cons_elem; auto.
      destruct (build_lim_set k) as [Z [??]].
      exists Z. split.
      hnf; simpl; intros.
      destruct H1 as [q [??]].
      assert (lim_idx q ≤ k).
      apply Hk.
      unfold IS.
      exists (lim_idx q).
      split; auto.
      apply in_map_iff.
      exists q; split; auto.
      destruct (lim_embed_upwards q k H3) as [q' [??]].
      generalize (lim_ok q').
      rewrite H4. intros.
      destruct (H0 _ H6) as [z [??]].
      exists z. split; auto.
      transitivity q; auto.
      transitivity q'; auto.
      destruct q'. simpl in *.
      destruct z; simpl in *.
      subst lim_elem1.
      subst lim_idx0.
      apply H in H7. simpl in H7. subst lim_idx1.
      clear.
      split; hnf; simpl; auto.
      exists k. exists (ord_refl _ _). exists (ord_refl _ _). auto.
      exists k. exists (ord_refl _ _). exists (ord_refl _ _). auto.

      hnf; intros.      
      split.
        case_eq hf; intros; hnf; auto.
        destruct (proj2_sig (fds_F I FDS k)) as [?[?[??]]].
        revert H5. pattern hf at 1.
        rewrite H1.
        intros [a [b ?]].
        apply H2 in H5.
        apply H0 in H5.
        destruct H5 as [z [??]].
        exists z. exists z. split; auto.

      repeat intro.
      destruct (choose_ub k (lim_idx z)) as [k' [??]].
      generalize (lim_ok z). intros.
      generalize (fds_ep_pair I FDS (lim_idx z) k' H3).
      intros [????].
      apply finep_id3 in H4. clear finep_id3 finep_id4.
      rewrite finrel_compose_elem in H4; eauto.
      destruct H4 as [z' [??]].
      assert ((z',z') ∈ proj1_sig (fds_F I FDS k')).
      destruct finep_approx3.
      apply H6 in H4. destruct H4; auto.
      clear finep_approx3 finep_approx4.

      assert (
        exists z'',
        (z'',z'') ∈ proj1_sig (fds_F I FDS k) /\
        (z',z'') ∈ fds_project I FDS  k k' H2 /\
        (forall q, (z',q) ∈ fds_project I FDS k k' H2 -> 
          (q,z'') ∈ proj1_sig (fds_F I FDS k))).

        apply find_largest_projection.

        generalize (refl_equal hf).
        pattern hf at 2. case hf. intros.

        rewrite H7 in Hinh0.
        destruct Hinh0 as [x ?].
        apply H1 in H8.
        apply finsubset_elem in H8.
        destruct H8.
        destruct H8 as [q [??]].
        rewrite H10 in H9.
        clear x H10.
        rename q into x.
        generalize (H x H8); intro.
        generalize (lim_ok x); intros.
        rewrite H10 in H11.
        destruct (fds_ep_pair I FDS k k' H2).
        apply finep_id3 in H11.
        clear finep_id3 finep_id4.
        rewrite finrel_compose_elem in H11; eauto.
        destruct H11 as [x' [??]].
        generalize H9; intro.
        rewrite lim_ord_rel_forall_exists in H13.
        rewrite H10 in H13.
        generalize H11. intro.
        apply (H13 k' H2 H3) in H14.
        assert ((x',z') ∈ proj1_sig (fds_F I FDS k')).
        destruct (fds_ep_pair I FDS (lim_idx z) k' H3).
        apply finep_id4.
        rewrite finrel_compose_elem; eauto.
        exists (lim_elem x).
        destruct finep_approx4 as [?[?[??]]].
        apply H17 with x' (lim_elem x); auto.
        generalize (lim_ok x). rewrite H10; auto.
        intros. rewrite <- H9. auto.

        intros.
        destruct (fds_ep_pair I FDS k k' H2).        
        destruct finep_approx4 as [_ [_ [_ ?]]].
        revert H8. pattern hf at 1.
        rewrite H7.
        intros. apply H8. auto.

      destruct H7 as [z'' [?[??]]].
      exists (LimSet k z'' H7).
      split.
      repeat intro.
      generalize H10. intro.
      apply H1 in H10.
      apply finsubset_elem in H10.
      destruct H10.
      destruct H10 as [q [??]].
      rewrite H13 in H12. rewrite H13 in H11.
      rewrite H13. clear x H13. rename q into x.
      rewrite lim_ord_rel_forall_exists in H12.

      assert (lim_idx x = k).
      apply H. auto.
      hnf. simpl.
      exists k. rewrite H13. exists (ord_refl _ _). exists (ord_refl _ _).
      intros.
      rewrite H13 in H12.
      generalize (H12 k' H2 H3). intros.
      generalize (lim_ok x); intros.
      rewrite H13 in H16.
      generalize (fds_ep_pair I FDS k k' H2).
      intros [????].
      apply finep_id3 in H16.
      rewrite finrel_compose_elem in H16; eauto.
      destruct H7 as [q [??]].
      clear finep_approx3 finep_approx4 finep_id3 finep_id4.
      destruct H16 as [x' [??]].
      generalize H16; intro.
      apply (H12 k' H2 H3) in H16.

      rewrite (fds_ident I FDS k).
      apply finrel_inv_elem.
      rewrite (fds_ident I FDS k) in H14.
      rewrite finrel_inv_elem in H14.
      generalize (proj2_sig (fds_F I FDS k)).
      intros [?[?[??]]].
      apply H22 with (lim_elem x); auto.
      clear H20 H21 H22 H23.
      apply H9.
      generalize (fds_compose' I FDS k k' k' H2 (ord_refl _ _) H2).
      intros. rewrite <- H20. clear H20.
      rewrite finrel_compose_elem; eauto.
      exists x'; split; auto.
      rewrite (fds_ident' I FDS k').
      apply finrel_inv_elem.
      generalize (fds_ep_pair I FDS (lim_idx z) k' H3).
      intros [????].
      apply finep_id4.
      rewrite finrel_compose_elem; eauto.
      destruct (fds_ep_pair I FDS k' k' (ord_refl I k')); eauto.
      destruct (fds_ep_pair I FDS k k' H2); eauto.
      intros. rewrite <- H12; auto.
    
      simpl. apply finsubset_elem.
      intros. rewrite <- H10; auto.
      split; auto.
      destruct (H0 z'') as [q [??]]; auto.
      exists q. split; auto.
      destruct q; simpl in *.
      subst lim_elem0.
      apply H in H10. simpl in H10. subst lim_idx0.
      
      split; hnf; simpl.
      exists k. exists (ord_refl _ _). exists (ord_refl _ _). auto.
      exists k. exists (ord_refl _ _). exists (ord_refl _ _). auto.

      hnf. simpl.
      exists k'. exists H2. exists H3.
      intros.
      assert ((z0,z') ∈ (proj1_sig (fds_F I FDS k'))).
      destruct (fds_ep_pair I FDS k k' H2).
      apply finep_id4.
      rewrite  finrel_compose_elem; eauto.
      destruct (fds_ep_pair I FDS (lim_idx z) k' H3).
      destruct finep_approx3 as [?[?[??]]].
      apply H13 with (lim_elem z) z'; auto.       
      apply lim_ok.
    Qed.

    Canonical Structure lim_ord_plotkin : plotkin_order hf lim_ord :=
      norm_plt lim_ord lim_ord_effective hf lim_ord_has_normals.


(*
Program Definition ex_eset_semidec {A:preord} (P:A -> Prop) (H:semidec P)
  : semidec (fun X:eset A => exists a:A, a ∈ X /\ P a)
  := Semidec _ _ (ex_eset_setdec A (decset P H)) _ _.
Next Obligation.
  intros.
  destruct H1 as [a [??]]. exists a; split; auto.
  rewrite <- H0; auto.
Qed.
Next Obligation.
  intros. split; intros.
  unfold ex_eset_setdec in H0.
  apply union_axiom in H0.
  destruct H0 as [X ?].
  destruct H0.
  destruct H0 as [n ?].
  case_eq (a n); intros.
  rewrite H2 in H0.
  exists c.
  split.    
  exists n. rewrite H2. auto.
  rewrite H0 in H1.
  apply (decset_correct P H) in H1. auto.
  rewrite H2 in H0. elim H0.
  rename a into X.
  destruct H0 as [a [??]].
  unfold ex_eset_setdec.
  apply union_axiom.
  exists (decset P H a).
  split.
  destruct H0 as [n ?].
  exists n.
  destruct (X n).
  split; hnf; intros.
  rewrite (decset_correct P H).
  rewrite (decset_correct P H) in H2.
  eapply (decset_prop_ok P H a c); auto.
  rewrite (decset_correct P H).
  rewrite (decset_correct P H) in H2.
  eapply (decset_prop_ok P H c a); auto.
  auto.
  rewrite (decset_correct P H). auto.
Qed.

Lemma asdf n : semidec
       (fun xy:fds_F I FDS n × lim_ord =>
         exists k, exists q, exists (Hnk:n≤k) (Hyk:lim_idx (snd xy) ≤k),
           (proj1_sig (fst xy), q) ∈ fds_embed I FDS n k Hnk /\
           (q, lim_elem (snd xy)) ∈ fds_project I FDS (lim_idx (snd xy)) k Hyk).
Proof.
  apply ex_eset_semidec.
  apply se


Check (fun n => @esubset (fds_F I FDS n × lim_ord)
       (fun xy => let (x,y) := xy in
         exists k, exists q, exists (Hnk:n≤k) (Hyk:lim_idx y≤k),
           (proj1_sig x, q) ∈ fds_embed I FDS n k Hnk /\
           (q, lim_elem y) ∈ fds_project I FDS (lim_idx y) k Hyk)
       ).

    Definition lim_embed_rel (n:I) : erel (fds_F I FDS n) lim_ord :=
      

        eprod (eff_enum _ (finord_effective hf (fds_F I FDS n)))
              (eff_enum _ lim_ord_effective).
*)

    Definition lim_embed_spec n (x:finord_to_preord hf (fds_F I FDS n)) (y:lim_set) :=
      exists k (Hnk:n≤k) (Hyk:lim_idx y≤k), exists q,
        (proj1_sig x, q) ∈ fds_embed I FDS n k Hnk /\
        (q, lim_elem y) ∈ fds_project I FDS (lim_idx y) k Hyk.

    Definition lim_proj_spec n (x:lim_set) (y:finord_to_preord hf (fds_F I FDS n)) :=
      exists k (Hxk:lim_idx x ≤ k) (Hnk: n ≤ k), exists q,
        (lim_elem x, q) ∈ fds_embed I FDS (lim_idx x) k Hxk /\
        (q, proj1_sig y) ∈ fds_project I FDS n k Hnk.
        
    Lemma lim_proj_cone m n (Hmn:m≤n) (x:lim_set) (z:fds_F I FDS m) :
      lim_proj_spec m x z <-> 
      exists y, 
        lim_proj_spec n x y /\ 
        (proj1_sig y,proj1_sig z) ∈ fds_project I FDS m n Hmn.
    Proof.
      split; intros.
      destruct H as [k [Hxk [Hzk [q [??]]]]].
      destruct z as [z Hz]; simpl in *.
      destruct (choose_ub n k) as [k' [??]].
      assert (Hmk' : m ≤ k').
      transitivity n; auto.
      assert (Hxk' : lim_idx x ≤ k').
      transitivity k; auto.
      
      assert ((q,q) ∈ proj1_sig (fds_F I FDS k)).
      destruct (fds_ep_pair I FDS m k Hzk).
      destruct finep_approx4 as [?[?[??]]].
      apply H3 in H0. destruct H0; auto.
      destruct (fds_ep_pair I FDS k k' H2).
      apply finep_id3 in H3.
      clear finep_id3 finep_id4.
      rewrite finrel_compose_elem in H3; eauto.
      destruct H3 as [q' [??]].
      assert ((q', z) ∈ fds_project I FDS m k' Hmk').
      generalize (fds_compose' I FDS m k k' Hzk H2 Hmk').
      intros. rewrite <- H5; clear H5.
      rewrite finrel_compose_elem; eauto.
      destruct (fds_ep_pair I FDS m k Hzk); eauto.
      generalize (fds_compose' I FDS m n k' Hmn H1 Hmk').
      intros. rewrite <- H6 in H5. clear H6.
      rewrite finrel_compose_elem in H5; eauto.
      destruct H5 as [y [??]].
      assert ((y,y) ∈ proj1_sig (fds_F I FDS n)).
      destruct (fds_ep_pair I FDS m n Hmn).
      destruct finep_approx6 as [?[?[??]]].
      apply H7 in H6. destruct H6; auto.
      exists (exist _ y H7).
      split; simpl; auto.
      hnf. simpl.
      exists k'. exists Hxk'. exists H1. 
      exists q'. split; auto.
      generalize (fds_compose I FDS (lim_idx x) k k' Hxk H2 Hxk').
      intros. rewrite <- H8; clear H8.
      rewrite finrel_compose_elem; eauto.
      destruct (fds_ep_pair I FDS (lim_idx x) k Hxk); eauto.
      destruct (fds_ep_pair I FDS n k' H1); eauto.
      destruct (fds_ep_pair I FDS m n Hmn); eauto.
      
      destruct H as [y [??]].
      hnf in H.
      destruct H as [k [Hxk [Hnk [q [??]]]]].
      hnf.
      assert (Hmk : m ≤ k). transitivity n; auto.
      exists k. exists Hxk. exists Hmk. exists q. split; auto.
      generalize (fds_compose' I FDS m n k Hmn Hnk Hmk).
      intros. rewrite <- H2; clear H2.
      rewrite finrel_compose_elem.
      exists (proj1_sig y); split; auto.
      destruct (fds_ep_pair I FDS n k Hnk); eauto.
      destruct (fds_ep_pair I FDS m n Hmn); eauto.
    Qed.

    Lemma lim_embed_cocone m n (Hmn:m≤n) (x:fds_F I FDS m) z :
      lim_embed_spec m x z <-> 
      exists y,
        (proj1_sig x,proj1_sig y) ∈ fds_embed I FDS m n Hmn /\
        lim_embed_spec n y z.
    Proof.
      split; intros.
      destruct H as [k [Hmk [Hzk [q [??]]]]].
      destruct x as [x Hx]; simpl in *.
      destruct (choose_ub n k) as [k' [??]].
      assert (Hmk' : m ≤ k').
      transitivity n; auto.
      assert (Hzk' : lim_idx z ≤ k').
      transitivity k; auto.
      
      assert ((q,q) ∈ proj1_sig (fds_F I FDS k)).
      destruct (fds_ep_pair I FDS m k Hmk).
      destruct finep_approx3 as [?[?[??]]].
      apply H3 in H. destruct H; auto.
      destruct (fds_ep_pair I FDS k k' H2).
      apply finep_id3 in H3.
      clear finep_id3 finep_id4.
      rewrite finrel_compose_elem in H3; eauto.
      destruct H3 as [q' [??]].
      assert ((x, q') ∈ fds_embed I FDS m k' Hmk').
      generalize (fds_compose I FDS m k k' Hmk H2 Hmk').
      intros. rewrite <- H5; clear H5.
      rewrite finrel_compose_elem; eauto.
      destruct (fds_ep_pair I FDS m k Hmk); eauto.
      generalize (fds_compose I FDS m n k' Hmn H1 Hmk').
      intros. rewrite <- H6 in H5. clear H6.
      rewrite finrel_compose_elem in H5; eauto.
      destruct H5 as [y [??]].
      assert ((y,y) ∈ proj1_sig (fds_F I FDS n)).
      destruct (fds_ep_pair I FDS m n Hmn).
      destruct finep_approx5 as [?[?[??]]].
      apply H7 in H5. destruct H5; auto.
      exists (exist _ y H7).
      split; simpl; auto.
      hnf. simpl.
      exists k'. exists H1. exists Hzk'. 
      exists q'. split; auto.
      generalize (fds_compose' I FDS (lim_idx z) k k' Hzk H2 Hzk').
      intros. rewrite <- H8; clear H8.
      rewrite finrel_compose_elem; eauto.
      destruct (fds_ep_pair I FDS (lim_idx z) k Hzk); eauto.
      destruct (fds_ep_pair I FDS m n Hmn); eauto.
      destruct (fds_ep_pair I FDS n k' H1); eauto.
      
      destruct H as [y [??]].
      hnf in H0.
      destruct H0 as [k [Hnk [Hzk [q [??]]]]].
      hnf.
      assert (Hmk : m ≤ k). transitivity n; auto.
      exists k. exists Hmk. exists Hzk. exists q. split; auto.
      generalize (fds_compose I FDS m n k Hmn Hnk Hmk).
      intros. rewrite <- H2; clear H2.
      rewrite finrel_compose_elem.
      exists (proj1_sig y); split; auto.
      destruct (fds_ep_pair I FDS m n Hmn); eauto.
      destruct (fds_ep_pair I FDS n k Hnk); eauto.
    Qed.

    Lemma lim_proj_dir0 n x : hf = false ->
      exists y, lim_proj_spec n x y.
    Proof.
      intros.
      destruct (choose_ub (lim_idx x) n) as [k [Hxk Hnk]].

      assert (exists q, (lim_elem x, q) ∈ fds_embed I FDS (lim_idx x) k Hxk).
      destruct (fds_ep_pair I FDS (lim_idx x) k Hxk) as [? _ _ _].
      destruct finep_approx3 as [_ [_ [_ ?]]].
      revert H0.
      generalize (lim_ok x).
      destruct (fds_F I FDS (lim_idx x)). simpl.
      rewrite H. simpl; intros.
      apply H1 in H0.
      eauto.
      destruct H0 as [q ?].
      
      assert ((q,q) ∈ proj1_sig (fds_F I FDS k)).
      destruct (fds_ep_pair I FDS (lim_idx x) k Hxk) as [? _ _ _].
      destruct finep_approx3 as [? _].
      apply H1 in H0.
      destruct H0; auto.

      assert (exists y, (q, y) ∈ fds_project I FDS n k Hnk).
      destruct (fds_ep_pair I FDS n k Hnk) as [_ ? _ _].
      destruct finep_approx3 as [_ [_ [_ ?]]].
      revert H1 H2.
      destruct (fds_F I FDS k). simpl.
      rewrite H. simpl; intros.
      apply H2 in H1.
      eauto.
      destruct H2 as [y ?].

      assert ((y,y) ∈ proj1_sig (fds_F I FDS n)).
      destruct (fds_ep_pair I FDS n k Hnk) as [_ ? _ _].
      destruct finep_approx3 as [? _].
      apply H3 in H2. destruct H2; auto.
      exists (exist _ y H3).
      hnf.
      exists k. exists Hxk. exists Hnk. exists q. split; auto.
    Qed.

    Lemma lim_proj_dir n x y y' :
      lim_proj_spec n x y ->
      lim_proj_spec n x y' -> exists z,
        lim_proj_spec n x z /\ y ≤ z /\ y' ≤ z.
    Proof.
      intros.
      destruct H as [k [Hxk [Hnk [q [??]]]]].
      destruct H0 as [k' [Hxk' [Hnk' [q' [??]]]]].
      destruct (choose_ub k k') as [k'' [??]].
      assert ((q,q) ∈ proj1_sig (fds_F I FDS k)).
      destruct (fds_ep_pair I FDS (lim_idx x) k Hxk).
      destruct finep_approx3.
      apply H5 in H.
      destruct H; auto.
      assert ((q',q') ∈ proj1_sig (fds_F I FDS k')).
      destruct (fds_ep_pair I FDS (lim_idx x) k' Hxk').
      destruct finep_approx3.
      apply H6 in H0.
      destruct H0; auto.
      destruct (fds_ep_pair I FDS k k'' H3).
      generalize H5; intro.
      apply finep_id3 in H5.
      clear finep_id3 finep_id4.
      rewrite finrel_compose_elem in H5; eauto.
      destruct H5 as [z1 [??]].
      clear finep_approx3 finep_approx4.

      destruct (fds_ep_pair I FDS k' k'' H4).
      generalize H6; intro.
      apply finep_id3 in H6.
      clear finep_id3 finep_id4.
      rewrite finrel_compose_elem in H6; eauto.
      destruct H6 as [z2 [??]].
      assert (Hxk'': lim_idx x ≤ k'').
      transitivity k; auto.
      clear finep_approx3 finep_approx4.

      assert ((lim_elem x, z1) ∈ fds_embed I FDS (lim_idx x) k'' Hxk'').
      generalize (fds_compose I FDS (lim_idx x) k k'' Hxk H3 Hxk'').
      intros. rewrite <- H11. clear H11.
      rewrite finrel_compose_elem; eauto.
      destruct (fds_ep_pair I FDS _ _ Hxk); eauto.
      destruct (fds_ep_pair I FDS _ _ H3); eauto.

      assert ((lim_elem x, z2) ∈ fds_embed I FDS (lim_idx x) k'' Hxk'').
      generalize (fds_compose I FDS (lim_idx x) k' k'' Hxk' H4 Hxk'').
      intros. rewrite <- H12. clear H12.
      rewrite finrel_compose_elem; eauto.
      destruct (fds_ep_pair I FDS _ _ Hxk'); eauto.
      destruct (fds_ep_pair I FDS _ _ H4); eauto.
      
      destruct (fds_ep_pair I FDS _ _ Hxk''); eauto.
      destruct finep_approx3 as [?[?[??]]].
      destruct (H15 (lim_elem x) z1 z2) as [z' [?[??]]]; auto.
      clear H13 H14 H15 H16 finep_approx4 finep_id3 finep_id4.
      assert ((z',q) ∈ fds_project I FDS k k'' H3).
      destruct (fds_ep_pair I FDS _ _ H3).
      destruct finep_approx4 as [?[?[??]]].
      apply H14 with z1 q; eauto.
      assert ((z',q') ∈ fds_project I FDS k' k'' H4).
      destruct (fds_ep_pair I FDS _ _ H4).
      destruct finep_approx4 as [?[?[??]]].
      apply H15 with z2 q'; eauto.
      
      assert (Hnk'' : n ≤ k'').
      transitivity k'; auto.

      assert ((z',proj1_sig y) ∈ fds_project I FDS n k'' Hnk'').
      generalize (fds_compose' I FDS n k k'' Hnk H3 Hnk'').
      intros. rewrite <- H15. clear H15.
      rewrite finrel_compose_elem. eauto.
      destruct (fds_ep_pair I FDS _ _ H3); eauto.
      destruct (fds_ep_pair I FDS _ _ Hnk); eauto.
      
      assert ((z',proj1_sig y') ∈ fds_project I FDS n k'' Hnk'').
      generalize (fds_compose' I FDS n k' k'' Hnk' H4 Hnk'').
      intros. rewrite <- H16. clear H16.
      rewrite finrel_compose_elem. eauto.
      destruct (fds_ep_pair I FDS _ _ H4); eauto.
      destruct (fds_ep_pair I FDS _ _ Hnk'); eauto.
      destruct (fds_ep_pair I FDS _ _ Hnk''); eauto.
      destruct finep_approx4 as [?[?[??]]].
      destruct (H22 z' (proj1_sig y) (proj1_sig y')) as [y'' [?[??]]]; auto.
      clear H20 H21 H22 H23 finep_id3 finep_id4.

      assert ((y'',y'') ∈ proj1_sig (fds_F I FDS n)).
      destruct (fds_F I FDS n) as [G HG]. simpl.
      destruct HG as [?[??]]. simpl in *.
      eapply m0; eauto.
      exists (exist _ y'' H20).
      split.
      hnf. simpl.
      exists k''. exists Hxk''. exists Hnk''.
      exists z'. split; auto.
      split; auto.
    Qed.

    Lemma lim_proj_spec_order n x x' y y' : x ≤ x' -> y' ≤ y ->
      lim_proj_spec n x y -> lim_proj_spec n x' y'.
    Proof.
       intros.
       destruct H1 as [k [Hxk [Hnk [q [??]]]]].
       generalize H.
       rewrite lim_ord_rel_forall_exists in H.
       intros.
       destruct H3 as [k' [Hxk' [Hx'k' ?]]].
       destruct (choose_ub k k') as [k'' [??]].
       exists k''.
       assert (Hx'k'' : lim_idx x' ≤ k'').
       transitivity k'; auto.
       assert (Hnk'' : n ≤ k'').
       transitivity k; auto.
       exists Hx'k''. exists Hnk''.
       assert ((q,q) ∈ proj1_sig (fds_F I FDS k)).
       generalize (fds_ep_pair I FDS (lim_idx x) k Hxk).
       intros [????].
       destruct finep_approx3.
       apply H6 in H1. destruct H1; auto.
       generalize (fds_ep_pair I FDS k k'' H4).
       intros. destruct H7 as [? ? ? _].
       apply finep_id3 in H6.
       rewrite finrel_compose_elem in H6; eauto.
       clear finep_id3.
       destruct H6 as [q' [??]].
       exists q'.
       assert (Hxk'' : lim_idx x ≤ k'').
       transitivity k'; auto.
       split.
       apply H with Hxk''.
       generalize (fds_compose I FDS (lim_idx x) k k'' Hxk H4 Hxk'').
       intros. rewrite <- H8. clear H8.
       generalize (fds_ep_pair I FDS _ k Hxk).
       intros [?? _ _].
       rewrite finrel_compose_elem; eauto.
       generalize (fds_compose' I FDS n k k'' Hnk H4 Hnk'').
       intros.
       rewrite <- H8; clear H8.
       generalize (fds_ep_pair I FDS n k Hnk).
       intros [????].
       rewrite finrel_compose_elem; eauto.
       exists q; split; auto.
       destruct finep_approx6 as [?[?[??]]].
       apply H9 with q (proj1_sig y); auto.
       generalize (fds_ep_pair I FDS (lim_idx x) k Hxk).
       intros [????].
       destruct finep_approx3.
       apply H8 in H2.
       destruct H2; auto.
     Qed.


  End bilimit.
End finite_limit.