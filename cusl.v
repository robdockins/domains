(* Copyright (c) 2014, Robert Dockins *)

Require Import List.

Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import directed.
Require Import plotkin.

Definition is_lub (A:preord) (x y z:A) :=
  x ≤ z /\ y ≤ z /\ forall z', x ≤ z' -> y ≤ z' -> z ≤ z'.
Arguments is_lub [A] x y z.

Record cusl (A:preord) :=
  { cusl_lub : forall x y:A, 
                 { z | is_lub x y z } + 
                 { forall z, x ≤ z -> y ≤ z -> False }
  }.

Lemma cusl_finset (A:preord) (C:cusl A) (X:finset A) (HX:inh true X) :
  { z | least_upper_bound z X } + { forall z, upper_bound z X -> False }.
Proof.
  revert HX. induction X; intros.
  - elimtype False. hnf in HX.
    destruct HX. apply nil_elem in H. auto.
  - destruct X.
    + left. exists a.
      split.
      * hnf; intros. apply cons_elem in H. destruct H.
        ** rewrite H. auto.
        ** apply nil_elem in H. elim H.
      * intros. apply H. apply cons_elem; auto.
    + destruct IHX.
      * exists c. apply cons_elem. auto.
      * destruct s.
        destruct (cusl_lub A C x a).
        ** destruct s as [z [?[??]]].
           left. exists z.
           split.
           *** hnf; intros.
               apply cons_elem in H2. destruct H2.
               **** rewrite H2. auto.
               **** rewrite <- H. apply l. auto.
           *** intros. apply H1.
               **** destruct l. apply H4.
                    red; intros.
                    apply H2. apply cons_elem; auto.
               **** apply H2. apply cons_elem; auto.
        ** right; intros.
           apply (f z).
           *** destruct l. apply H1.
               red; intros. apply H. apply cons_elem; auto.
           *** apply H. apply cons_elem; auto.
      * right; intros.
        apply (f z).
        red; intros. apply H. apply cons_elem; auto.
Qed.


Fixpoint calc_lubs A (C:cusl A) (l:list (finset A)) : finset A :=
  match l with
  | nil => nil
  | x::l' => 
      match inh_dec A true x with
      | left Hx => 
        match cusl_finset A C x Hx with
        | inleft (exist _ z Hz) => z::nil
        | inright _ => nil
        end
      | right Hx => nil
      end ++ calc_lubs A C l'
  end.

Lemma calc_lubs_correct A C l z :
  z ∈ calc_lubs A C l <-> exists x, In x l /\ inh true x /\ least_upper_bound z x.
Proof.
  induction l; simpl.
  - split; intros.  
    + apply nil_elem in H; elim H.
    + destruct H as [?[??]]. elim H.
  - destruct (inh_dec A true a).
    + destruct (cusl_finset A C a i).
      * destruct s as [q Hz].
        simpl.
        split; intros.
        ** apply cons_elem in H. destruct H.
           *** exists a. split; auto. split; auto.
               rewrite H. auto.
           *** apply IHl in H.
               destruct H as [x [?[??]]]. exists x; split; auto.
        ** destruct H as [x [?[??]]]. destruct H.
           *** subst x.
               apply cons_elem. left.
               destruct Hz; destruct H1.
               split; auto. 
           *** apply cons_elem; right. apply IHl. eauto.
      * simpl.
        rewrite IHl.
        split; intros [x [?[??]]]; exists x; split; auto.
        destruct H.
        ** subst a.
           elim (f z). destruct H1; auto. 
        ** auto.
    + simpl.
      rewrite IHl.
      split; intros [x [?[??]]]; exists x; split; auto.
      destruct H.
      * subst a.
        elim n. hnf; eauto.
      * auto.
Qed.

Definition sub_lubs A (C:cusl A) (X:finset A) : finset A :=
  calc_lubs A C (list_finsubsets X).

Lemma sub_lubs_correct A C X lub (HA:ord_dec A) :
  lub ∈ sub_lubs A C X <-> exists Y:finset A, Y ⊆ X /\ inh true Y /\ least_upper_bound lub Y.
Proof.
  unfold sub_lubs.
  rewrite calc_lubs_correct.
  split; intros [Y [?[??]]].
  - exists Y. split; auto.
    apply list_finsubsets_correct. exists Y; split; auto.
  - apply list_finsubsets_complete in H; auto.
    destruct H as [Y' [??]].  
    exists Y'. split; auto.
    split.
    + destruct H0 as [q ?]. exists q. rewrite <- H2; auto.
    + rewrite <- H2. auto.
Qed.

Lemma cusl_has_normals (A:preord) (Heff:effective_order A) (C:cusl A) : has_normals A Heff true.
Proof.
  red; intros.
  exists (X ++ sub_lubs A C X).
  split.
  - red; intros. apply app_elem; auto.
  - split.
    + destruct Hinh as [q ?]. exists q. apply app_elem. auto.
    + intros. apply prove_directed; auto.
      intros.
      apply finsubset_elem in H.
      apply finsubset_elem in H0.
      destruct H. destruct H0.
      destruct (cusl_lub A C x y) as [[q ?]|Hq];
        [| elim (Hq z); auto ].
      destruct i as [?[??]].
      exists q. split; auto. split; auto.
      apply finsubset_elem.
      intros. destruct H6. rewrite H8. auto.
      split.
      * apply app_elem. right.
        apply sub_lubs_correct. 
        constructor. apply (eff_ord_dec A Heff).
        apply app_elem in H.
        apply app_elem in H0.
        destruct H; [ destruct H0 |].
        ** exists (x::y::nil).
           split. apply cons_subset; auto. apply cons_subset; auto. apply nil_subset.
           split. exists x. apply cons_elem; auto.
           split. apply ub_cons; auto. apply ub_cons; auto. apply ub_nil.
           intros. apply H5. apply H6. apply cons_elem; auto.
           apply H6. apply cons_elem. right. apply cons_elem. auto.
        ** apply sub_lubs_correct in H0.
           destruct H0 as [Y2 [?[??]]].
           exists (x::Y2).
           split.
           *** red; intros. apply cons_elem in H8. destruct H8.
               rewrite H8; auto. auto.
           *** split. exists x. apply cons_elem; auto.
           split. red; intros.
           **** apply cons_elem in H8. destruct H8; auto.
                ***** rewrite H8. auto.
                ***** destruct H7. rewrite <- H4. apply H7; auto.
           **** intros. apply H5.
                ***** apply H8. apply cons_elem; auto.
                ***** destruct H7. apply H9. red; intros. apply H8.
                      apply cons_elem; auto.

           *** constructor. apply (eff_ord_dec A Heff).
        ** apply sub_lubs_correct in H.
           destruct H as [Y1 [?[??]]].
           destruct H0.
           *** exists (y::Y1).
               split.
               **** red; intros. apply cons_elem in H8. destruct H8.
                    rewrite H8; auto. auto.
               **** split. exists y. apply cons_elem; auto.
                    split.
                    ***** red; intros.
                          apply cons_elem in H8. destruct H8; auto.
                          ****** rewrite H8. auto.
                          ****** destruct H7. rewrite <- H3. apply H7; auto.
                    ***** intros. apply H5.
                          ****** destruct H7. apply H9. red; intros. apply H8.
                                 apply cons_elem; auto.
                          ****** apply H8. apply cons_elem; auto.

           *** apply sub_lubs_correct in H0.
               destruct H0 as [Y2 [?[??]]].
               exists (Y1++Y2).
               split.
               **** red; intros. apply app_elem in H10. destruct H10; auto.
               **** split.
                    ***** destruct H6 as [n ?]. exists n. apply app_elem; auto.
                    ***** split.
                          ****** hnf; intros. apply app_elem in H10. destruct H10.
                                 ******* destruct H7.
                                         rewrite <- H3. apply H7; auto.
                                 ******* destruct H9.
                                         rewrite <- H4. apply H9; auto.
                          ****** intros.
                                 apply H5.
                                 ******* destruct H7. apply H11.
                                         red; intros. apply H10. apply app_elem; auto.
                                 ******* destruct H9. apply H11.
                                         red; intros. apply H10. apply app_elem; auto.
                                         
               **** constructor. apply (eff_ord_dec A Heff).
           *** constructor. apply (eff_ord_dec A Heff).
      * apply H5; auto.    
      * intros. destruct H2. transitivity x0; auto.
      * intros. destruct H2. transitivity x0; auto.
Qed.


Definition cusl_plotkin (A:preord) (Heff:effective_order A) (C:cusl A) 
  : plotkin_order true A
  :=  norm_plt A Heff true (cusl_has_normals A Heff C).

