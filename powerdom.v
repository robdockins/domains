(* Copyright (c) 2014, Robert Dockins *)

Require Import Setoid.
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
Require Import joinable.
Require Import approx_rels.
Require Import profinite.
Require Import embed.

(** * Powerdomains

    Here we construct the lower, upper and convex powerdomains, and show that they
    form continuous functors in the category of embeddings.

    Powerdomains over a domain X re defined as preorders consisting of
    finite h-inhabited subsets of X with the upper, lower and convex ordering,
    respectively.

    Notibly, the convex powerdomain over unpointed domains has a representative
    for the empty set, which the convex powerdomain over unpointed domains lacks.
    This fact might be previously known (I am not actually sure), but it does not
    seem to be widely appreciated.
  *)

Inductive pdom_sort :=
  | Lower
  | Upper
  | Convex.

Module powerdom.
Section powerdom.
  Variable hf:bool.

  Record pdom_elem (X:preord) :=
    PdomElem
    { elem : finset X
    ; elem_inh : inh hf elem
    }.
  Arguments elem [X] p.
  Arguments elem_inh [X] p.

  Section orders.
    Variable X:preord.

    Definition lower_ord (P Q:pdom_elem X) :=
      forall x, x ∈ elem P ->
        exists y, y ∈ elem Q /\ x ≤ y.
 
    Definition upper_ord (P Q:pdom_elem X) :=
      forall y, y ∈ elem Q ->
        exists x, x ∈ elem P /\ x ≤ y.

    Definition convex_ord (P Q:pdom_elem X) :=
      lower_ord P Q /\ upper_ord P Q.

    Lemma lower_ord_refl P : lower_ord P P.
    Proof.
      repeat intro; eauto.
    Qed.

    Lemma upper_ord_refl P : upper_ord P P.
    Proof.
      repeat intro; eauto.
    Qed.

    Lemma convex_ord_refl P : convex_ord P P.
    Proof.
      split. apply lower_ord_refl. apply upper_ord_refl.
    Qed.

    Lemma lower_ord_trans P Q R :
      lower_ord P Q -> lower_ord Q R -> lower_ord P R.
    Proof.
      unfold lower_ord. intros.
      destruct (H x) as [y [??]]; auto.
      destruct (H0 y) as [z [??]]; auto.
      exists z; split; eauto.
    Qed.

    Lemma upper_ord_trans P Q R :
      upper_ord P Q -> upper_ord Q R -> upper_ord P R.
    Proof.
      unfold upper_ord. intros.
      rename y into z.
      destruct (H0 z) as [y [??]]; auto.
      destruct (H y) as [x [??]]; auto.
      exists x; split; eauto.
    Qed.

    Lemma convex_ord_trans P Q R :
      convex_ord P Q -> convex_ord Q R -> convex_ord P R.
    Proof.
      unfold convex_ord; intuition.
      eapply lower_ord_trans; eassumption.
      eapply upper_ord_trans; eassumption.
    Qed.

    Definition lower_preord_mixin :=
      Preord.Mixin (pdom_elem X) lower_ord lower_ord_refl lower_ord_trans.
    Definition upper_preord_mixin :=
      Preord.Mixin (pdom_elem X) upper_ord upper_ord_refl upper_ord_trans.
    Definition convex_preord_mixin :=
      Preord.Mixin (pdom_elem X) convex_ord convex_ord_refl convex_ord_trans.

    Hypothesis Xeff : effective_order X.

    Lemma lower_ord_dec : forall x y, {lower_ord x y}+{~lower_ord x y}.
    Proof.
      unfold lower_ord.
      destruct x as [xs Hxs]. simpl. clear Hxs.
      induction xs; simpl; intros.
      left. intros. apply nil_elem in H. elim H.
      destruct (IHxs y).
      assert ({exists q, q ∈ elem y /\ a ≤ q}+
              {forall q, q ∈ elem y -> a ≰ q}).
      clear -Xeff. destruct y as [ys Hys]. simpl. clear Hys.
      induction ys.
      right. intros. apply nil_elem in H. elim H.
      destruct (eff_ord_dec X Xeff a a0).
      left. exists a0. split; auto. apply cons_elem; auto.
      destruct IHys.
      left. destruct e as [q [??]]. exists q. split; auto.
      apply cons_elem; auto.
      right. simpl; intros.
      apply cons_elem in H. destruct H.
      intro. apply n. rewrite <- H; auto.
      apply n0; auto.
      destruct H.
      left; intros.
      apply cons_elem in H. destruct H.
      destruct e0 as [q [??]]. exists q. split; auto.
      rewrite H; auto.
      apply (e x); auto. 
      right; intro.
      destruct (H a) as [q [??]].
      apply cons_elem; auto.
      apply (n q); auto.
      right. intro.
      apply n. intros.
      apply (H x); auto.
      apply cons_elem; auto.
    Qed.
      
    Lemma upper_ord_dec : forall x y, {upper_ord x y}+{~upper_ord x y}.
    Proof.
      unfold upper_ord. intros [x Hx] [y Hy]. simpl. clear Hx Hy.
      revert x. induction y; intros.
      left. intros. apply nil_elem in H. elim H.
      destruct (IHy x).
      assert ({exists q, q ∈ x /\ q ≤ a}+
              {forall q, q ∈ x -> q ≰ a}).
      clear -Xeff. induction x.
      right. intros. apply nil_elem in H. elim H.
      destruct (eff_ord_dec X Xeff a0 a).
      left. exists a0. split; auto. apply cons_elem; auto.
      destruct IHx.
      left. destruct e as [q [??]]. exists q. split; auto.
      apply cons_elem; auto.
      right; intros. apply cons_elem in H. destruct H.
      intro. apply n. rewrite <- H; auto.
      apply n0; auto.
      destruct H.
      left. intros. apply cons_elem in H. destruct H.
      destruct e0 as [q [??]]. exists q. split; auto.
      rewrite H; auto.
      apply e; auto.
      right; intro.
      destruct (H a) as [q [??]]. apply cons_elem; auto.
      apply (n q); auto.
      right; intro.
      apply n; intros.
      apply (H y0); auto. apply cons_elem; auto.
    Qed.

    Definition pdom_ord (sort:pdom_sort) := 
      Preord.Pack
        (pdom_elem X) 
        match sort with
          | Lower  => lower_preord_mixin
          | Upper  => upper_preord_mixin
          | Convex => convex_preord_mixin
        end.

    Lemma pdom_ord_dec sort : forall (x y:pdom_ord sort), {x≤y}+{x≰y}.
    Proof.
      destruct sort. simpl.
      apply lower_ord_dec.
      apply upper_ord_dec.
      intros x y.
      destruct (lower_ord_dec x y).
      destruct (upper_ord_dec x y).
      left; split; auto.
      right; intros [??]; contradiction.
      right; intros [??]; contradiction.
    Qed.

    Lemma pdom_elem_eq_lower sort (x y:pdom_ord sort) :
      elem x ⊆ elem y -> lower_ord x y.
    Proof.
      repeat intro.
      apply H in H0. exists x0. split; auto.
    Qed.

    Lemma pdom_elem_eq_upper sort (x y:pdom_ord sort) :
      elem y ⊆ elem x -> upper_ord x y.
    Proof.
      repeat intro.
      apply H in H0. exists y0. split; auto.
    Qed.

    Lemma pdom_elem_eq_le sort (x y:pdom_ord sort) :
      elem x ≈ elem y -> x ≤ y.
    Proof.
      intros [??]; destruct sort; simpl.
      apply pdom_elem_eq_lower; auto.
      apply pdom_elem_eq_upper; auto.
      split.
      apply pdom_elem_eq_lower; auto.
      apply pdom_elem_eq_upper; auto.
    Qed.

    Lemma pdom_elem_eq_eq sort (x y:pdom_ord sort) :
      elem x ≈ elem y -> x ≈ y.
    Proof.
      intros; split; apply pdom_elem_eq_le; auto.
    Qed.    

    Definition enum_elems sort : eset (pdom_ord sort)
      := fun n =>
           match finsubsets X (eff_enum X Xeff) n with
           | None => None
           | Some l => 
              match inh_dec X hf l with
              | left Hinh => Some (PdomElem X l Hinh)
              | right _ => None
              end
           end.

    Lemma enum_elems_complete sort (x:pdom_ord sort) :
      x ∈ enum_elems sort.
    Proof.
      assert (elem x ∈ finsubsets X (eff_enum X Xeff)).
      apply (finsubsets_complete X (eff_enum X Xeff) (elem x)).
      red; intros. apply eff_complete.
      destruct H as [n ?].
      exists n. unfold enum_elems. simpl in *.
      destruct (finsubsets X (eff_enum X Xeff) n).
      destruct (inh_dec X hf c).
      apply pdom_elem_eq_eq. simpl; auto.
      apply n0. generalize (elem_inh x).
      apply inh_eq; auto.
      auto.      
    Qed.

    Definition pdom_effective sort : effective_order (pdom_ord sort) :=
      EffectiveOrder 
        (pdom_ord sort) (pdom_ord_dec sort)
        (enum_elems sort) (enum_elems_complete sort).

    Hypothesis Xplt : plotkin_order hf X.

    Definition all_tokens sort (M:finset (pdom_ord sort)) : finset X :=
      mub_closure Xplt (concat _ (map (@elem _) M)).

    Fixpoint select_pdom_elems sort (ls:finset (finset X)) : finset (pdom_ord sort) :=
      match ls with
      | nil => nil
      | x::xs =>
          match inh_dec X hf x with
          | left H => PdomElem X x H :: select_pdom_elems sort xs
          | right _ => select_pdom_elems sort xs
          end
      end.

    Lemma select_pdoms_in sort ls :
      forall x:pdom_ord sort, 
        elem x ∈ ls -> x ∈ select_pdom_elems sort ls.
    Proof.
      induction ls; simpl; intuition.
      apply nil_elem in H; elim H.
      destruct (inh_dec X hf a).
      apply cons_elem in H. destruct H.
      apply cons_elem. left.
      apply pdom_elem_eq_eq. simpl. auto.
      apply cons_elem. right. apply IHls; auto.
      apply cons_elem in H. destruct H.
      elim n. generalize (elem_inh x).
      apply inh_eq. auto.
      apply IHls; auto.      
    Qed.

    Lemma select_pdoms_in' sort ls :
      forall x:pdom_ord sort, 
        x ∈ select_pdom_elems sort ls ->
        exists x', x ≈ x' /\ elem x' ∈ ls.
    Proof.
      intros.
      induction ls; simpl in *; intros.
      apply nil_elem in H. elim H.
      destruct (inh_dec X hf a).
      apply cons_elem in H. destruct H.
      econstructor. split. apply H.
      simpl. apply cons_elem; auto.
      destruct IHls as [x' [??]]; auto.
      exists x'; split; auto. apply cons_elem; auto.
      destruct IHls as [x' [??]]; auto.
      exists x'; split; auto. apply cons_elem; auto.
    Qed.

    Definition normal_pdoms sort (M:finset (pdom_ord sort)) :=
      select_pdom_elems sort (list_finsubsets (all_tokens sort M)).

    Lemma normal_pdoms_in sort M :
      forall P:pdom_ord sort,
        (forall x, x ∈ elem P -> x ∈ all_tokens sort M) ->
        P ∈ normal_pdoms sort M.
    Proof.
      intros. unfold normal_pdoms.
      apply select_pdoms_in.
      apply list_finsubsets_complete; auto.
      apply eff_to_ord_dec. auto.
    Qed.

    Lemma normal_pdoms_in' sort M :
      forall P:pdom_ord sort,
        P ∈ normal_pdoms sort M ->
        exists P', P ≈ P' /\
          (forall x, x ∈ elem P' -> x ∈ all_tokens sort M).
    Proof.
      intros. unfold normal_pdoms.
      apply select_pdoms_in' in H.
      destruct H as [x' [??]]. exists x'; split; auto.
      intros. apply list_finsubsets_correct in H0.
      apply H0; auto.      
    Qed.

    Lemma pdom_has_normals sort :
      has_normals (pdom_ord sort) (pdom_effective sort) hf.
    Proof.
      intros M HM.
      exists (normal_pdoms sort M).
      assert (M ⊆ normal_pdoms sort M).
      red; intros.
      destruct H as [q [??]].
      rewrite H0.
      apply normal_pdoms_in.
      intros.
      unfold all_tokens.
      clear -H H1.
      induction M; simpl in *. elim H.
      destruct H. subst q.
      apply mub_clos_incl.
      apply app_elem. auto.
      eapply mub_clos_mono.
      2: apply IHM; auto.
      red; intros. apply app_elem; auto.
      split; auto.
      split.
      revert HM.
      case hf; auto.
      intros [m ?]. exists m.
      apply H; auto.

      intro z.
      apply prove_directed.

      case_eq hf; intros. auto.

      assert (exists z0:finset X,
        (forall x, x ∈ z0 -> exists x', x' ∈ elem z /\ x ≤ x') /\
        (forall x', x' ∈ elem z -> exists x, x ∈ z0 /\ x ≤ x') /\
        (forall x, x ∈ z0 -> x ∈ all_tokens sort M)).
      generalize (elem z).
      induction c.
      exists nil. split; intros.
      apply nil_elem in H1; elim H1.
      split; intros.
      apply nil_elem in H1; elim H1.
      apply nil_elem in H1; elim H1.
      destruct IHc as [z0 [?[??]]].
      destruct (mub_complete Xplt nil a) as [a' [??]].
      rewrite H0. hnf. auto.
      apply ub_nil.
      exists (a'::z0).
      split; intros.
      apply cons_elem in H6. destruct H6.
      exists a. split.
      apply cons_elem; auto. rewrite H6; auto.
      destruct (H1 x) as [x' [??]]; auto.
      exists x'; split; auto. apply cons_elem; auto.
      split; intros.
      apply cons_elem in H6. destruct H6.
      exists a'. split; auto.
      apply cons_elem; auto. rewrite H6; auto.
      destruct (H2 x') as [x [??]]; auto.
      exists x; split; auto. apply cons_elem; auto.
      apply cons_elem in H6. destruct H6.
      rewrite H6.
      unfold all_tokens.
      apply (mub_clos_mub Xplt _ nil); auto.
      rewrite H0; hnf; auto.
      apply nil_subset.
      apply H3; auto.

      destruct H1 as [z0 [?[??]]].
      assert (inh hf z0).
      rewrite H0; hnf; auto.
      exists (PdomElem X z0 H4). apply finsubset_elem.
      intros. rewrite <- H5; auto.
      split; auto.
      apply normal_pdoms_in. simpl. auto.
      destruct sort; hnf; auto.

      intros.      
      apply finsubset_elem in H0.
      apply finsubset_elem in H1.
      destruct H0. destruct H1.
      apply normal_pdoms_in' in H0.
      apply normal_pdoms_in' in H1.
      destruct H0 as [x' [??]].
      destruct H1 as [y' [??]].
      
      set (Q m := 
        (exists n, n ∈ elem x' /\ n ≤ m) /\
        (exists n, n ∈ elem y' /\ n ≤ m) /\
        (exists n, n ∈ elem z /\ m ≤ n)).
      assert (exists qelems:finset X,
        forall m, m ∈ qelems <-> Q m /\ m ∈ all_tokens sort M).

      assert (Qdec : forall m, {Q m}+{~Q m}).
      intro m. unfold Q. apply dec_conj.
      destruct (finset_find_dec _ (fun n => n ≤ m)) with (elem x').
      intros. rewrite <- H6; auto.
      intro. apply (eff_ord_dec X Xeff).
      left. destruct s; eauto.
      right. intros [??]. apply (n x0); auto.
      destruct H6; auto. destruct H6; auto.
      apply dec_conj.
      destruct (finset_find_dec _ (fun n => n ≤ m)) with (elem y').
      intros. rewrite <- H6; auto.
      intro. apply (eff_ord_dec X Xeff).
      left. destruct s; eauto.
      right. intros [??]. apply (n x0); auto.
      destruct H6; auto. destruct H6; auto.
      destruct (finset_find_dec _ (fun n => m ≤ n)) with (elem z).
      intros. rewrite <- H6; auto.
      intro. apply (eff_ord_dec X Xeff).
      left. destruct s; eauto.
      right. intros [??]. apply (n x0); auto.
      destruct H6; auto. destruct H6; auto.

      exists (finsubset X Q Qdec (all_tokens sort M)).
      intro. rewrite finsubset_elem. intuition.
      intros. destruct H7 as [?[??]].
      split.
      destruct H7 as [n [??]]. exists n. rewrite <- H6; auto.
      split.
      destruct H8 as [n [??]]. exists n. rewrite <- H6; auto.
      destruct H9 as [n [??]]. exists n. rewrite <- H6; auto.

      destruct H6 as [qelems Hq].
      assert (sort <> Lower -> inh hf qelems).
      case_eq hf; intros; hnf; auto.

      assert (upper_ord x' z /\ upper_ord y' z).
      rewrite H0 in H2. rewrite H1 in H3.
      destruct sort. elim H7; auto.
      split; auto.
      destruct H2; destruct H3; split; auto.
      generalize (elem_inh z).
      rewrite H6. intros [m ?].
      destruct H8.
      destruct (H8 m) as [mx [??]]; auto.
      destruct (H10 m) as [my [??]]; auto.
      destruct (mub_complete Xplt (mx::my::nil) m) as [q0 [??]].
      apply directed.elem_inh with mx. apply cons_elem; auto.
      apply ub_cons; auto. apply ub_cons; auto. apply ub_nil.
      exists q0. apply Hq.
      split. split.
      exists mx. split. auto. apply H15. apply cons_elem; auto.
      split.
      exists my. split. auto. apply H15.
      apply cons_elem; right. apply cons_elem; auto.
      exists m. split; auto.
      unfold all_tokens.
      apply (mub_clos_mub Xplt _ (mx::my::nil)); auto.
      eapply directed.elem_inh. apply cons_elem; auto.
      apply cons_subset; auto.
      apply cons_subset; auto.
      apply nil_subset.


      destruct sort. 
      assert (inh hf (elem x' ++ elem y')).      
      generalize (elem_inh x').
      case hf; auto.
      intros [n ?]. exists n. apply app_elem; auto.
      exists (PdomElem X (elem x'++elem y') H7).
      split.
      rewrite H0.
      hnf; simpl; intros. exists x0. split; auto. apply app_elem; auto.
      split.
      rewrite H1.
      hnf; simpl; intros. exists x0. split; auto. apply app_elem; auto.
      apply finsubset_elem. 
      intros. rewrite <- H8; auto.
      split.
      apply normal_pdoms_in.
      simpl. intros.
      apply app_elem in H8. destruct H8; auto.
      hnf; simpl; intros.
      apply app_elem in H8. destruct H8.
      rewrite H0 in H2.
      apply H2; auto.
      rewrite H1 in H3.      
      apply H3; auto.
      
      assert (Hq' : inh hf qelems).
      apply H6. discriminate.
      exists (PdomElem X qelems Hq').
      simpl.
      rewrite H0. rewrite H1.
      split.
      hnf; simpl; intros.
      apply Hq in H7. destruct H7.
      destruct H7 as [?[??]]. auto.
      split.
      hnf; simpl; intros.
      apply Hq in H7. destruct H7.
      destruct H7 as [?[??]]. auto.
      apply finsubset_elem.         
      intros. rewrite <- H7; auto.
      split.
      apply normal_pdoms_in.
      simpl. intros.
      apply Hq in H7. destruct H7; auto.
      hnf; intros.
      rewrite H0 in H2.
      rewrite H1 in H3.
      destruct (H2 y0) as [q1 [??]]; auto.
      destruct (H3 y0) as [q2 [??]]; auto.
      destruct (mub_complete Xplt (q1::q2::nil) y0).
      eapply directed.elem_inh. apply cons_elem. left; eauto.
      apply ub_cons; auto. apply ub_cons; auto. apply ub_nil.

      destruct H12.
      exists x0. split; auto.
      apply Hq.
      split.
      split. exists q1. split; auto. apply H12. apply cons_elem; auto.
      split. exists q2. split; auto. apply H12.
      apply cons_elem; right. apply cons_elem; auto.
      exists y0; split; auto.
      unfold all_tokens.
      apply mub_clos_mub with (q1::q2::nil).
      eapply directed.elem_inh. apply cons_elem. left; eauto.
      red; intros.
      apply cons_elem in H14. destruct H14. rewrite H14.
      apply H4; auto.
      apply cons_elem in H14. destruct H14. rewrite H14.
      apply H5; auto.
      apply nil_elem in H14. elim H14.
      auto.

      assert (Hq' : inh hf qelems).
      apply H6. discriminate.
      exists (PdomElem X qelems Hq').
      rewrite H0. rewrite H1.
      rewrite H0 in H2.
      rewrite H1 in H3.
      split.
      hnf; simpl; intros.
      split; hnf; simpl; intros.
      destruct H2.
      destruct (H2 x0) as [q1 [??]]; auto.
      destruct H3.
      destruct (H11 q1) as [q2 [??]]; auto.
      destruct (mub_complete Xplt (x0::q2::nil) q1).
      eapply directed.elem_inh. apply cons_elem. left; eauto.
      apply ub_cons. auto. apply ub_cons; auto. apply ub_nil.

      destruct H14.
      exists x1. split.
      apply Hq. split.
      split. exists x0. split; auto. apply H14. apply cons_elem; auto.
      split. exists q2. split; auto. apply H14.
      apply cons_elem. right. apply cons_elem; auto.
      exists q1. split; auto.
      apply mub_clos_mub with (x0::q2::nil).
      eapply directed.elem_inh. apply cons_elem. left; eauto.
      red; intros.
      apply cons_elem in H16. destruct H16. rewrite H16.
      apply H4; auto.
      apply cons_elem in H16. destruct H16. rewrite H16.
      apply H5; auto.
      apply nil_elem in H16. elim H16.
      auto.
      apply H14. apply cons_elem; auto.
      apply Hq in H7. destruct H7.
      destruct H7 as [?[??]]. auto.

      split.
      split.
      hnf; simpl; intros.
      destruct H3.
      destruct (H3 x0) as [q1 [??]]; auto.
      destruct H2.
      destruct (H11 q1) as [q2 [??]]; auto.
      destruct (mub_complete Xplt (x0::q2::nil) q1).
      eapply directed.elem_inh. apply cons_elem. left; eauto.
      apply ub_cons; auto. apply ub_cons; auto. apply ub_nil.

      destruct H14.
      exists x1. split.
      apply Hq. split.
      split. exists q2. split; auto. apply H14.
      apply cons_elem. right. apply cons_elem; auto.
      split. exists x0. split; auto. apply H14.
      apply cons_elem; auto.
      exists q1. split; auto.
      apply mub_clos_mub with (x0::q2::nil).
      eapply directed.elem_inh. apply cons_elem. left; eauto.
      red; intros.
      apply cons_elem in H16. destruct H16. rewrite H16.
      apply H5; auto.
      apply cons_elem in H16. destruct H16. rewrite H16.
      apply H4; auto.
      apply nil_elem in H16. elim H16.
      auto.
      apply H14. apply cons_elem; auto.
      hnf; intros.
      apply Hq in H7. destruct H7.
      destruct H7 as [?[??]]. auto.

      apply finsubset_elem.         
      intros. rewrite <- H7; auto.
      split.
      apply normal_pdoms_in.
      simpl. intros.
      apply Hq in H7. destruct H7; auto.
      
      split.
      hnf; intros.
      apply Hq in H7.
      destruct H7. destruct H7 as [?[??]].
      auto.
      hnf; intros.
      destruct H2.
      destruct H3.
      destruct (H8 y0) as [q1 [??]]; auto.
      destruct (H9 y0) as [q2 [??]]; auto.
      destruct (mub_complete Xplt (q1::q2::nil) y0).
      eapply directed.elem_inh. apply cons_elem. left; eauto.
      apply ub_cons; auto. apply ub_cons; auto. apply ub_nil.
      destruct H14.
      exists x0. split; auto.
      apply Hq.
      split.
      split. exists q1. split; auto. apply H14. apply cons_elem; auto.
      split. exists q2. split; auto. apply H14.
      apply cons_elem; right. apply cons_elem; auto.
      exists y0; split; auto.
      unfold all_tokens.
      apply mub_clos_mub with (q1::q2::nil).
      eapply directed.elem_inh. apply cons_elem. left; eauto.
      red; intros.
      apply cons_elem in H16. destruct H16. rewrite H16.
      apply H4; auto.
      apply cons_elem in H16. destruct H16. rewrite H16.
      apply H5; auto.
      apply nil_elem in H16. elim H16.
      auto.

      intros. rewrite <- H2; auto.
      intros. rewrite <- H2; auto.
    Qed.

    Definition pdom_plt sort : plotkin_order hf (pdom_ord sort) :=
      norm_plt (pdom_ord sort) (pdom_effective sort) hf
               (pdom_has_normals sort).
  End orders.

  Program Definition single_elem (X:preord) (x:X) : pdom_elem X :=
    PdomElem X (x::nil) _.
  Next Obligation.
    repeat intro.    
    apply directed.elem_inh with x. apply cons_elem; auto.
  Qed.

  Program Definition union_elem (X:preord) (p q:pdom_elem X) :=
    PdomElem X (elem p ++ elem q) _.
  Next Obligation.  
    intros. generalize (elem_inh q).
    case hf; auto.
    intros [n ?]. exists n. apply app_elem; auto.
  Qed.

  Program Definition concat_elem sort (X:preord) 
    (xs:list (pdom_ord X sort)) (H:inh hf xs) :=
    PdomElem X (concat _ (map (@elem _) xs)) _.
  Next Obligation.
    intros.
    revert H.
    case_eq hf; intros; auto.
    destruct H0 as [x [??]]. destruct H0. clear H1 x.
    induction xs; simpl; intros. elim H0.
    destruct H0. subst x0.
    generalize (elem_inh a).
    rewrite H. intros [q ?].
    exists q. apply app_elem. auto.
    destruct IHxs as [q ?]; auto.
    exists q. apply app_elem; auto.
  Qed.    

  Definition powerdomain sort (X:PLT.PLT hf) :=
    PLT.Ob hf (pdom_elem X)
      (PLT.Class _ _
        (match sort with
          | Lower  => lower_preord_mixin (PLT.ord X)
          | Upper  => upper_preord_mixin (PLT.ord X)
          | Convex => convex_preord_mixin (PLT.ord X)
        end)
        (pdom_effective (PLT.ord X) (PLT.effective X) sort)
        (pdom_plt (PLT.ord X) (PLT.effective X) (PLT.plotkin X) sort)).


  Section powerdomain_fmap.
    Variables X Y:PLT.PLT hf.
    Variable f: X → Y.

    Definition fmap_upper (x:pdom_elem X) (y:pdom_elem Y) :=
      forall a, a ∈ elem x -> exists b, b ∈ elem y /\ (a,b) ∈ PLT.hom_rel f.

    Definition fmap_lower (x:pdom_elem X) (y:pdom_elem Y) :=
      forall b, b ∈ elem y -> exists a, a ∈ elem x /\ (a,b) ∈ PLT.hom_rel f.

    Definition fmap_convex x y :=
      fmap_lower x y /\ fmap_upper x y.

    Lemma fmap_upper_semidec x y : semidec (fmap_upper x y).
    Proof.
      unfold fmap_upper.
      apply all_finset_semidec.
      intros.
      destruct H0 as [q [??]]. exists q; split; auto.
      apply member_eq with (a,q); auto.
      destruct H; split; split; auto.
      intros.
      apply ex_finset_semidec.
      intros.
      apply member_eq with (a,a0); auto.
      destruct H; split; split; auto.
      intros. apply semidec_in.
      apply OrdDec. 
      apply (eff_ord_dec (PLT.prod X Y)).
      apply PLT.effective.
    Qed.      

    Lemma fmap_lower_semidec x y : semidec (fmap_lower x y).
    Proof.
      unfold fmap_lower.
      apply all_finset_semidec.
      intros.
      destruct H0 as [q [??]]. exists q; split; auto.
      apply member_eq with (q,a); auto.
      destruct H; split; split; auto.
      intros.
      apply ex_finset_semidec.
      intros.
      apply member_eq with (a0,a); auto.
      destruct H; split; split; auto.
      intros. apply semidec_in.
      apply OrdDec. 
      apply (eff_ord_dec (PLT.prod X Y)).
      apply PLT.effective.
    Qed.      

    Lemma fmap_convex_semidec x y : semidec (fmap_convex x y).
    Proof.
      unfold fmap_convex. apply semidec_conj.
      apply fmap_lower_semidec.
      apply fmap_upper_semidec.
    Qed.

    Definition fmap_lower_rel : erel (pdom_ord X Lower) (pdom_ord Y Lower) :=
      @esubset (prod_preord (pdom_ord X Lower) (pdom_ord Y Lower))
        (fun z => fmap_lower (fst z) (snd z))
        (fun z => fmap_lower_semidec (fst z) (snd z))
        (eff_enum _ (effective_prod (pdom_effective X (PLT.effective X) Lower)
                                    (pdom_effective Y (PLT.effective Y) Lower))).


    Definition fmap_upper_rel : erel (pdom_ord X Upper) (pdom_ord Y Upper) :=
      @esubset (prod_preord (pdom_ord X Upper) (pdom_ord Y Upper))
        (fun z => fmap_upper (fst z) (snd z))
        (fun z => fmap_upper_semidec (fst z) (snd z))
        (eff_enum _ (effective_prod (pdom_effective X (PLT.effective X) Upper)
                                    (pdom_effective Y (PLT.effective Y) Upper))).

    Definition fmap_convex_rel :=
      @esubset (prod_preord (pdom_ord X Convex) (pdom_ord Y Convex))
        (fun z => fmap_convex (fst z) (snd z))
        (fun z => fmap_convex_semidec (fst z) (snd z))
        (eff_enum _ (effective_prod (pdom_effective X (PLT.effective X) Convex)
                                    (pdom_effective Y (PLT.effective Y) Convex))).

    Definition fmap_rel sort :=
      match sort with
      | Lower  => fmap_lower_rel
      | Upper  => fmap_upper_rel
      | Convex => fmap_convex_rel
      end. 

    Definition fmap_spec sort x y :=
      match sort with
      | Lower  => fmap_lower x y
      | Upper  => fmap_upper x y
      | Convex => fmap_convex x y
      end.

Lemma swelling_lemma (A:preord) (HA:effective_order A)
  (M:finset A)
  (INV : finset A -> Prop)
  (P : finset A -> Prop) 

  (HP : forall z, z ⊆ M -> INV z -> 
    P z \/ exists q, q ∈ M /\ q ∉ z /\ INV (q::z)) :

  (exists z0, z0 ⊆ M /\ INV z0) ->
  exists z, z ⊆ M /\ INV z /\ P z.
Proof.
  intros [z [??]].
  assert (exists M0:finset A,
    (forall q, q ∈ M0 <-> q ∈ M /\ q ∉ z)).
  assert (forall q, {q ∉ z}+{~q ∉ z}).
  intros. 
  destruct (finset_in_dec A (OrdDec A (eff_ord_dec A HA)) z q); auto.
  set (M0 := finsubset A (fun q => q ∉ z) X0 M).
  exists M0. intro q.
  unfold M0. rewrite finsubset_elem. split; auto.
  repeat intro. apply H2. rewrite H1; auto.
  destruct H1 as [M0 ?].
  revert z H H0 H1.  

  induction M0 using 
    (well_founded_induction (Wf_nat.well_founded_ltof _ (@length _))); intros.

  destruct (HP z); eauto.
  destruct H3 as [q [?[??]]].
  set (x' := @finset_remove A HA x q).
  apply (H x') with (q::z).
  red; simpl. unfold x'.
  apply finset_remove_length2.
  apply H2. split; auto.
  apply cons_subset; auto.
  auto.
  intros. split; intros.
  apply finset_remove_elem in H6.
  destruct H6.
  apply H2 in H6.
  destruct H6; split; auto.
  intro.
  apply cons_elem in H9. destruct H9.
  apply H7; auto.
  apply H8; auto.
  apply finset_remove_elem.
  destruct H6. split.
  apply H2.
  split; auto.
  intro. apply H7. apply cons_elem; auto.
  intro. apply H7. apply cons_elem; auto.
Qed.

    Lemma fmap_convex_swell 
      (z : powerdomain Convex X)
      (x y: powerdomain Convex Y) :
      fmap_spec Convex z x ->
      fmap_spec Convex z y ->
      exists z0:finset Y,
        (forall b, b ∈ z0 -> exists a, a ∈ elem z /\ (a,b) ∈ PLT.hom_rel f) /\
        (forall a, a ∈ elem z -> exists b, b ∈ z0 /\ (a,b) ∈ PLT.hom_rel f) /\

        (forall c, c ∈ elem x -> exists m, m ∈ z0 /\ c ≤ m) /\
        (forall d, d ∈ elem y -> exists m, m ∈ z0 /\ d ≤ m) /\

        (forall m, m ∈ z0 -> exists c, c ∈ elem x /\ c ≤ m) /\
        (forall m, m ∈ z0 -> exists d, d ∈ elem y /\ d ≤ m).
    Proof.
      intros [??] [??].
      hnf in H, H0, H1, H2.
      
      set (M := mub_closure (PLT.plotkin Y) (elem x ++ elem y)).
      set (INV (z0:finset Y) :=
        (forall b, b ∈ z0 -> exists a, a ∈ elem z /\ (a,b) ∈ PLT.hom_rel f) /\
        (forall a, a ∈ elem z -> exists b, b ∈ z0 /\ (a,b) ∈ PLT.hom_rel f) /\
        (forall m, m ∈ z0 -> exists c, c ∈ elem x /\ c ≤ m) /\
        (forall m, m ∈ z0 -> exists d, d ∈ elem y /\ d ≤ m)).
      set (P (z0:finset Y) :=
        (forall c, c ∈ elem x -> exists m, m ∈ z0 /\ c ≤ m) /\
        (forall d, d ∈ elem y -> exists m, m ∈ z0 /\ d ≤ m)).
      
      destruct (swelling_lemma Y (PLT.effective Y) M INV P)
        as [z0 [?[??]]].
      3: exists z0; hnf in H4, H5; intuition.

      intros. unfold P.
      destruct (finset_find_dec' Y (fun c => exists m, m ∈ z0 /\ c ≤ m)) 
        with (elem x).
      intros. destruct H6 as [m [??]].
      exists m; split; auto. rewrite <- H5; auto.
      intro c.
      destruct (finset_find_dec Y (fun m => c ≤ m)) with z0.
      intros. rewrite <- H5; auto.
      apply (eff_ord_dec _ (PLT.effective Y)).
      destruct s as [s [??]]. left; eauto.
      right; intros [?[??]]. apply (n x0); auto.

      right.
      destruct s as [c [??]].
      destruct (H c) as [a [??]]; auto.
      destruct (H2 a) as [d [??]]; auto.
      destruct (PLT.hom_directed hf X Y f a (c::d::nil)) as [q [??]].
      eapply directed.elem_inh. apply cons_elem; left; auto.
      red; intros.
      apply cons_elem in H11. destruct H11. rewrite H11.
      apply erel_image_elem. auto.
      apply cons_elem in H11. destruct H11. rewrite H11.
      apply erel_image_elem. auto.
      apply nil_elem in H11. elim H11.
      apply erel_image_elem in H12.
      destruct (mub_complete (PLT.plotkin Y) (c::d::nil) q) as [q' [??]].
      eapply directed.elem_inh. apply cons_elem; left; auto.
      auto.
      exists q'. split.
      unfold M.
      apply (mub_clos_mub (PLT.plotkin Y) (elem x ++ elem y) (c::d::nil)).
      eapply directed.elem_inh. apply cons_elem; left; auto.
      apply cons_subset.
      apply mub_clos_incl. apply app_elem; auto.
      apply cons_subset.
      apply mub_clos_incl. apply app_elem; auto.
      apply nil_subset.
      auto.
      split.
      intro.
      elim H6.
      exists q'. split; auto. apply H13.
      apply cons_elem; auto.
      hnf. repeat split; intros.
      apply cons_elem in H15. destruct H15.
      exists a. split; auto.
      apply PLT.hom_order with a q; auto.
      rewrite H15; auto.
      destruct H4 as [?[?[??]]].
      apply H4; auto.
      destruct H4 as [?[?[??]]].
      destruct (H16 a0) as [t [??]]; auto.
      exists t; split; auto.
      apply cons_elem; auto.
      apply cons_elem in H15. destruct H15.
      exists c. split; auto.
      rewrite H15. apply H13. apply cons_elem; auto.
      destruct H4 as [?[?[??]]].
      apply H17; auto.
      apply cons_elem in H15. destruct H15.
      exists d. split; auto.
      rewrite H15. apply H13.
      apply cons_elem; right.
      apply cons_elem; auto.
      destruct H4 as [?[?[??]]].
      apply H18; auto.
      
      destruct (finset_find_dec' Y (fun c => exists m, m ∈ z0 /\ c ≤ m)) 
        with (elem y).
      intros. destruct H6 as [m [??]].
      exists m; split; auto. rewrite <- H5; auto.
      intro c.
      destruct (finset_find_dec Y (fun m => c ≤ m)) with z0.
      intros. rewrite <- H5; auto.
      apply (eff_ord_dec _ (PLT.effective Y)).
      destruct s as [s [??]]. left; eauto.
      right; intros [?[??]]. apply (n x0); auto.
      
      right.
      destruct s as [d [??]].
      destruct (H1 d) as [a [??]]; auto.
      destruct (H0 a) as [c [??]]; auto.
      destruct (PLT.hom_directed hf X Y f a (c::d::nil)) as [q [??]].
      eapply directed.elem_inh. apply cons_elem; left; auto.
      red; intros.
      apply cons_elem in H11. destruct H11. rewrite H11.
      apply erel_image_elem. auto.
      apply cons_elem in H11. destruct H11. rewrite H11.
      apply erel_image_elem. auto.
      apply nil_elem in H11. elim H11.
      apply erel_image_elem in H12.
      destruct (mub_complete (PLT.plotkin Y) (c::d::nil) q) as [q' [??]].
      eapply directed.elem_inh. apply cons_elem; left; auto.
      auto.
      exists q'. split.
      unfold M.
      apply (mub_clos_mub (PLT.plotkin Y) (elem x ++ elem y) (c::d::nil)).
      eapply directed.elem_inh. apply cons_elem; left; auto.
      apply cons_subset.
      apply mub_clos_incl. apply app_elem; auto.
      apply cons_subset.
      apply mub_clos_incl. apply app_elem; auto.
      apply nil_subset.
      auto.
      split.
      intro.
      elim H6.
      exists q'. split; auto. apply H13.
      apply cons_elem; right.
      apply cons_elem; auto.
      hnf. repeat split; intros.
      apply cons_elem in H15. destruct H15.
      exists a. split; auto.
      apply PLT.hom_order with a q; auto.
      rewrite H15; auto.
      destruct H4 as [?[?[??]]].
      apply H4; auto.
      destruct H4 as [?[?[??]]].
      destruct (H16 a0) as [t [??]]; auto.
      exists t; split; auto.
      apply cons_elem; auto.
      apply cons_elem in H15. destruct H15.
      exists c. split; auto.
      rewrite H15. apply H13. apply cons_elem; auto.
      destruct H4 as [?[?[??]]].
      apply H17; auto.
      apply cons_elem in H15. destruct H15.
      exists d. split; auto.
      rewrite H15. apply H13.
      apply cons_elem; right.
      apply cons_elem; auto.
      destruct H4 as [?[?[??]]].
      apply H18; auto.
      left; auto.

      unfold INV.
      revert H0 H2.
      generalize (elem z). clear.
      induction c; intros.
      exists nil.
      intuition; hnf; intros; apply nil_elem in H; elim H.
      destruct IHc as [z0 [?[?[?[?]]]]].
      intros. apply H0. apply cons_elem; auto.
      intros. apply H2. apply cons_elem; auto.
      destruct (H0 a) as [xq [??]]. apply cons_elem; auto.
      destruct (H2 a) as [yq [??]]. apply cons_elem; auto.
      destruct (PLT.hom_directed hf X Y f a (xq::yq::nil)) as [q [??]].
      eapply directed.elem_inh. apply cons_elem; left; auto.
      red; intros.
      apply cons_elem in H10. destruct H10. rewrite H10.
      apply erel_image_elem. auto.
      apply cons_elem in H10. destruct H10. rewrite H10.
      apply erel_image_elem. auto.
      apply nil_elem in H10. elim H10.
      apply erel_image_elem in H11.
      destruct (mub_complete (PLT.plotkin Y) (xq::yq::nil) q) as [q' [??]]; auto.
      eapply directed.elem_inh. apply cons_elem; left; auto.
      assert (q' ∈ M).
      unfold M.
      apply (mub_clos_mub (PLT.plotkin Y) (elem x ++ elem y) (xq::yq::nil)).
      eapply directed.elem_inh. apply cons_elem; left; auto.
      apply cons_subset.
      apply mub_clos_incl. apply app_elem; auto.
      apply cons_subset.
      apply mub_clos_incl. apply app_elem; auto.
      apply nil_subset.
      auto.
      exists (q'::z0). split.
      apply cons_subset; auto.
      split; intros.
      apply cons_elem in H15; destruct H15; auto.
      exists a. split. apply cons_elem; auto.
      apply PLT.hom_order with a q; auto.
      rewrite H15; auto.
      destruct (H1 b) as [t [??]]; auto.
      exists t; split; auto. apply cons_elem; auto.
      split; intros.
      apply cons_elem in H15; destruct H15; auto.
      exists q'. split; auto.
      apply cons_elem; auto.
      apply PLT.hom_order with a q; auto.
      destruct (H3 a0) as [t [??]]; auto.
      exists t; split; auto. apply cons_elem; auto.
      split; intros.
      apply cons_elem in H15. destruct H15.
      exists xq. split; auto.
      rewrite H15. apply H12. apply cons_elem; auto.
      apply H4; auto.
      apply cons_elem in H15. destruct H15.
      exists yq. split; auto.
      rewrite H15. apply H12; auto.
      apply cons_elem; right. apply cons_elem; auto.
      apply H5; auto.
    Qed.


    Lemma fmap_rel_elem sort : forall x y,
      (x,y) ∈ fmap_rel sort <-> fmap_spec sort x y.
    Proof.
      destruct sort; simpl; intros.

      unfold fmap_lower_rel.
      rewrite esubset_elem.
      simpl. intuition.
      apply eprod_elem; split; apply enum_elems_complete.
      unfold fmap_lower. intros.
      destruct H as [[??][??]].
      destruct (H4 b0) as [q [??]]; auto.
      destruct (H0 q) as [q' [??]]; auto.
      destruct (H q') as [q'' [??]]; auto.
      exists q''; split; auto.
      revert H8.
      apply PLT.hom_order; auto.
            
      unfold fmap_upper_rel.
      rewrite esubset_elem.
      simpl. intuition.
      apply eprod_elem; split; apply enum_elems_complete.
      intros. unfold fmap_upper.
      intros.
      destruct H as [[??][??]].
      destruct (H a0) as [a' [??]]; auto.
      hnf in H0.
      destruct (H0 a') as [q [??]]; auto.
      destruct (H4 q) as [q' [??]]; auto.
      exists q'. split. auto.
      revert H8. apply PLT.hom_order; auto.

      unfold fmap_convex_rel.
      rewrite esubset_elem.
      simpl. intuition.
      apply eprod_elem; split; apply enum_elems_complete.
      intros. unfold fmap_convex.
      destruct H0.
      destruct H as [[??][??]].
      split.
      intros. unfold fmap_lower.
      intros.
      destruct H4.
      destruct (H4 b0) as [b' [??]]; auto.
      destruct (H0 b') as [q [??]]; auto.
      destruct H.
      destruct (H q) as [q' [??]]; auto.
      exists q'. split. auto.
      revert H10. apply PLT.hom_order; auto.
      intros. unfold fmap_upper.
      intros.
      destruct H.
      destruct (H6 a0) as [a' [??]]; auto.
      destruct (H1 a') as [q [??]]; auto.
      destruct H4.
      destruct (H11 q) as [q' [??]]; auto.
      exists q'. split. auto.
      revert H10. apply PLT.hom_order; auto.
    Qed.

    Program Definition fmap sort
      : (powerdomain sort X) → (powerdomain sort Y) 
      := PLT.Hom hf (powerdomain sort X) (powerdomain sort Y) 
           (fmap_rel sort) _ _.
    Next Obligation.
      intros.
      rewrite (fmap_rel_elem sort) in H1.
      rewrite (fmap_rel_elem sort).
      unfold fmap_spec in *.
      destruct sort; hnf; simpl; intros.
      hnf in H1.
      destruct (H0 b) as [b' [??]]; auto.
      destruct (H1 b') as [a [??]]; auto.
      destruct (H a) as [a' [??]]; auto.
      exists a'; split; auto.
      revert H6. apply PLT.hom_order; auto.
      destruct (H a) as [a' [??]]; auto.
      destruct (H1 a') as [b [??]]; auto.
      destruct (H0 b) as [b' [??]]; auto.
      exists b'. split; auto.
      revert H6. apply PLT.hom_order; auto.

      destruct H1. split; hnf; simpl; intros.
      destruct H. destruct H0.
      destruct (H0 b) as [b' [??]]; auto.
      destruct (H1 b') as [a [??]]; auto.      
      destruct (H a) as [a' [??]]; auto.
      exists a'. split; auto.
      revert H9. apply PLT.hom_order; auto.

      destruct H.
      destruct (H4 a) as [a' [??]]; auto.
      destruct (H2 a') as [b [??]]; auto.       
      destruct H0.
      destruct (H9 b) as [b' [??]]; auto.
      exists b'. split; auto.
      revert H8. apply PLT.hom_order; auto.
    Qed.
    Next Obligation.
      intros sort z.
      apply prove_directed.

      simpl.
      generalize (refl_equal hf).
      pattern hf at 1 3. case hf; intros; auto.

      assert (exists z0:finset Y,
        (forall y, y ∈ z0 -> exists x, x ∈ elem z /\ (x,y) ∈ PLT.hom_rel f) /\
        (forall x, x ∈ elem z -> exists y, y ∈ z0 /\ (x,y) ∈ PLT.hom_rel f)).

        generalize (elem z).
        induction c.
        exists nil. split; intros.
        apply nil_elem in H0; elim H0.
        apply nil_elem in H0; elim H0.
        destruct IHc as [z0 [??]].
        destruct (PLT.hom_directed hf X Y f a nil) as [b [??]].
        rewrite <- H at 2. red; auto.
        red; intros. apply nil_elem in H2. elim H2.
        apply erel_image_elem in H3.
        exists (b::z0). split; simpl; intros.
        apply cons_elem in H4.
        destruct H4.
        exists a. split; auto.
        apply cons_elem; auto.
        apply member_eq with (a,b); auto. split; split; auto.
        destruct (H0 y) as [?[??]]; auto.
        exists x. split; auto. apply cons_elem; auto.
        apply cons_elem in H4. destruct H4.
        exists b. split.
        apply cons_elem; auto.
        apply member_eq with (a,b); auto. split; split; auto.
        destruct (H1 x) as [?[??]]; auto.
        exists x0. split; auto.
        apply cons_elem; auto.

      destruct sort. simpl.
      assert (inh hf (nil : finset Y)).
      simpl. rewrite <- H at 2. hnf; auto.
      exists (PdomElem _ nil H1).
      apply erel_image_elem.
      rewrite (fmap_rel_elem Lower).
      hnf. simpl; intros. apply nil_elem in H2. elim H2.

      destruct H0 as [z0 [??]].
      assert (inh hf z0).
      rewrite <- H at 2; hnf; auto.
      exists (PdomElem Y z0 H2).
      apply erel_image_elem.
      rewrite (fmap_rel_elem Upper).
      hnf. simpl. auto.
      
      destruct H0 as [z0 [??]].
      assert (inh hf z0).
      rewrite <- H at 2; hnf; auto.
      exists (PdomElem Y z0 H2).
      apply erel_image_elem.
      rewrite (fmap_rel_elem Convex).
      split; auto.
      
      intros.      
      apply erel_image_elem in H.
      apply erel_image_elem in H0.
      rewrite (fmap_rel_elem sort) in H.
      rewrite (fmap_rel_elem sort) in H0.
      
      destruct sort. simpl.
      hnf in H, H0.
      
      exists (union_elem _ x y).
      split. hnf.
      intros. exists x0. split; auto.
      simpl. apply app_elem; auto.
      split. hnf.
      intros. exists x0. split; auto.
      simpl. apply app_elem; auto.
      apply erel_image_elem.
      rewrite (fmap_rel_elem Lower).
      hnf. intros.
      simpl in H1.
      apply app_elem in H1.
      destruct H1.
      apply H. auto.
      apply H0; auto.

      assert (exists z0:finset Y,
        (forall p, p ∈ z0 -> exists q, q ∈ elem x /\ q ≤ p) /\
        (forall p, p ∈ z0 -> exists q, q ∈ elem y /\ q ≤ p) /\
        (forall x, x ∈ elem z -> exists y, y ∈ z0 /\ (x,y) ∈ PLT.hom_rel f)).

        revert H H0. simpl. unfold fmap_upper.
        generalize (elem z). induction c; simpl; intros.
        exists nil. intuition.
        apply nil_elem in H1. elim H1.
        apply nil_elem in H1. elim H1.
        apply nil_elem in H1. elim H1.

        destruct IHc as [z0 [?[??]]].
        intros. apply H. apply cons_elem; auto.
        intros. apply H0. apply cons_elem; auto.

        destruct (H a) as [q1 [??]]. apply cons_elem; auto.
        destruct (H0 a) as [q2 [??]]. apply cons_elem; auto.
        destruct (PLT.hom_directed hf X Y f a (q1::q2::nil)) as [q [??]].
        eapply directed.elem_inh. apply cons_elem; left; auto.
        red; intros.
        apply cons_elem in H8. destruct H8. rewrite H8.
        apply erel_image_elem. auto.
        apply cons_elem in H8. destruct H8. rewrite H8.
        apply erel_image_elem. auto.
        apply nil_elem in H8. elim H8.
        apply erel_image_elem in H9.
        exists (q::z0). intuition.
        apply cons_elem in H10. destruct H10.
        exists q1. split; auto.
        rewrite H10. apply H8.
        apply cons_elem; auto.
        apply H1; auto.
        apply cons_elem in H10. destruct H10.
        exists q2. split; auto. rewrite H10.
        apply H8. apply cons_elem. right. apply cons_elem; auto.
        apply H2; auto.
        apply cons_elem in H10. destruct H10.
        exists q. split; auto.
        apply cons_elem. auto.
        apply member_eq with (a,q); auto.
        split; split; auto.
        destruct (H3 x0) as [b [??]]; auto.
        exists b; split; auto.
        apply cons_elem; auto.

      destruct H1 as [z0 [?[??]]].
      assert (inh hf z0).
        generalize (elem_inh z).
        clear -H3.
        pattern hf at 2 5. case hf; simpl; auto.
        intros [??]. destruct (H3 x) as [q [??]]; eauto.
      exists (PdomElem _ z0 H4).
      split. hnf. simpl; auto.
      split. hnf. simpl; auto.
      apply erel_image_elem.
      rewrite (fmap_rel_elem Upper).
      hnf. simpl; intros.
      apply H3. auto.

      destruct (fmap_convex_swell z x y) as [z0 [?[?[?[?[??]]]]]]; auto.
      assert (inh hf z0).
        generalize (elem_inh z).
        clear -H2.
        pattern hf at 2 5. case hf; simpl; auto.
        intros [??]. destruct (H2 x) as [?[??]]; eauto.

      exists (PdomElem _ z0 H7).
      split.
      split; hnf; simpl; intros; auto.
      split.
      split; hnf; simpl; intros; auto.
      apply erel_image_elem.
      rewrite (fmap_rel_elem Convex).
      split; hnf; simpl; intros; auto.
    Qed.

  End powerdomain_fmap.

  Lemma pdom_fmap_id sort (A:PLT.PLT hf) :
    fmap A A id sort ≈ id.
  Proof.
    split; hnf; intros.
    destruct a.
    simpl. apply ident_elem.
    simpl in H. 
    rewrite (fmap_rel_elem A A id sort) in H.
    destruct sort; simpl in *.
    hnf in H.
    hnf; intros.
    destruct (H x H0) as [q [??]].
    exists q. split; auto.
    simpl in H2. apply ident_elem in H2. auto.
    hnf; intros.
    hnf in H.
    destruct (H y H0) as [q [??]].
    exists q; split; auto.    
    simpl in H2.
    apply ident_elem in H2. auto.

    destruct H.
    split.
    hnf; intros.
    destruct (H x H1) as [q [??]].
    exists q; split; auto.
    simpl in H3. 
    apply ident_elem in H3. auto.
    hnf; intros.
    destruct (H0 y H1) as [q [??]].
    exists q; split; auto.
    simpl in H3. 
    apply ident_elem in H3. auto.

    simpl.
    destruct a.
    apply (fmap_rel_elem A A id sort).
    simpl in H. apply ident_elem in H.
    destruct sort; simpl.
    hnf; intros.
    destruct (H b H0) as [q [??]].
    exists q; split; auto.
    simpl. apply ident_elem; auto.
    hnf; intros.
    destruct (H a H0) as [q [??]].
    exists q; split; auto.
    simpl. apply ident_elem; auto.

    destruct H; split; hnf; intros.
    destruct (H b H1) as [q [??]].
    exists q; split; auto.
    simpl; apply ident_elem; auto.
    destruct (H0 a H1) as [q [??]].
    exists q; split; auto.
    simpl; apply ident_elem; auto.
  Qed.    

  Lemma pdom_fmap_compose sort (A B C:PLT.PLT hf) (f:B → C) (g:A → B) :
    fmap A C (f ∘ g) sort ≈ fmap B C f sort ∘ fmap A B g sort.
  Proof.
    split; hnf; intros; destruct a.
    
    rewrite (fmap_rel_elem A C (f ∘ g) sort) in H.
    apply PLT.compose_hom_rel.
    destruct sort.

    hnf in H.
    assert (exists q:finset B,
      (forall m, m ∈ elem c0 -> exists n, n ∈ q /\ (n,m) ∈ PLT.hom_rel f) /\
      (forall n, n ∈ q -> exists o, o ∈ elem c /\ (o,n) ∈ PLT.hom_rel g)).

    revert H. generalize (elem c0). induction c1; intros.
    exists nil; intuition.
    apply nil_elem in H0. elim H0.
    apply nil_elem in H0. elim H0.
    destruct IHc1 as [q [??]].
    intros. apply H. apply cons_elem; auto.
    destruct (H a) as [b [??]].
    apply cons_elem; auto.
    apply PLT.compose_hom_rel in H3. destruct H3 as [b' [??]].
    exists (b'::q). intuition.
    apply cons_elem in H5. destruct H5.
    exists b'. split; auto.
    apply cons_elem; auto.
    revert H4. apply PLT.hom_order; auto.
    destruct (H0 m) as [n [??]]; auto.
    exists n; split; auto.
    apply cons_elem; auto.
    apply cons_elem in H5. destruct H5.
    exists b. split; auto.
    revert H3; apply PLT.hom_order; auto.
    apply H1; auto.
    destruct H0 as [q [??]].
    assert (inh hf q).
    generalize (elem_inh c0).
    clear -H0.
    pattern hf at 2 5. case hf; simpl; auto.
    intros [??].
    destruct (H0 x) as [?[??]]; eauto.
    exists (PdomElem _ q H2).
    split; simpl.
    rewrite (fmap_rel_elem A B g Lower).
    hnf. simpl; auto.
    rewrite (fmap_rel_elem B C f Lower).
    hnf. simpl; auto.

    hnf in H.
    assert (exists q:finset B,
      (forall m, m ∈ elem c -> exists n, n ∈ q /\ (m,n) ∈ PLT.hom_rel g) /\
      (forall n, n ∈ q -> exists o, o ∈ elem c0 /\ (n,o) ∈ PLT.hom_rel f)).

      revert H. generalize (elem c). induction c1; intros.
      exists nil; intuition.
      apply nil_elem in H0. elim H0.
      apply nil_elem in H0. elim H0.
      destruct IHc1 as [q [??]].
      intros. apply H. apply cons_elem; auto.
      destruct (H a) as [b [??]].
      apply cons_elem; auto.
      apply PLT.compose_hom_rel in H3. destruct H3 as [b' [??]].
      exists (b'::q). intuition.
      apply cons_elem in H5. destruct H5.
      exists b'. split; auto.
      apply cons_elem; auto.
      revert H3. apply PLT.hom_order; auto.
      destruct (H0 m) as [n [??]]; auto.
      exists n; split; auto.
      apply cons_elem; auto.
      apply cons_elem in H5. destruct H5.
      exists b. split; auto.
      revert H4; apply PLT.hom_order; auto.
      apply H1; auto.

    destruct H0 as [q [??]].
    assert (inh hf q).
    generalize (elem_inh c).
    clear -H0.
    pattern hf at 2 5. case hf; simpl; auto.
    intros [??].
    destruct (H0 x) as [?[??]]; eauto.
    exists (PdomElem _ q H2).
    split; simpl.
    rewrite (fmap_rel_elem A B g Upper).
    hnf. simpl; auto.
    rewrite (fmap_rel_elem B C f Upper).
    hnf. simpl; auto.

    rename c into a.
    rename c0 into c.
    destruct H. hnf in H. hnf in H0.

    assert (exists q1:finset B,
      (forall x, x ∈ elem a -> exists y, y ∈ q1 /\ (x,y) ∈ PLT.hom_rel g) /\
      (forall y, y ∈ q1 -> exists x, x ∈ elem a /\ (x,y) ∈ PLT.hom_rel g) /\
      (forall y, y ∈ q1 -> exists z, z ∈ elem c /\ (y,z) ∈ PLT.hom_rel f)).
    revert H0. generalize (elem a). induction c0; intros.
    exists nil. repeat split; intros.
    apply nil_elem in H1. elim H1.
    apply nil_elem in H1. elim H1.
    apply nil_elem in H1. elim H1.
    destruct IHc0 as [q1 [??]].
    intros. apply H0. apply cons_elem; auto.
    destruct (H0 a0) as [y [??]]; auto.
    apply cons_elem; auto.
    apply PLT.compose_hom_rel in H4.
    destruct H4 as [m [??]]; auto.
    exists (m::q1). split; intros.
    apply cons_elem in H6. destruct H6.
    exists m; split; auto. apply cons_elem; auto.
    apply PLT.hom_order with a0 m; auto.
    destruct (H1 x) as [t [??]]; auto.
    exists t; split; auto. apply cons_elem; auto.
    split; intros.
    apply cons_elem in H6. destruct H6.
    exists a0. split. apply cons_elem; auto.
    apply PLT.hom_order with a0 m; auto.
    destruct H2. destruct (H2 y0) as [t [??]]; auto.
    exists t; split; auto. apply cons_elem; auto.
    apply cons_elem in H6. destruct H6.
    exists y. split; auto.
    apply PLT.hom_order with m y; auto.
    apply H2; auto.
    destruct H1 as [q1 [??]].
    
    assert (exists q2:finset B,
      (forall z, z ∈ elem c -> exists y, y ∈ q2 /\ (y,z) ∈ PLT.hom_rel f) /\
      (forall y, y ∈ q2 -> exists z, z ∈ elem c /\ (y,z) ∈ PLT.hom_rel f) /\

      (forall y, y ∈ q2 -> exists x, x ∈ elem a /\ (x,y) ∈ PLT.hom_rel g)).

    revert H. generalize (elem c). induction c0; intros.
    exists nil; repeat split; intros. 
    apply nil_elem in H3. elim H3.
    apply nil_elem in H3. elim H3.
    apply nil_elem in H3. elim H3.

    destruct IHc0 as [q2 [??]]. intros. apply H. apply cons_elem; auto.
    rename a0 into z.
    destruct (H z) as [x [??]]. apply cons_elem; auto.
    apply PLT.compose_hom_rel in H6. destruct H6 as [y [??]].
    exists (y::q2).
    split; intros.
    apply cons_elem in H8. destruct H8.
    exists y. split. apply cons_elem; auto.
    apply PLT.hom_order with y z; auto.
    destruct (H3 z0) as [t [??]]; auto.
    exists t; split; auto.
    apply cons_elem; auto.
    split; intros.
    apply cons_elem in H8. destruct H8.
    exists z. split; auto.
    apply cons_elem; auto.
    apply PLT.hom_order with y z; auto.
    destruct H4.
    destruct (H4 y0) as [t [??]]; auto.
    exists t. split; auto. apply cons_elem; auto.
    apply cons_elem in H8. destruct H8.
    exists x; split; auto.
    apply PLT.hom_order with x y; auto.
    apply H4; auto.
    destruct H3 as [q2 [??]].
    clear H H0.
    destruct H2. destruct H4.
    
    set (INV (b:finset B) :=
      (forall y, y ∈ b -> exists x, x ∈ elem a /\ (x,y) ∈ PLT.hom_rel g) /\
      (forall y, y ∈ b -> exists z, z ∈ elem c /\ (y,z) ∈ PLT.hom_rel f) /\
      (forall x, x ∈ elem a -> exists y, y ∈ b /\ (x,y) ∈ PLT.hom_rel g)).
    set (P (b:finset B) :=
      (forall y, y ∈ q2 -> exists y', y' ∈ b /\ y ≤ y')).
    set (M := mub_closure (PLT.plotkin B) (q1 ++ q2)).

    destruct (swelling_lemma B (PLT.effective B) M INV P) as [z0 [?[??]]].
    
    intros. unfold P.
    destruct (finset_find_dec' B (fun y => exists y', y' ∈ z /\ y ≤ y')) 
      with q2; auto.
    intros. destruct H8 as [t [??]]. exists t; split; auto.
    rewrite <- H7. auto.
    intro. destruct (finset_find_dec B (fun y' => x ≤ y')) with z; auto.
    intros. rewrite <- H7; auto.
    intro. apply eff_ord_dec. apply PLT.effective.
    destruct s as [?[??]]; left; eauto.
    right; intros [?[??]]. apply (n x0); auto.
    destruct s as [m [??]]. right.
    destruct (H4 m) as [x [??]]; auto.
    destruct (H1 x) as [n [??]]; auto.
    destruct (PLT.hom_directed hf A B g x (m::n::nil)) as [q [??]].
    eapply directed.elem_inh; apply cons_elem; left; auto.
    red; intros.
    apply cons_elem in H13. destruct H13. rewrite H13.
    apply erel_image_elem; auto.
    apply cons_elem in H13. destruct H13. rewrite H13.
    apply erel_image_elem; auto.
    apply nil_elem in H13; elim H13.
    apply erel_image_elem in H14.
    destruct (mub_complete (PLT.plotkin B) (m::n::nil) q) as [q' [??]]; auto.
    eapply directed.elem_inh; apply cons_elem; left; auto.
    exists q'. split.
    unfold M.
    apply (mub_clos_mub (PLT.plotkin B) (q1 ++ q2) (m::n::nil)).
    eapply directed.elem_inh; apply cons_elem; left; auto.
    apply cons_subset.
    apply mub_clos_incl. apply app_elem. auto.
    apply cons_subset.
    apply mub_clos_incl. apply app_elem. auto.
    apply nil_subset.
    auto.
    split. intro.
    apply H8. exists q'. split; auto.
    apply H15. apply cons_elem; auto.
    split; intros.
    apply cons_elem in H17.
    destruct H17.
    exists x. split; auto.
    apply PLT.hom_order with x q; auto.
    rewrite H17. auto.
    destruct H6 as [?[??]].
    apply H6; auto.
    split; intros.
    apply cons_elem in H17. destruct H17.
    destruct (H2 m) as [t [??]]; auto.
    exists t; split; auto.
    apply PLT.hom_order with m t; auto.
    rewrite H17. apply H15. apply cons_elem; auto.
    destruct H6 as [?[??]].
    apply H18; auto.
    destruct H6 as [?[??]].
    destruct (H19 x0) as [t [??]]; auto.
    exists t; split; auto.
    apply cons_elem; auto.

    exists q1.
    split. hnf.
    intros. unfold M.
    apply mub_clos_incl. apply app_elem; auto.
    hnf; split; intros.
    destruct (H y); auto.
    split; intros.
    apply H0; auto. apply H1; auto.
    
    subst INV P.
    destruct H6 as [?[??]]. simpl in *.

    assert (Hinh : inh hf z0).
      generalize (elem_inh a).
      clear -H9.
      pattern hf at 2 5. case hf; simpl; auto.
      intros [??]. destruct (H9 x) as [?[??]]; eauto.
      
    exists (PdomElem B z0 Hinh).
    split; simpl.
    rewrite (fmap_rel_elem A B g Convex).
    split; hnf; simpl; intros; auto.
    rewrite (fmap_rel_elem B C f Convex).
    split; hnf; simpl; intros; auto.
    destruct (H3 b) as [q [??]]; auto.
    destruct (H7 q) as [q' [??]]; auto.
    exists q'. split; auto.
    apply PLT.hom_order with q b; auto.

    apply PLT.compose_hom_rel in H.
    destruct H as [y [??]].
    rewrite (fmap_rel_elem A C (f ∘ g) sort).
    rewrite (fmap_rel_elem A B g sort) in H.
    rewrite (fmap_rel_elem B C f sort) in H0.

    destruct sort.
    hnf; intros.
    destruct (H0 b) as [q [??]]; auto.
    destruct (H q) as [q' [??]]; auto.
    exists q'; split; auto.
    apply PLT.compose_hom_rel. eauto.

    hnf; intros.
    destruct (H a) as [q [??]]; auto.
    destruct (H0 q) as [q' [??]]; auto.
    exists q'; split; auto.
    apply PLT.compose_hom_rel. eauto.

    destruct H; destruct H0.
    split; hnf; intros.
    destruct (H0 b) as [q [??]]; auto.
    destruct (H q) as [q' [??]]; auto.
    exists q'. split; auto.
    apply PLT.compose_hom_rel. exists q; split; auto.
    destruct (H1 a) as [q [??]]; auto.
    destruct (H2 q) as [q' [??]]; auto.
    exists q'. split; auto.
    apply PLT.compose_hom_rel. exists q; split; auto.
  Qed.

  Lemma fmap_monotone sort X Y f f' :
    f ≤ f' -> fmap X Y f sort ≤ fmap X Y f' sort.
  Proof.
    intros. hnf; simpl; intros. destruct a as [x y].
    rewrite (fmap_rel_elem X Y f sort) in H0.
    rewrite (fmap_rel_elem X Y f' sort).
    destruct sort; simpl in *.
    hnf; intros.
    destruct (H0 b) as [q [??]]; eauto.
    hnf; intros.
    destruct (H0 a) as [q [??]]; eauto.
    destruct H0.
    split; hnf; intros.
    destruct (H0 b) as [q [??]]; eauto.
    destruct (H1 a) as [q [??]]; eauto.
  Qed.

  Lemma fmap_respects sort X Y f f' :
    f ≈ f' -> fmap X Y f sort ≈ fmap X Y f' sort.
  Proof.
    intros. split; apply fmap_monotone; auto.
  Qed.

  Program Definition pdomain sort : functor (PLT.PLT hf) (PLT.PLT hf) :=
    Functor _ _ (powerdomain sort) (fun X Y f => fmap X Y f sort) _ _ _.
  Next Obligation.
    intros.
    transitivity (fmap A A id sort).
    apply fmap_respects; auto.
    apply pdom_fmap_id.    
  Qed.
  Next Obligation.
    intros.
    transitivity (fmap A C (f ∘ g) sort).
    apply fmap_respects; auto.
    apply pdom_fmap_compose.
  Qed.
  Next Obligation.
    intros.
    apply fmap_respects; auto.
  Qed.

  Definition single_rel sort (X:PLT.PLT hf) : erel X (powerdomain sort X) :=
    esubset_dec _
      (fun xp => (single_elem X (fst xp) : pdom_ord X sort) ≥ snd xp)
      (fun x => pdom_ord_dec X (PLT.effective X) sort (snd x) (single_elem X (fst x)))
      (eprod (eff_enum _ (PLT.effective X)) (enum_elems X (PLT.effective X) sort)).

  Lemma single_rel_elem sort (X:PLT.PLT hf) x (p:pdom_ord X sort) :
    (x,p) ∈ single_rel sort X <-> p ≤ single_elem X x.
  Proof.
    unfold single_rel. rewrite esubset_dec_elem. simpl.
    rewrite eprod_elem. intuition.
    apply eff_complete. apply enum_elems_complete.
    intros. destruct H as [[??][??]]; auto.
    rewrite H3; auto.
    rewrite H0.
    apply pdom_elem_eq_le. simpl.
    assert (fst x0 ≈ fst y).
    split; auto.
    split; hnf; simpl; intros.
    apply cons_elem in H5. apply cons_elem.
    rewrite <- H4; auto.
    apply cons_elem in H5. apply cons_elem.
    rewrite H4; auto.
  Qed.

  Lemma single_elem_mono sort (X:preord) (x x':X) :
    x ≤ x' -> (single_elem X x:pdom_ord X sort) ≤ single_elem X x'.
  Proof.
    intro.
    destruct sort; hnf; simpl; intros.
    apply cons_elem in H0. destruct H0.
    exists x'. split; auto. apply cons_elem; auto. rewrite H0; auto.
    apply nil_elem in H0. elim H0.
    apply cons_elem in H0. destruct H0.
    exists x. split; auto. apply cons_elem. auto.
    rewrite H0; auto. apply nil_elem in H0; elim H0.
    split; hnf; simpl; intros.
    apply cons_elem in H0. destruct H0.
    exists x'. split; auto. apply cons_elem; auto. rewrite H0; auto.
    apply nil_elem in H0. elim H0.
    apply cons_elem in H0. destruct H0.
    exists x. split; auto. apply cons_elem. auto.
    rewrite H0; auto. apply nil_elem in H0; elim H0.
  Qed.    

  Program Definition single sort X : X → powerdomain sort X :=
    PLT.Hom hf X (powerdomain sort X) (single_rel sort X) _ _.
  Next Obligation.
    intros.
    apply (single_rel_elem sort X) in H1.
    apply (single_rel_elem sort X).
    rewrite H0. rewrite H1.
    apply single_elem_mono. auto.
  Qed.
  Next Obligation.
    repeat intro.
    exists (single_elem X x).
    split. repeat intro.
    apply H in H0.
    apply erel_image_elem in H0.
    apply (single_rel_elem sort X) in H0.
    auto.
    apply erel_image_elem.
    apply (single_rel_elem sort X). auto.
  Qed.

  Definition union_rel sort (X:PLT.PLT hf)
    : erel (PLT.prod (powerdomain sort X) (powerdomain sort X)) (powerdomain sort X)
    := esubset_dec 
         (PLT.prod (PLT.prod (powerdomain sort X) (powerdomain sort X)) (powerdomain sort X))
         (fun xyz => snd xyz ≤ union_elem X (fst (fst xyz)) (snd (fst xyz)))
         (fun xyz => pdom_ord_dec X (PLT.effective X) sort _ _)
         (eprod (eprod (enum_elems _ (PLT.effective X) sort)
                       (enum_elems _ (PLT.effective X) sort))
                (enum_elems _ (PLT.effective X) sort)).

  Lemma union_elem_lower_ord X (x x' y y':pdom_elem X) :
    lower_ord X x x' -> lower_ord X y y' ->
    lower_ord X (union_elem X x y) (union_elem X x' y').
  Proof.
    unfold lower_ord; simpl; intros.
    apply app_elem in H1. destruct H1.
    destruct (H x0) as [q [??]];auto.
    exists q. split; auto. apply app_elem; auto.
    destruct (H0 x0) as [q [??]];auto.
    exists q. split; auto. apply app_elem; auto.
  Qed.

  Lemma union_elem_upper_ord X (x x' y y':pdom_elem X) :
    upper_ord X x x' -> upper_ord X y y' ->
    upper_ord X (union_elem X x y) (union_elem X x' y').
  Proof.
    unfold upper_ord; simpl; intros.
    apply app_elem in H1. destruct H1.
    destruct (H y0) as [q [??]]; auto.
    exists q; split; auto. apply app_elem; auto.
    destruct (H0 y0) as [q [??]]; auto.
    exists q; split; auto. apply app_elem; auto.
  Qed.    

  Lemma union_elem_convex_ord X (x x' y y':pdom_elem X) :
    convex_ord X x x' -> convex_ord X y y' ->
    convex_ord X (union_elem X x y) (union_elem X x' y').
  Proof.
    unfold convex_ord; intuition.
    apply union_elem_lower_ord; auto.
    apply union_elem_upper_ord; auto.
  Qed.

  Lemma union_elem_pdom_ord sort X (x x' y y':pdom_ord X sort) :
    x ≤ x' -> y ≤ y' -> 
    (union_elem X x y : pdom_ord X sort) ≤  union_elem X x' y'.
  Proof.
    destruct sort; simpl.
    apply union_elem_lower_ord; auto.
    apply union_elem_upper_ord; auto.
    apply union_elem_convex_ord; auto.
  Qed.

  Lemma union_rel_elem sort X x y z :
    ((x,y),z) ∈ union_rel sort X <-> union_elem X x y ≥ z.
  Proof.
    unfold union_rel. rewrite esubset_dec_elem. simpl. intuition.
    apply (eprod_elem _ _ _ _ (x,y) z). split.
    apply eprod_elem. split.
    apply enum_elems_complete.    
    apply enum_elems_complete.
    apply enum_elems_complete.
    simpl; intros.
    etransitivity.
    etransitivity. 2: apply H0.
    destruct H as [[??][??]]; auto.
    destruct H as [[??][??]].
    destruct H. destruct H2.
    apply (union_elem_pdom_ord sort X); auto.
  Qed.

  Program Definition union sort X :
    (PLT.prod (powerdomain sort X) (powerdomain sort X)) → powerdomain sort X :=
    PLT.Hom _ _ _ (union_rel sort X) _ _.
  Next Obligation.
    intros. 
    destruct x. destruct x'.
    apply (union_rel_elem sort X c c0 y) in H1.
    apply union_rel_elem.
    rewrite H0. rewrite H1.
    destruct H.
    apply (union_elem_pdom_ord sort X); auto.
  Qed.
  Next Obligation.
    repeat intro.
    destruct x as [a b].
    exists (union_elem X a b).
    split.
    repeat intro.
    apply H in H0.
    apply erel_image_elem in H0.
    apply (union_rel_elem _ _ a b x) in H0.
    auto.
    apply erel_image_elem.
    apply (union_rel_elem sort X). auto.
  Qed.

  Definition join_rel sort X : erel (powerdomain sort (powerdomain sort X))
                                    (powerdomain sort X)
    := esubset_dec 
         (PLT.prod (powerdomain sort (powerdomain sort X)) (powerdomain sort X))
         (fun xy => snd xy ≤ concat_elem sort X (elem (fst xy)) (elem_inh (fst xy)))
         (fun xy => pdom_ord_dec X (PLT.effective X) sort _ _)
         (eprod (enum_elems _ (PLT.effective (powerdomain sort X)) sort)
                (enum_elems _ (PLT.effective X) sort)).


  (* FIXME move this *)
  Lemma concat_in (A:Type) (xs:list (list A)) : 
    forall x, In x (concat A xs) <->
      exists q, In q xs /\ In x q.
  Proof.
    induction xs; simpl; intuition.
    destruct H as [?[??]]; auto.
    apply in_app_or in H. destruct H.
    exists a. split; auto.
    apply IHxs in H.
    destruct H as [q [??]]; eauto.
    apply in_or_app.
    destruct H as [q [??]]. destruct H.
    subst q. auto.
    right. apply IHxs. eauto.
  Qed.

  Lemma concat_elem_mono sort X (a b:powerdomain sort (powerdomain sort X)) :
    a ≤ b ->
    (concat_elem sort X (elem a) (elem_inh a) : powerdomain sort X) ≤
    concat_elem sort X (elem b) (elem_inh b).
  Proof.
    intro. destruct sort.

    simpl. unfold concat_elem. hnf.
    repeat intro. simpl in *.
    assert (exists z,
      x ∈ z /\ In z (map (elem (X:=X)) (elem a))).
      destruct H0 as [x' [??]].
      apply concat_in in H0.
      destruct H0 as [q [??]].
      exists q. split; auto.
      exists x'. split; auto.

    destruct H1 as [z [??]].
    hnf in H.
    apply in_map_iff in H2.
    destruct H2 as [q [??]].
    subst z.
    destruct (H q) as [q' [??]].
    exists q. split; auto.
    destruct H2 as [q'' [??]].
    assert ((q:powerdomain Lower X) ≤ q'').
    rewrite H4; auto.
    hnf in H6.
    destruct (H6 x) as [y [??]]; auto.
    exists y. split; auto.
    destruct H7 as [y' [??]].
    exists y'. split; auto.
    apply concat_in.
    exists (elem q'').
    split; auto.
    apply in_map. auto.

    repeat intro. simpl in *.
    assert (exists z,
      y ∈ z /\ In z (map (elem (X:=X)) (elem b))).
      destruct H0 as [y' [??]].
      apply concat_in in H0.
      destruct H0 as [q [??]].
      exists q. split; auto.
      exists y'. split; auto.

    destruct H1 as [z [??]].
    hnf in H.
    apply in_map_iff in H2.
    destruct H2 as [q [??]].
    subst z.
    destruct (H q) as [q' [??]].
    exists q. split; auto.
    destruct H2 as [q'' [??]].
    assert ((q'':powerdomain Upper X) ≤ q).
    rewrite <- H4; auto.
    hnf in H6.
    destruct (H6 y) as [x [??]]; auto.
    exists x. split; auto.
    destruct H7 as [x' [??]].
    exists x'. split; auto.
    apply concat_in.
    exists (elem q'').
    split; auto.
    apply in_map. auto.

    split.
    destruct H as [? _].
    simpl. unfold concat_elem. hnf.
    repeat intro. simpl in *.
    assert (exists z,
      x ∈ z /\ In z (map (elem (X:=X)) (elem a))).
      destruct H0 as [x' [??]].
      apply concat_in in H0.
      destruct H0 as [q [??]].
      exists q. split; auto.
      exists x'. split; auto.

    destruct H1 as [z [??]].
    hnf in H.
    apply in_map_iff in H2.
    destruct H2 as [q [??]].
    subst z.
    destruct (H q) as [q' [??]].
    exists q. split; auto.
    destruct H2 as [q'' [??]].
    assert ((q:powerdomain Convex X) ≤ q'').
    rewrite H4; auto.
    destruct H6.
    destruct (H6 x) as [y [??]]; auto.
    exists y. split; auto.
    destruct H8 as [y' [??]].
    exists y'. split; auto.
    apply concat_in.
    exists (elem q'').
    split; auto.
    apply in_map. auto.

    destruct H as [_ ?].
    repeat intro. simpl in *.
    assert (exists z,
      y ∈ z /\ In z (map (elem (X:=X)) (elem b))).
      destruct H0 as [y' [??]].
      apply concat_in in H0.
      destruct H0 as [q [??]].
      exists q. split; auto.
      exists y'. split; auto.

    destruct H1 as [z [??]].
    hnf in H.
    apply in_map_iff in H2.
    destruct H2 as [q [??]].
    subst z.
    destruct (H q) as [q' [??]].
    exists q. split; auto.
    destruct H2 as [q'' [??]].
    assert ((q'':powerdomain Convex X) ≤ q).
    rewrite <- H4; auto.
    destruct H6.
    destruct (H7 y) as [x [??]]; auto.
    exists x. split; auto.
    destruct H8 as [x' [??]].
    exists x'. split; auto.
    apply concat_in.
    exists (elem q'').
    split; auto.
    apply in_map. auto.
  Qed.

  Lemma join_rel_elem sort X m n :
    (m,n) ∈ join_rel sort X <-> n ≤ concat_elem sort X (elem m) (elem_inh m).
  Proof.
    unfold join_rel.
    rewrite esubset_dec_elem.
    intuition.
    apply eprod_elem. split.
    apply enum_elems_complete.
    apply enum_elems_complete.

    intros. destruct H as [[??][??]].
    rewrite <- H3 in H0.
    rewrite H0.
    apply concat_elem_mono. auto.
  Qed.

  Program Definition join sort X : 
    powerdomain sort (powerdomain sort X) → powerdomain sort X :=
    PLT.Hom hf _ _ (join_rel sort X) _ _.
  Next Obligation.
    intros.
    rewrite join_rel_elem in H1.
    rewrite join_rel_elem.
    rewrite H0. rewrite H1.
    apply concat_elem_mono. auto.
  Qed.
  Next Obligation.
    repeat intro.
    exists (concat_elem sort X (elem x) (elem_inh x)).
    split.
    red; intros.
    generalize H0; intros.
    apply H in H0. apply erel_image_elem in H0.
    apply join_rel_elem in H0. auto.
    apply erel_image_elem.
    apply join_rel_elem. auto.
  Qed.

  Lemma single_natural sort (X Y:PLT.PLT hf) (f:X → Y) :
    pdomain sort·f ∘ single sort X ≈ single sort Y ∘ f.
  Proof.
    simpl.
    split; intros [x y] ?.
    apply PLT.compose_hom_rel in H.
    destruct H as [x' [??]].
    simpl in H.
    rewrite (single_rel_elem sort X) in H.
    apply PLT.compose_hom_rel.
    rewrite (fmap_rel_elem X Y f sort) in H0.

    destruct sort.

    hnf in H0.
    hnf in H.
    destruct (PLT.hom_directed hf X Y f x (elem y)) as [q [??]].
    apply elem_inh.
    red; intros. apply erel_image_elem.
    destruct (H0 a) as [q [??]]; auto.
    destruct (H q) as [q' [??]]; auto.
    simpl in H4. apply cons_elem in H4.
    destruct H4. 2: apply nil_elem in H4; elim H4.
    apply PLT.hom_order with q a; auto.
    rewrite H5; auto.
    apply erel_image_elem in H2.
    exists q. split; auto.
    simpl. apply single_rel_elem.
    hnf; intros.
    simpl.
    exists q. split.
    apply cons_elem; auto.
    apply H1. auto.

    hnf in H0.
    destruct (H x) as [q [??]]; simpl.
    apply cons_elem; auto.
    destruct (H0 q) as [q' [??]]; auto.
    exists q'. split.
    apply PLT.hom_order with q q'; auto.
    apply single_rel_elem.
    hnf; intros.
    simpl in H5.
    apply cons_elem in H5.
    destruct H5. exists q'. split; auto.
    apply nil_elem in H5. elim H5.

    destruct H. destruct H0.
    hnf in H, H0, H1, H2.
    simpl in *.
    destruct (H1 x) as [q [??]]. apply cons_elem; auto. clear H1.
    assert (forall t, t ∈ elem x' -> t ≤ x).   
    intros.
    destruct (H t) as [t' [??]]; auto.
    apply cons_elem in H5. destruct H5.
    2: apply nil_elem in H5; elim H5.
    rewrite H6; auto. clear H.
    destruct (PLT.hom_directed hf X Y f x (elem y)) as [r [??]].
    apply elem_inh.
    red; intros. apply erel_image_elem.
    destruct (H0 a) as [p [??]]; auto.
    apply PLT.hom_order with p a; auto.
    apply erel_image_elem in H5.
    exists r. split; auto.
    rewrite (single_rel_elem Convex Y).
    split; hnf; intros.
    simpl.
    exists r. split.
    apply cons_elem; auto. apply H. auto.
    simpl in H6. apply cons_elem in H6.
    destruct H6. 2: apply nil_elem in H6; elim H6.
    destruct (H2 q) as [q' [??]]; auto.
    exists q'. split; auto.
    rewrite H6. apply H. auto.
    
    apply PLT.compose_hom_rel in H.    
    apply PLT.compose_hom_rel.
    destruct H as [y' [??]].
    simpl in H0.
    apply (single_rel_elem sort Y) in H0.
    exists (single_elem X x).
    split. simpl.
    apply (single_rel_elem sort X). auto.
    simpl.
    rewrite (fmap_rel_elem X Y f sort).
    destruct sort; simpl.

    hnf in H0. repeat intro.
    destruct (H0 b) as [q [??]]; auto.
    simpl.
    simpl in H2. apply cons_elem in H2.
    destruct H2. 2: apply nil_elem in H2; elim H2.
    exists x. split. apply cons_elem; auto.
    apply PLT.hom_order with x y'; auto.
    rewrite H3; auto.

    hnf in H0; repeat intro.
    simpl in H1.
    apply cons_elem in H1. destruct H1.
    2: apply nil_elem in H1; elim H1.    
    simpl in H0.
    destruct (H0 y') as [q [??]].
    apply cons_elem; auto.
    exists q. split; auto.
    apply PLT.hom_order with x y'; auto.

    destruct H0. hnf in H0, H1.
    destruct (H1 y') as [t [??]]; auto.
    simpl. apply cons_elem; auto. clear H1.
    assert (forall x, x ∈ elem y -> x ≤ y').
    intros. destruct (H0 x0) as [q [??]]; auto.
    simpl in H4.
    apply cons_elem in H4. destruct H4.
    rewrite <- H4; auto.
    apply nil_elem in H4; elim H4.
    clear H0.
    split; hnf; simpl; intros.
    exists x; split; auto.
    apply cons_elem; auto.
    apply PLT.hom_order with x y'; auto.
    apply cons_elem in H0.
    destruct H0. 2: apply nil_elem in H0; elim H0.
    exists t. split; auto.
    apply PLT.hom_order with x y'; auto.    
  Qed.

  Program Definition singleNT sort : nt id(PLT.PLT hf) (pdomain sort) 
    := NT (id) (pdomain sort) (single sort) _.
  Next Obligation.
    simpl; intros. symmetry. apply single_natural.
  Qed.


  Lemma join_natural sort (X Y:PLT.PLT hf) (f:X → Y) :
    pdomain sort·f ∘ join sort X ≈ join sort Y ∘ pdomain sort·pdomain sort·f.
  Proof.
    split; intros [x y] ?.    
    apply PLT.compose_hom_rel in H.
    apply PLT.compose_hom_rel.
    destruct H as [q [??]].
    simpl in H.
    apply join_rel_elem in H.

    assert ((concat_elem sort X (elem x) (elem_inh x) : pdomain sort X, y) ∈
      PLT.hom_rel (pdomain sort·f)).
    apply PLT.hom_order with q y; auto.
    clear q H H0.

    simpl in H1.
    apply (fmap_rel_elem X Y f sort) in H1.
    
    set (ys := map (single_elem Y) (elem y) : finset (pdomain sort Y)).
    assert (inh hf ys).
      generalize (elem_inh y).
      pattern hf at 2 7. case hf; simpl; auto.
      intros [??]. destruct H as [?[??]].
      exists (single_elem Y x1).
      unfold ys.
      exists (single_elem Y x1). split; auto.
      apply in_map. auto.

    destruct sort.

    exists (PdomElem (pdomain Lower Y) ys H).
    simpl.
    rewrite (fmap_rel_elem (pdomain Lower X) (pdomain Lower Y) (fmap X Y f Lower) Lower).
    simpl.

    split.
    hnf; simpl; intros.
    unfold ys in H0.
    destruct H0 as [b' [??]].
    rewrite in_map_iff in H0.
    destruct H0 as [b'' [??]]. subst b'.
    hnf in H1.
    destruct (H1 b'') as [q [??]].
    exists b''; split; auto.
    simpl in H0.
    destruct H0 as [q' [??]].
    apply concat_in in H0.
    destruct H0 as [q'' [??]].
    apply in_map_iff in H0.
    destruct H0 as [q''' [??]]. subst q''.
    exists q'''. split.
    exists q'''; auto.    
    simpl.
    rewrite (fmap_rel_elem X Y f Lower).
    hnf; intros.
    destruct H2.
    destruct (H2 b0) as [c [??]]; auto.
    simpl in H9.
    apply cons_elem in H9.
    destruct H9. 2: apply nil_elem in H9; elim H9.
    rewrite H9 in H10.
    exists q. split; auto.
    exists q'; split; auto.
    apply PLT.hom_order with q b''; auto.

    simpl. apply join_rel_elem.
    simpl.
    hnf; intros.
    destruct H0 as [x' [??]].    
    exists x0. split; auto.
    exists x'; split; auto.
    simpl.
    apply concat_in.
    exists (x'::nil).
    split; simpl; auto.
    unfold ys.
    rewrite map_map. simpl.
    apply in_map_iff.
    exists x'. split; auto.

    assert (forall a, a ∈ elem x -> exists z:finset Y,   
      (forall a, a ∈ z ->
        exists q, q ∈ elem y /\ q ≤ a) /\
      (forall t, t ∈ elem a ->
        exists q, q ∈ z /\ q ∈ elem y /\ (t,q) ∈ PLT.hom_rel f)).
    intros.
    cut (forall t, t ∈ elem a -> exists b, b ∈ elem y /\ (t,b) ∈ PLT.hom_rel f).
      generalize (elem a). induction c; intros.
      exists nil. split; intros. 
      apply nil_elem in H3. elim H3.
      apply nil_elem in H3. elim H3.
      
      destruct IHc as [z ?]; auto.
      intros. apply H2. apply cons_elem; auto.
      destruct (H2 a0) as [q [??]]. apply cons_elem; auto.
      exists (q::z).
      split.
      intros. apply cons_elem in H6. destruct H6.
      exists q. split; auto.
      destruct H3. apply H3; auto.

      intros. apply cons_elem in H6. destruct H6.
      exists q. split; auto.
      apply cons_elem; auto.
      split; auto. apply PLT.hom_order with a0 q; auto.
      destruct H3.
      destruct (H7 t) as [t' [?[??]]]; auto.
      exists t'; split; auto. apply cons_elem; auto.

      intros. 
      destruct H0 as [a' [??]].
      destruct H3.
      destruct (H4 t) as [t' [??]]; auto.
      destruct (H1 t').
      destruct H5 as [t'' [??]].
      exists t''; split; auto.
      apply concat_in. exists (elem a'). split; auto.
      apply in_map. auto.
      destruct H7.
      exists x0; split; auto.
      apply PLT.hom_order with t' x0; auto.

    assert (exists zs:finset (pdomain Upper Y),
      (forall z, z ∈ zs -> forall a, a ∈ elem z ->
        exists q, q ∈ elem y /\ q ≤ a) /\
      (forall a, a ∈ elem x -> exists z, z ∈ zs /\
        forall t : X,
          t ∈ elem a ->
          exists q : Y, q ∈ elem z /\ q ∈ elem y /\ (t, q) ∈ PLT.hom_rel f)).

    revert H0. generalize (elem x). induction c; intros.
    exists nil. split; intros. 
    apply nil_elem in H2. elim H2.
    apply nil_elem in H2. elim H2.
    destruct IHc as [zs ?].
    intros; apply H0; apply cons_elem; auto.
    destruct (H0 a) as [z ?]; auto.
    apply cons_elem; auto.
    assert (Hz : inh hf z).
    generalize (elem_inh a).
    pattern hf at 2 5; case hf; simpl; auto.
    intros [??]. 
    destruct H3.
    destruct (H5 x0) as [?[??]]; eauto.
    exists (PdomElem Y z Hz :: zs).
    split.

    simpl; intros.
    apply cons_elem in H4.
    destruct H4.
    destruct H4.
    destruct (H6 a0) as [t [??]]; auto.
    simpl in H7. destruct H3.
    destruct (H3 t) as [q [??]]; eauto.
    destruct H2.
    eapply H2; eauto.

    intros. apply cons_elem in H4. destruct H4.
    exists (PdomElem Y z Hz).
    split. apply cons_elem; auto.
    simpl. intros.
    destruct H4.
    destruct (H6 t) as [t' [??]]; auto.
    destruct H3.
    destruct (H9 t') as [q [?[??]]]; auto.
    exists q; split; auto. split; auto.
    apply PLT.hom_order with t' q; auto.
    destruct H2.
    destruct (H5 a0) as [z' [??]]; auto.
    exists z'; split; auto.
    apply cons_elem; auto.
    
    destruct H2 as [zs [??]].
    assert (inh hf zs).
    generalize (elem_inh x).
    pattern hf at 2 7. case hf; simpl; auto.
    intros [??]. destruct (H3 x0) as [?[??]]; eauto.
    exists (PdomElem _ zs H4).
    split.
    simpl.
    rewrite (fmap_rel_elem _ _ (fmap X Y f Upper) Upper).
    hnf. intros.
    destruct (H3 a) as [z [??]]; auto.
    simpl. exists z. split; auto.
    rewrite (fmap_rel_elem _ _ f Upper).
    hnf; intros.
    destruct (H7 a0) as [q [?[??]]]; eauto.

    simpl. apply join_rel_elem.
    simpl. hnf; intros.
    simpl in H5.
    destruct H5 as [y' [??]].
    apply concat_in in H5.
    destruct H5 as [y'' [??]].
    apply in_map_iff in H5.
    destruct H5 as [q [??]].
    subst y''.
    eapply H2; eauto.
    exists q. split; auto.
    exists y'; split; auto.
  
(**)
    destruct H1. hnf in H0, H1. simpl in *.
    rename H0 into Hopp.
    rename H1 into H0.
    
    assert (forall a, a ∈ elem x -> exists z:finset Y,   
      (forall a, a ∈ z ->
        exists q, q ∈ elem y /\ q ≤ a) /\
      (forall b, b ∈ z ->
        exists q, q ∈ elem a /\ (q,b) ∈ PLT.hom_rel f) /\
      (forall t, t ∈ elem a ->
        exists q, q ∈ z /\ q ∈ elem y /\ (t,q) ∈ PLT.hom_rel f)).

    intros.
    cut (forall t, t ∈ elem a -> exists b, b ∈ elem y /\ (t,b) ∈ PLT.hom_rel f).
      generalize (elem a). induction c; intros.
      exists nil. split; intros. 
      apply nil_elem in H3. elim H3.
      split; intros.
      apply nil_elem in H3. elim H3.
      apply nil_elem in H3. elim H3.
      
      destruct IHc as [z ?]; auto.
      intros. apply H2. apply cons_elem; auto.
      destruct (H2 a0) as [q [??]]. apply cons_elem; auto.
      exists (q::z).
      split.
      intros. apply cons_elem in H6. destruct H6.
      exists q. split; auto.
      destruct H3 as [?[??]].
      apply H3; auto.
      split; intros.
      apply cons_elem in H6. destruct H6.
      exists a0. split. apply cons_elem; auto.
      apply PLT.hom_order with a0 q; auto.
      destruct H3 as [?[??]].
      destruct (H7 b) as [q2 [??]]; auto.
      exists q2; split; auto. apply cons_elem; auto.
      
      apply cons_elem in H6. destruct H6.
      exists q. split; auto.
      apply cons_elem; auto.
      split; auto. apply PLT.hom_order with a0 q; auto.
      destruct H3 as [?[??]].
      destruct (H8 t) as [t' [?[??]]]; auto.
      exists t'; split; auto. apply cons_elem; auto.

      intros. 
      destruct H1 as [a' [??]].
      destruct H3.
      destruct H4 as [??].
      destruct (H5 t) as [t' [??]]; auto.
      destruct (H0 t').
      destruct H6 as [t'' [??]].
      exists t''; split; auto.
      apply concat_in. exists (elem a'). split; auto.
      apply in_map. auto.
      destruct H8.
      exists x0; split; auto.
      apply PLT.hom_order with t' x0; auto.
      
    assert (forall ys:finset Y,
      (forall b, b ∈ ys -> exists a,
        a ∈ (concat X (map (elem (X:=X)) (elem x)) : finset _) /\
        (a, b) ∈ PLT.hom_rel f) ->
      exists zs:finset (pdomain Convex Y),
      (forall z, z ∈ zs -> forall a, a ∈ elem z ->
        exists q, q ∈ elem y /\ q ≤ a) /\
      (forall z, z ∈ zs ->
        exists a : powerdomain Convex X, a ∈ elem x /\ (a, z) ∈ fmap_convex_rel X Y f)
      /\
      (forall a, a ∈ elem x -> exists z, z ∈ zs /\
        (forall t : X,
          t ∈ elem a ->
          exists q : Y, q ∈ elem z /\ q ∈ elem y /\ (t, q) ∈ PLT.hom_rel f) 
        /\
        (forall q, q ∈ elem z ->
          exists t, t ∈ elem a /\ (t, q) ∈ PLT.hom_rel f)
      )
      /\
      (forall q, q ∈ ys ->
        exists z, z ∈ zs /\ exists a, a ∈ elem z /\ q ≤ a)).

      rename H1 into Ha.
      clear -Ha.
      induction ys; intros.
      
      assert (exists (zs:finset (pdomain Convex Y)),
      (forall z, z ∈ zs -> forall a, a ∈ elem z ->
        exists q, q ∈ elem y /\ q ≤ a) /\
      (forall z, z ∈ zs ->
        exists a : powerdomain Convex X, a ∈ elem x /\ (a, z) ∈ fmap_convex_rel X Y f)
      /\
      (forall a, a ∈ elem x -> exists z, z ∈ zs /\
        (forall t : X,
          t ∈ elem a ->
          exists q : Y, q ∈ elem z /\ q ∈ elem y /\ (t, q) ∈ PLT.hom_rel f)
        /\
        (forall q, q ∈ elem z ->
          exists t, t ∈ elem a /\ (t, q) ∈ PLT.hom_rel f))).

        clear H.
        revert Ha. generalize (elem x). induction c; intros.
        exists nil. intuition.
        apply nil_elem in H; elim H.
        apply nil_elem in H; elim H.
        apply nil_elem in H; elim H.

        destruct IHc as [zs [?[??]]].
        intros; apply Ha. apply cons_elem; auto.
        destruct (Ha a) as [z [?[??]]]; clear Ha. apply cons_elem; auto.
        assert (Hz : inh hf z).
        generalize (elem_inh a).
        pattern hf at 2 5. case hf; simpl; auto.
        intros [??]. destruct (H4 x0) as [?[??]]; eauto.
        exists (PdomElem _ z Hz ::zs).
        repeat split; intros.
        apply cons_elem in H5. destruct H5.
        destruct H5.
        destruct H7.
        destruct (H8 a0) as [a0' [??]]; auto.
        simpl in H9.
        destruct (H2 a0') as [q [??]]; auto.
        exists q; split; auto.
        rewrite H12; auto.
        eapply H; eauto.
        apply cons_elem in H5. destruct H5.
        exists a. split. apply cons_elem; auto.
        rewrite (fmap_rel_elem X Y f Convex).
        split; hnf; simpl; intros.
        destruct H5 as [[??][??]].
        destruct (H5 b) as [b' [??]]; auto.
        simpl in H10.
        destruct (H3 b') as [q [??]]; auto.
        exists q. split; auto.
        apply PLT.hom_order with q b'; auto.
        destruct (H4 a0) as [q [?[??]]]; auto.
        destruct H5 as [[??][??]].
        destruct (H10 q) as [q' [??]]; auto. 
        exists q'; split; auto.
        apply PLT.hom_order with a0 q; auto.
        destruct (H0 z0) as [a' [??]]; auto.
        exists a'; split; auto.
        apply cons_elem; auto.
        apply cons_elem in H5. destruct H5.
        econstructor. split. apply cons_elem; left. reflexivity.
        simpl. split; intros.
        destruct H5 as [[??][??]].
        destruct (H9 t) as [t' [??]]; auto.
        destruct (H4 t') as [q [?[??]]]; auto.
        exists q; split; auto. split; auto.
        apply PLT.hom_order with t' q; auto.
        destruct (H3 q) as [q' [??]]; auto.
        destruct H5 as [[??][??]].
        destruct (H10 q') as [q'' [??]]; auto.
        exists q''. split; auto.
        apply PLT.hom_order with q' q; auto.
        destruct (H1 a0) as [z' [?[??]]]; auto.
        exists z'; split; auto.
        simpl. apply cons_elem; auto.

      destruct H0 as [zs [?[??]]].
      exists zs; intuition.
      apply nil_elem in H3. elim H3.

      destruct IHys as [zs [?[?[??]]]].
      intros. apply H. apply cons_elem; auto.
      destruct (H a) as [x' [??]]; auto. apply cons_elem. auto. clear H.
      destruct H4 as [x2' [??]].
      apply concat_in in H. destruct H as [x2'' [??]].
      apply in_map_iff in H. destruct H as [x2''' [??]].
      subst x2''.
      destruct (H2 x2''') as [z [?[??]]].
      exists x2'''; split; auto.     
      destruct (H8 x2') as [q [?[??]]].
      exists x2'; split; auto.
      destruct (PLT.hom_directed hf X Y f x' (a:: q::nil)) as [q' [??]].
      apply directed.elem_inh with a. apply cons_elem; auto.
      red; intros.
      apply cons_elem in H13. destruct H13. rewrite H13.
      apply erel_image_elem. auto.
      apply cons_elem in H13. destruct H13. rewrite H13.
      apply erel_image_elem. apply PLT.hom_order with x2' q; auto.
      apply nil_elem in H13. elim H13.
      apply erel_image_elem in H14.
      assert (inh hf (q':: elem z)).
      apply inh_sub with (elem z).
      red; intros. apply cons_elem; auto.
      apply elem_inh.
      exists (PdomElem Y (q'::elem z) H15 :: zs).
      repeat split; intros.
      apply cons_elem in H16. destruct H16; auto.
      destruct H16.
      destruct H18.
      destruct (H19 a0) as [a0' [??]]; auto.
      simpl in H20.
      apply cons_elem in H20. destruct H20.
      rewrite H20 in H21.
      exists q; split; auto.
      rewrite <- H21.
      apply H13. apply cons_elem. right. apply cons_elem; auto.
      destruct (H0 z H a0' H20) as [t [??]].
      exists t; split; auto. rewrite H23. auto.
      eapply H0; eauto.

      apply cons_elem in H16. destruct H16.
      exists x2'''. split; auto.
      exists x2'''. split; auto.
      rewrite (fmap_rel_elem X Y f Convex).
      split; hnf; simpl; intros.
      destruct H16.
      destruct H16.
      destruct (H16 b) as [m [??]]; auto.
      simpl in H20. apply cons_elem in H20.
      destruct H20.
      rewrite H20 in H21.
      exists x2'. split; auto.
      exists x2'; split; auto.
      apply PLT.hom_order with x' q'; auto.
      destruct (H9 m) as [t [??]]; auto.
      exists t. split; auto.
      apply PLT.hom_order with t m; auto.
      destruct (H8 a0) as [p [?[??]]]; auto.
      destruct H16.      
      destruct H16.
      destruct (H22 p) as [p' [??]]; auto.
      simpl. apply cons_elem; auto.
      exists p'; split; auto.
      apply PLT.hom_order with a0 p; auto.
      apply H1; auto.

      destruct (H2 a0) as [z' [??]]; auto.
      exists z'; split; auto.
      apply cons_elem; auto.
      
      apply cons_elem in H16. destruct H16.
      econstructor. split. apply cons_elem. left. reflexivity.
      simpl. exists q'. split.
      apply cons_elem; auto. 
      rewrite H16. apply H13.
      apply cons_elem; auto.
      destruct (H3 q0) as [m [??]]; auto.
      exists m; split; auto.
      apply cons_elem; auto.
 
    destruct (H2 (elem y)) as [zs [?[?[??]]]]; clear H2.
    intros. apply Hopp. auto.

    assert (inh hf zs).
    generalize (elem_inh x).
    pattern hf at 2 7. case hf; simpl; auto.
    intros [??]. 
    destruct (H5 x0) as [?[??]]; eauto.
    exists (PdomElem _ zs H2).
    split.
    simpl.
    rewrite (fmap_rel_elem _ _ (fmap X Y f Convex) (Convex)).
    split; hnf; simpl; intros. auto.
    destruct (H5 a) as [z [?[??]]]; auto.
    simpl. exists z. split; auto.
    rewrite (fmap_rel_elem _ _ f Convex).
    hnf; intros.
    split; hnf; simpl; intros.
    auto. 
    
    destruct (H9 a0) as [q [?[??]]]; eauto.
    simpl. apply join_rel_elem.
    simpl. split; hnf; intros.

(**)
    simpl.
    destruct (H6 x0) as [?[?[?[??]]]]; auto.
    destruct H8 as [?[??]].
    destruct H11.
    destruct H11.
    destruct (H11 x2) as [?[??]]; auto.
    destruct H14 as [?[??]].
    exists x5.
    split.    
    exists x5. split; auto.
    apply concat_in. exists (elem x3). split; auto.
    apply in_map. auto.
    rewrite H10. rewrite H15. auto.

(**)
    simpl in H7.
    destruct H7 as [y' [??]].
    apply concat_in in H7.
    destruct H7 as [y'' [??]].
    apply in_map_iff in H7.
    destruct H7 as [q [??]].
    subst y''.
    eapply H3; eauto.
    exists q. split; auto.
    exists y'; split; auto.

(**)
    apply PLT.compose_hom_rel in H.
    apply PLT.compose_hom_rel.
    destruct H as [q [??]].
    simpl in H0.    
    rewrite (join_rel_elem) in H0.
    exists (concat_elem sort X (elem x) (elem_inh x)).
    split.
    simpl. apply join_rel_elem. auto.
    apply PLT.hom_order with
      (concat_elem sort X (elem x) (elem_inh x))
      (concat_elem sort Y (elem q) (elem_inh q)); auto.
    simpl.
    rewrite (fmap_rel_elem X Y f sort).
    clear H0 y.    
    simpl in H.
    rewrite (fmap_rel_elem _ _ (fmap X Y f sort) sort) in H.
    
    destruct sort; simpl in *.
    hnf in H. hnf; simpl; intros.
    destruct H0 as [b' [??]].
    apply concat_in in H0.
    destruct H0 as [b'' [??]].
    apply in_map_iff in H0.
    destruct H0 as [b''' [??]]. subst b''.
    destruct (H b''') as [p [??]]; auto.
    exists b'''; split; auto. 
    rewrite (fmap_rel_elem _ _ f Lower) in H4.
    destruct (H4 b') as [p' [??]]; auto.
    exists b'; split; auto.  
    destruct H0 as [p2 [??]].
    destruct H7.
    destruct (H7 p') as [p2' [??]]; auto.
    destruct H9 as [p2'' [??]].
    exists p2'. split.
    2: apply PLT.hom_order with p' b'; auto.    
    exists p2''; split; auto.
    apply concat_in. exists (elem p2); split; auto.
    apply in_map. auto.
    
    hnf in H. hnf; simpl; intros.
    destruct H0 as [a' [??]].
    apply concat_in in H0.
    destruct H0 as [p [??]].
    apply in_map_iff in H0.
    destruct H0 as [t [??]]. subst p.
    destruct (H t) as [b [??]].
    exists t; split; auto.
    destruct H0 as [b' [??]].
    rewrite (fmap_rel_elem _ _ f Upper) in H4.
    hnf in H4.
    destruct (H4 a) as [r [??]]; auto.
    exists a'; split; auto.
    destruct H5.
    destruct (H8 r) as [r' [??]]; auto.
    destruct H9 as [r'' [??]].
    exists r'.
    split.
    exists r''. split; auto.
    apply concat_in.
    exists (elem b'); split; auto.
    apply in_map. auto.
    apply PLT.hom_order with a r; auto.
    
    destruct H. hnf in H, H0.
    split; hnf; simpl; intros.
        
    destruct H1 as [a' [??]].
    apply concat_in in H1.
    destruct H1 as [p [??]].
    apply in_map_iff in H1.
    destruct H1 as [t [??]]. subst p.
    destruct (H t) as [c [??]].
    exists t; split; auto.
    destruct H1 as [c' [??]].
    rewrite (fmap_rel_elem _ _ f Convex) in H5.
    destruct H5 as [? _].
    destruct (H5 a') as [r [??]]; auto.
    exists a'; split; auto.
    destruct H6.
    destruct H6.
    destruct (H6 r) as [r' [??]]; auto.
    destruct H11 as [r'' [??]].
    exists r'.
    split.
    exists r''. split; auto.
    apply concat_in.
    exists (elem c'); split; auto.
    apply in_map. auto.
    apply PLT.hom_order with r a'; auto.
    
    destruct H1 as [a' [??]].
    apply concat_in in H1.
    destruct H1 as [p [??]].
    apply in_map_iff in H1.
    destruct H1 as [t [??]]. subst p.
    destruct (H0 t) as [b [??]].
    exists t; split; auto.
    destruct H1 as [b' [??]].
    rewrite (fmap_rel_elem _ _ f Convex) in H5.
    destruct H5 as [_ ?].
    destruct (H5 a) as [r [??]]; auto.
    exists a'; split; auto.
    destruct H6.
    destruct H9.
    destruct (H10 r) as [r' [??]]; auto.
    destruct H11 as [r'' [??]].
    exists r'.
    split.
    exists r''. split; auto.
    apply concat_in.
    exists (elem b'); split; auto.
    apply in_map. auto.
    apply PLT.hom_order with a r; auto.
  Qed.

  Program Definition joinNT sort : nt (pdomain sort ∘ pdomain sort) (pdomain sort)
    := NT (pdomain sort ∘ pdomain sort) (pdomain sort) (join sort) _.
  Next Obligation.
    intros. symmetry. apply join_natural.
  Qed.

  (* The monad laws for powerdomains *)
  Lemma monad_unit1 sort :
    joinNT sort ∘ singleNT sort◃pdomain sort ≈ id.
  Proof.
    intro X; simpl.
    split; hnf; simpl; intros [x y] ?.
    simpl. apply ident_elem.
    apply PLT.compose_hom_rel in H.
    destruct H as [q [??]].
    simpl in H0.
    apply join_rel_elem in H0.
    rewrite H0.
    simpl in H. 
    rewrite (single_rel_elem sort) in H.
    destruct sort; simpl in *.
    hnf; simpl; intros.
    hnf in H. simpl in H.
    destruct H1 as [x0' [??]].
    apply concat_in in H1.
    destruct H1 as [m [??]].
    apply in_map_iff in H1.
    destruct H1 as [m' [??]]. subst m.
    destruct (H m') as [y' [??]]; auto.
    exists m'; split; auto.
    apply cons_elem in H1. destruct H1.
    2: apply nil_elem in H1; elim H1.
    rewrite H1 in H5.
    destruct (H5 x0) as [z [??]].
    exists x0'; auto.
    exists z; auto.
    hnf; simpl; intros.
    hnf in H. simpl in H.
    destruct (H x) as [z [??]].
    apply cons_elem; auto.
    destruct H2 as [z' [??]].
    rewrite H4 in H3.
    destruct (H3 y0) as [m [??]]; auto.
    destruct H5 as [m' [??]].
    exists m. split; auto.
    exists m'; split; auto.
    apply concat_in.
    exists (elem z'). split; auto.
    apply in_map. auto.
    
    clear H0.
    split; hnf; simpl; intros.
    destruct H0 as [x0' [??]].
    apply concat_in in H0.
    destruct H0 as [y' [??]].
    apply in_map_iff in H0.
    destruct H0 as [y'' [??]]. subst y'.
    destruct H.    
    destruct (H y'') as [z [??]].
    exists y''; split; auto.
    simpl in H4.
    apply cons_elem in H4. destruct H4.
    2: apply nil_elem in H4; elim H4.
    rewrite H4 in H5.
    destruct H5.
    destruct (H5 x0') as [p [??]]; auto.
    exists x0'; auto.
    exists p; split; auto.
    rewrite H1; auto.
    destruct H.
    destruct (H1 x) as [z [??]]; auto.
    simpl. apply cons_elem; auto.
    destruct H2 as [z' [??]].
    rewrite H4 in H3.
    destruct H3.
    destruct (H5 y0) as [p [??]]; auto.    
    destruct H6 as [p' [??]].
    exists p'. split.
    exists p'; split; auto.
    apply concat_in. exists (elem z'). split; auto.
    apply in_map; auto.
    rewrite <- H8; auto.

    simpl in H. apply ident_elem in H.
    apply PLT.compose_hom_rel.
    exists (single_elem (pdomain sort X) x).
    split.
    simpl. apply single_rel_elem. auto.
    simpl. apply join_rel_elem. simpl.
    rewrite H.
    destruct sort.
    hnf; simpl; intros.
    exists x0. split; auto.
    apply app_elem; auto.
    hnf; simpl; intros.
    apply app_elem in H0. destruct H0; eauto.
    apply nil_elem in H0. elim H0.
    split; hnf; simpl; intros.
    exists x0; split; auto.
    apply app_elem; auto.
    apply app_elem in H0. destruct H0; eauto.
    apply nil_elem in H0. elim H0.
  Qed.

  Lemma monad_unit2 sort :
    joinNT sort ∘ pdomain sort▹singleNT sort ≈ id.
  Proof.
    intro X. simpl.
    split; hnf; simpl; intros [x y] ?.
    simpl. apply ident_elem.
    apply PLT.compose_hom_rel in H.
    destruct H as [q [??]].
    simpl in H0.
    apply join_rel_elem in H0.
    rewrite H0.
    simpl in H. 
    rewrite (fmap_rel_elem _ _ (single sort X) sort) in H.
    clear y H0.
    destruct sort; simpl in *.
    hnf; simpl; intros.
    hnf in H. simpl in H.
    destruct H0 as [x0' [??]].
    apply concat_in in H0.
    destruct H0 as [m [??]].
    apply in_map_iff in H0.
    destruct H0 as [m' [??]]. subst m.
    destruct (H m') as [y' [??]]; auto.
    exists m'; split; auto.
    rewrite (single_rel_elem Lower X) in H4.
    hnf in H4.
    destruct (H4 x0') as [z [??]]; auto.
    exists x0'; split; auto.
    simpl in H5.
    apply cons_elem in H5. destruct H5.
    2: apply nil_elem in H5; elim H5.
    rewrite H5 in H6.
    exists y'; split; auto.
    rewrite H1; auto.
    hnf; simpl; intros.
    hnf in H. simpl in H.
    destruct (H y) as [z [??]]. auto.
    destruct H1 as [z' [??]]; auto.
    rewrite (single_rel_elem Upper X) in H2.
    rewrite H3 in H2.
    destruct (H2 y) as [p [??]]; auto.
    simpl. apply cons_elem; auto.
    destruct H4 as [p' [??]]; auto.
    rewrite H6 in H5.
    exists p'. split; auto.
    exists p'; split; auto.
    apply concat_in.
    exists (elem z'); split; auto.
    apply in_map; auto.
    
    destruct H.        
    split.
    clear H0.
    hnf; simpl; intros.
    hnf in H. simpl in H.
    destruct H0 as [x0' [??]].
    apply concat_in in H0.
    destruct H0 as [m [??]].
    apply in_map_iff in H0.
    destruct H0 as [m' [??]]. subst m.
    destruct (H m') as [y' [??]]; auto.
    exists m'; split; auto.
    rewrite (single_rel_elem Convex X) in H4.
    destruct H4 as [? _]. hnf in H4.
    destruct (H4 x0') as [z [??]]; auto.
    exists x0'; split; auto.
    simpl in H5.
    apply cons_elem in H5. destruct H5.
    2: apply nil_elem in H5; elim H5.
    rewrite H5 in H6.
    exists y'; split; auto.
    rewrite H1; auto.

    clear H. rename H0 into H .
    hnf; simpl; intros.
    hnf in H. simpl in H.
    destruct (H y) as [z [??]]. auto.
    destruct H1 as [z' [??]]; auto.
    rewrite (single_rel_elem Convex X) in H2.
    rewrite H3 in H2.
    destruct H2 as [_ ?].
    destruct (H2 y) as [p [??]]; auto.
    simpl. apply cons_elem; auto.
    destruct H4 as [p' [??]]; auto.
    rewrite H6 in H5.
    exists p'. split; auto.
    exists p'; split; auto.
    apply concat_in.
    exists (elem z'); split; auto.
    apply in_map; auto.

    simpl in H. apply ident_elem in H.
    apply PLT.compose_hom_rel.
    set (xs := map (single_elem X) (elem x) : finset (pdomain sort X)).
    assert (Hxs : inh hf xs).
    generalize (elem_inh x).
    pattern hf at 2 7. case hf; simpl; auto.
    intros [??]. unfold xs.
    destruct H0 as [x0' [??]].
    exists (single_elem X x0').
    exists (single_elem X x0'). split; auto.
    apply in_map. auto.
    exists (PdomElem _ xs Hxs).
    split.
    simpl.
    rewrite (fmap_rel_elem _ _ (single sort X) sort).
    destruct sort.
    hnf; simpl; intros.
    destruct H0 as [b' [??]].        
    unfold xs in H0.
    apply in_map_iff in H0.
    destruct H0 as [q [??]]. subst b'.
    exists q. split.
    exists q; split; auto.
    simpl. rewrite (single_rel_elem Lower X). auto.
    hnf; simpl; intros.
    destruct H0 as [a' [??]].
    exists (single_elem _ a').
    split. unfold xs.
    exists (single_elem X a'). split; auto.
    apply in_map. auto.
    rewrite (single_rel_elem Upper X). 
    hnf; simpl; intros.
    apply cons_elem in H2. destruct H2.
    2: apply nil_elem in H2; elim H2.
    exists a'. split; auto. apply cons_elem; auto.
    rewrite <- H1; auto.
    
    split. 
    hnf; simpl; intros.
    destruct H0 as [b' [??]].        
    unfold xs in H0.
    apply in_map_iff in H0.
    destruct H0 as [q [??]]. subst b'.
    exists q. split.
    exists q; split; auto.
    simpl. rewrite (single_rel_elem Convex X). auto.
    hnf; simpl; intros.
    destruct H0 as [a' [??]].
    exists (single_elem _ a').
    split. unfold xs.
    exists (single_elem X a'). split; auto.
    apply in_map. auto.
    rewrite (single_rel_elem Convex X). 
    split.
    hnf; simpl; intros.
    apply cons_elem in H2. destruct H2.
    2: apply nil_elem in H2; elim H2.
    exists a'. split; auto. apply cons_elem; auto.
    hnf; simpl; intros.
    apply cons_elem in H2. destruct H2.
    2: apply nil_elem in H2; elim H2.
    exists a'. split; auto. apply cons_elem; auto.
    rewrite <- H1; auto.

    simpl.
    rewrite (join_rel_elem sort X).
    rewrite H. simpl.
    destruct sort.

    hnf; simpl; intros.
    destruct H0 as [x0' [??]].
    exists x0'. split; auto.
    exists x0'; split; auto.
    apply concat_in. exists (x0'::nil). split; simpl; auto.
    unfold xs.
    rewrite map_map. simpl.
    apply in_map_iff.
    exists x0'. split; auto.
  
    hnf; simpl; intros.
    destruct H0 as [x0' [??]].
    exists x0'. split; auto.
    exists x0'; split; auto.
    apply concat_in in H0.
    destruct H0 as [q [??]].
    unfold xs in H0.
    rewrite map_map in H0.
    apply in_map_iff in H0. destruct H0 as [q' [??]].
    subst q. simpl in H2.
    destruct H2; subst. 2: contradiction.
    auto.

    split.
    hnf; simpl; intros.
    destruct H0 as [x0' [??]].
    exists x0'. split; auto.
    exists x0'; split; auto.
    apply concat_in. exists (x0'::nil). split; simpl; auto.
    unfold xs.
    rewrite map_map. simpl.
    apply in_map_iff.
    exists x0'. split; auto.
  
    hnf; simpl; intros.
    destruct H0 as [x0' [??]].
    exists x0'. split; auto.
    exists x0'; split; auto.
    apply concat_in in H0.
    destruct H0 as [q [??]].
    unfold xs in H0.
    rewrite map_map in H0.
    apply in_map_iff in H0. destruct H0 as [q' [??]].
    subst q. simpl in H2.
    destruct H2; subst. 2: contradiction.
    auto.
  Qed.

  Lemma monad_assoc sort :
    joinNT sort ∘ joinNT sort◃pdomain sort ≈
    joinNT sort ∘ pdomain sort▹joinNT sort.
  Proof.
    intro X; simpl.
    split; hnf; simpl; intros [x y] ?.
    apply PLT.compose_hom_rel in H.
    destruct H as [q [??]].
    simpl in *.
    apply join_rel_elem in H.
    apply join_rel_elem in H0.
    eapply PLT.hom_order.
    reflexivity. apply H0. clear H0.
    apply PLT.compose_hom_rel.
    set (xs := map (fun a => concat_elem sort X (elem a) (elem_inh a)) (elem x) : 
      finset (powerdomain sort X)).
    assert (Hxs : inh hf xs).
    generalize (elem_inh x).    
    pattern hf at 2 5. case hf; simpl; auto.
    intros [??]. unfold xs.
    destruct H0 as [x0' [??]].
    exists (concat_elem sort X (elem x0') (elem_inh x0')).
    econstructor. split. 2: reflexivity.
    apply in_map_iff.
    exists x0'; split; auto.
    exists (PdomElem _ xs Hxs).
    split.
    simpl.
    rewrite (fmap_rel_elem _ _ (join sort X) sort).

    clear q H.
    destruct sort.
    
    hnf; simpl; intros.
    unfold xs in H.
    destruct H as [b' [??]].
    apply in_map_iff in H.
    destruct H as [z [??]]. subst b'.
    exists z. split. exists z; split; auto.
    rewrite (join_rel_elem Lower X). auto.
    hnf; simpl; intros.    
    destruct H as [a' [??]].
    exists (concat_elem Upper X (elem a') (elem_inh a')).
    split. unfold xs.
    exists (concat_elem Upper X (elem a') (elem_inh a')). split; auto.
    apply in_map_iff. exists a'. split; auto.
    rewrite join_rel_elem.
    hnf; simpl; intros.
    destruct H1 as [y0' [??]].
    apply concat_in in H1.
    destruct H1 as [q [??]].
    apply in_map_iff in H1.
    destruct H1 as [q' [??]]. subst q.
    destruct H0.
    destruct (H1 q') as [p [??]].
    exists q'; split; auto.        
    destruct H5 as [p' [??]].
    rewrite H7 in H6.
    destruct (H6 y0') as [t [??]]; auto.    
    exists y0'; auto.
    destruct H8 as [t' [??]].
    exists t'. split.
    exists t'; split; auto.
    apply concat_in. exists (elem p'); split; auto.
    apply in_map; auto.
    rewrite <- H10; auto.
    rewrite H2; auto.
    
    split.
    hnf; simpl; intros.
    unfold xs in H.
    destruct H as [b' [??]].
    apply in_map_iff in H.
    destruct H as [z [??]]. subst b'.
    exists z. split. exists z; split; auto.
    rewrite (join_rel_elem Convex X). auto.
    hnf; simpl; intros.    
    destruct H as [a' [??]].
    exists (concat_elem Convex X (elem a') (elem_inh a')).
    split. unfold xs.
    exists (concat_elem Convex X (elem a') (elem_inh a')). split; auto.
    apply in_map_iff. exists a'. split; auto.
    rewrite join_rel_elem.

    split.
    hnf; simpl; intros.
    destruct H1 as [y0' [??]].
    apply concat_in in H1.
    destruct H1 as [q [??]].
    apply in_map_iff in H1.
    destruct H1 as [q' [??]]. subst q.
    destruct H0.
    destruct H1.
    destruct (H1 q') as [p [??]].
    exists q'; split; auto.        
    destruct H6 as [p' [??]].
    rewrite H8 in H7.
    destruct H7.
    destruct (H7 y0') as [t [??]]; auto.
    exists y0'; auto.
    destruct H10 as [t' [??]].
    exists t'. split.
    exists t'; split; auto.
    apply concat_in. exists (elem p'); split; auto.
    apply in_map; auto.
    rewrite <- H12; auto.
    rewrite H2; auto.

    hnf; simpl; intros.
    destruct H1 as [y0' [??]].
    apply concat_in in H1.
    destruct H1 as [q [??]].
    apply in_map_iff in H1.
    destruct H1 as [q' [??]]. subst q.
    destruct H0.
    destruct H1.
    destruct (H5 q') as [p [??]].
    exists q'; split; auto.        
    destruct H6 as [p' [??]].
    rewrite H8 in H7.
    destruct H7.
    destruct (H9 y0') as [t [??]]; auto.
    exists y0'; auto.
    destruct H10 as [t' [??]].
    exists t'. split.
    exists t'; split; auto.
    apply concat_in. exists (elem p'); split; auto.
    apply in_map; auto.
    rewrite <- H12; auto.
    rewrite H2; auto.
    
    simpl. rewrite (join_rel_elem sort X). simpl. 
    destruct sort.

    hnf in H. hnf; simpl in *; intros.
    destruct H0 as [x0' [??]].
    apply concat_in in H0. destruct H0 as [p [??]].
    apply in_map_iff in H0. destruct H0 as [p' [??]]. subst p.
    destruct (H p') as [z [??]].
    exists p'; split; auto.
    destruct H0 as [z' [??]].        
    apply concat_in in H0.
    destruct H0 as [r [??]].
    apply in_map_iff in H0.
    destruct H0 as [r' [??]]. subst r.
    rewrite H5 in H4.
    destruct (H4 x0') as [m [??]]; auto.
    exists x0'; split; auto.
    destruct H0 as [m' [??]]. exists m'.
    split.    
    exists m'; split; auto.
    apply concat_in. unfold xs. rewrite map_map.
    simpl.
    econstructor. split.
    apply in_map_iff.
    econstructor.
    split. reflexivity.
    apply H7.
    apply concat_in.
    exists (elem z'). split; auto.
    apply in_map. auto.
    rewrite <- H9; auto.
    rewrite H1; auto.

    hnf; simpl; intros.
    destruct H0 as [y0' [??]].
    apply concat_in in H0. destruct H0 as [p [??]].
    unfold xs in H0. rewrite map_map in H0.
    apply in_map_iff in H0. destruct H0 as [p' [??]]. subst p.
    simpl in H2.
    apply concat_in in H2. destruct H2 as [r [??]].
    apply in_map_iff in H0. destruct H0 as [r' [??]]. subst r.
    hnf in H. simpl in H.
    destruct (H r') as [t [??]].
    exists r'. split; auto.
    apply concat_in.
    exists (elem p'). split; auto.
    apply in_map. auto.
    destruct H0 as [t' [??]].
    rewrite H6 in H5.
    destruct (H5 y0') as [s [??]]; auto.
    exists y0'; auto.
    destruct H7 as [s' [??]].
    exists s'. split.
    exists s'. split; auto.
    apply concat_in. exists (elem t'); split; auto.
    apply in_map. auto.
    rewrite <- H9; auto.
    rewrite H1; auto.
    
    split.
    destruct H as [? _].
    hnf in H. hnf; simpl in *; intros.
    destruct H0 as [x0' [??]].
    apply concat_in in H0. destruct H0 as [p [??]].
    apply in_map_iff in H0. destruct H0 as [p' [??]]. subst p.
    destruct (H p') as [z [??]].
    exists p'; split; auto.
    destruct H0 as [z' [??]].        
    apply concat_in in H0.
    destruct H0 as [r [??]].
    apply in_map_iff in H0.
    destruct H0 as [r' [??]]. subst r.
    rewrite H5 in H4.
    destruct H4 as [H4 _].
    destruct (H4 x0') as [m [??]]; auto.
    exists x0'; split; auto.
    destruct H0 as [m' [??]]. exists m'.
    split.    
    exists m'; split; auto.
    apply concat_in. unfold xs. rewrite map_map.
    simpl.
    econstructor. split.
    apply in_map_iff.
    econstructor.
    split. reflexivity.
    apply H7.
    apply concat_in.
    exists (elem z'). split; auto.
    apply in_map. auto.
    rewrite <- H9; auto.
    rewrite H1; auto.

    destruct H as [_ ?].
    hnf; simpl; intros.
    destruct H0 as [y0' [??]].
    apply concat_in in H0. destruct H0 as [p [??]].
    unfold xs in H0. rewrite map_map in H0.
    apply in_map_iff in H0. destruct H0 as [p' [??]]. subst p.
    simpl in H2.
    apply concat_in in H2. destruct H2 as [r [??]].
    apply in_map_iff in H0. destruct H0 as [r' [??]]. subst r.
    hnf in H. simpl in H.
    destruct (H r') as [t [??]].
    exists r'. split; auto.
    apply concat_in.
    exists (elem p'). split; auto.
    apply in_map. auto.
    destruct H0 as [t' [??]].
    rewrite H6 in H5.
    destruct H5 as [_ H5].
    destruct (H5 y0') as [s [??]]; auto.
    exists y0'; auto.
    destruct H7 as [s' [??]].
    exists s'. split.
    exists s'. split; auto.
    apply concat_in. exists (elem t'); split; auto.
    apply in_map. auto.
    rewrite <- H9; auto.
    rewrite H1; auto.

    apply PLT.compose_hom_rel in H.    
    destruct H as [z [??]].
    apply PLT.compose_hom_rel.
    simpl in H0.    
    rewrite (join_rel_elem sort X) in H0.
    simpl in H.
    rewrite (fmap_rel_elem _ _ (join sort X) sort) in H.
    exists (concat_elem sort (powerdomain sort X) (elem x) (elem_inh x)).
    split.
    simpl. rewrite (join_rel_elem sort). auto.
    rewrite (join_rel_elem sort). simpl.
    rewrite H0.
    clear y H0.
    
    destruct sort.
    
    hnf in H. simpl in H.
    hnf; simpl; intros.
    destruct H0 as [x0' [??]].
    apply concat_in in H0.
    destruct H0 as [q [??]].
    apply in_map_iff in H0. destruct H0 as [q' [??]]. subst q.
    destruct (H q') as [t [??]].
    exists q'; split; auto.
    rewrite (join_rel_elem Lower X) in H4.
    hnf in H4. simpl in H4.
    destruct (H4 x0') as [s [??]].
    exists x0'; split; auto.
    destruct H5 as [s' [??]].
    apply concat_in in H5.
    destruct H5 as [p [??]].
    apply in_map_iff in H5. destruct H5 as [p' [??]]. subst p.
    destruct H0 as [t' [??]].
    destruct H5.
    destruct (H5 p') as [p'' [??]]; auto.
    exists p'; split; auto.
    destruct H11 as [p''' [??]].
    rewrite H13 in H12.
    destruct (H12 s') as [s'' [??]]; auto.
    exists s'; split; auto.
    destruct H14 as [s''' [??]].
    exists s''. split.
    exists s'''. split; auto.
    apply concat_in.
    exists (elem p'''). split; auto.
    apply in_map.
    apply concat_in.
    exists (elem t'); split; auto.
    apply in_map. auto.
    rewrite H1. rewrite H6.
    rewrite H7. auto.

    hnf in H. simpl in H.
    hnf; simpl; intros.
    destruct H0 as [y' [??]].
    apply concat_in in H0.
    destruct H0 as [q [??]].
    apply in_map_iff in H0.
    destruct H0 as [q' [??]]. subst q.
    apply concat_in in H3. destruct H3 as [p [??]].
    apply in_map_iff in H0. destruct H0 as [p' [??]]. subst p.
    destruct (H p') as [r [??]].    
    exists p'; split; auto.
    rewrite (join_rel_elem Upper X) in H5.
    hnf in H5; simpl in H5.
    destruct H0 as [r' [??]].
    destruct (H5 y') as [t [??]].
    exists y'; split; auto.
    apply concat_in. exists (elem q'). split ;auto.
    apply in_map. auto.
    destruct H7 as [t' [??]].
    destruct H6.
    destruct (H10 t') as [s [??]].
    exists t'; split; auto.
    destruct H11 as [s' [??]].
    exists s'. split.
    exists s'; split; auto.
    apply concat_in.
    exists (elem r'). split; auto.
    apply in_map. auto.
    rewrite <- H13.
    rewrite H12. rewrite <- H9. rewrite H8. auto.

    split. destruct H as [? _].

    hnf in H. simpl in H.
    hnf; simpl; intros.
    destruct H0 as [x0' [??]].
    apply concat_in in H0.
    destruct H0 as [q [??]].
    apply in_map_iff in H0. destruct H0 as [q' [??]]. subst q.
    destruct (H q') as [t [??]].
    exists q'; split; auto.
    rewrite (join_rel_elem Convex X) in H4.
    destruct H4 as [? _].
    hnf in H4. simpl in H4.
    destruct (H4 x0') as [s [??]].
    exists x0'; split; auto.
    destruct H5 as [s' [??]].
    apply concat_in in H5.
    destruct H5 as [p [??]].
    apply in_map_iff in H5. destruct H5 as [p' [??]]. subst p.
    destruct H0 as [t' [??]].
    destruct H5.
    destruct H5 as [? _].
    destruct (H5 p') as [p'' [??]]; auto.
    exists p'; split; auto.
    destruct H11 as [p''' [??]].
    rewrite H13 in H12.
    destruct H12 as [? _].
    destruct (H12 s') as [s'' [??]]; auto.
    exists s'; split; auto.
    destruct H14 as [s''' [??]].
    exists s''. split.
    exists s'''. split; auto.
    apply concat_in.
    exists (elem p'''). split; auto.
    apply in_map.
    apply concat_in.
    exists (elem t'); split; auto.
    apply in_map. auto.
    rewrite H1. rewrite H6.
    rewrite H7. auto.

    destruct H as [_ ?].
    hnf in H. simpl in H.
    hnf; simpl; intros.
    destruct H0 as [y' [??]].
    apply concat_in in H0.
    destruct H0 as [q [??]].
    apply in_map_iff in H0.
    destruct H0 as [q' [??]]. subst q.
    apply concat_in in H3. destruct H3 as [p [??]].
    apply in_map_iff in H0. destruct H0 as [p' [??]]. subst p.
    destruct (H p') as [r [??]].    
    exists p'; split; auto.
    rewrite (join_rel_elem Convex X) in H5.
    hnf in H5; simpl in H5.
    destruct H0 as [r' [??]].
    destruct H5 as [_ ?].
    destruct (H5 y') as [t [??]].
    exists y'; split; auto.
    apply concat_in. exists (elem q'). split ;auto.
    apply in_map. auto.
    destruct H7 as [t' [??]].
    destruct H6.
    destruct H10 as [_ ?].
    destruct (H10 t') as [s [??]].
    exists t'; split; auto.
    destruct H11 as [s' [??]].
    exists s'. split.
    exists s'; split; auto.
    apply concat_in.
    exists (elem r'). split; auto.
    apply in_map. auto.
    rewrite <- H13.
    rewrite H12. rewrite <- H9. rewrite H8. auto.
  Qed.

End powerdom.

Definition empty_elem sort (X:PLT) : pdomain false sort X :=
  PdomElem false X nil I.

Definition empty_rel sort (X Y:PLT) : erel X (pdomain false sort Y) :=
  @esubset_dec (X × pdomain false sort Y)
    (fun xy => snd xy ≤ empty_elem sort Y)
    (fun xy => eff_ord_dec _ (PLT.effective (pdomain false sort Y)) _ _)
    (eprod (eff_enum _ (PLT.effective X))
           (eff_enum _ (PLT.effective (pdomain false sort Y)))).

Lemma empty_rel_elem sort (X Y:PLT) x y :
  (x,y) ∈ empty_rel sort X Y <-> y ≤ empty_elem sort Y.
Proof.
  unfold empty_rel. rewrite esubset_dec_elem.
  intuition.
  apply eprod_elem; split; apply eff_complete.
  intros. rewrite <- H0.
  destruct H as [[??][??]]; auto.
Qed.

Program Definition empty sort (X Y:PLT) : X → pdomain false sort Y :=
  PLT.Hom false X (pdomain false sort Y) (empty_rel sort X Y) _ _ .
Next Obligation.
  simpl; intros. 
  rewrite (empty_rel_elem sort X Y) in H1.
  rewrite (empty_rel_elem sort X Y).
  rewrite <- H1. auto.
Qed.
Next Obligation.
  repeat intro.
  exists (empty_elem sort Y).
  split.
  hnf; intros.
  apply H in H0.
  apply erel_image_elem in H0.
  rewrite (empty_rel_elem sort X Y) in H0.
  auto.
  apply erel_image_elem.
  rewrite (empty_rel_elem sort X Y). auto.
Qed.

Lemma empty_natural sort (X Y Z:PLT) (f:Y → Z) :
  pdomain false sort·f ∘ empty sort X Y ≈ empty sort X Z.
Proof.
  split; hnf; intros [??] ?.
  apply PLT.compose_hom_rel in H.
  destruct H as [?[??]].
  rewrite (empty_rel_elem sort X Z).
  rewrite (empty_rel_elem sort X Y) in H.
  assert ((empty_elem sort Y, c0) ∈ PLT.hom_rel (pdomain false sort·f)).
  apply PLT.hom_order with x c0; eauto.
  clear H H0.
  simpl in H1.
  rewrite (fmap_rel_elem false Y Z f sort) in H1.
  destruct sort.  

  hnf in H1; hnf; simpl in *; intros.
  destruct (H1 x0) as [q [??]]; auto.
  apply nil_elem in H0. elim H0.
  hnf; intros.  
  simpl in H. apply nil_elem in H. elim H.
  destruct H1.
  split; hnf; simpl in *; intros.
  destruct (H x0) as [q[??]]; auto.
  simpl in *. apply nil_elem in H2. elim H2.
  apply nil_elem in H1. elim H1.
  
  apply PLT.compose_hom_rel.
  simpl in H.  
  rewrite (empty_rel_elem sort X Z) in H.
  exists (empty_elem sort Y).
  split.
  rewrite (empty_rel_elem sort X Y). auto.
  apply PLT.hom_order with (empty_elem sort Y) (empty_elem sort Z); auto.
  simpl.
  rewrite (fmap_rel_elem false Y Z f sort).
  destruct sort; hnf; simpl; intros.
  apply nil_elem in H0. elim H0.
  apply nil_elem in H0. elim H0.
  split; hnf; simpl; intros.  
  apply nil_elem in H0. elim H0.
  apply nil_elem in H0. elim H0.
Qed.

Lemma empty_unit sort (X Y:PLT) (f:X → pdomain false sort Y) :
  f ≈ union false sort Y ∘ 〈 empty sort X Y, f 〉.
Proof.
  split; hnf; intros. destruct a as [x y].
  apply PLT.compose_hom_rel.
  exists (empty_elem sort Y, y).
  split.
  apply PLT.pair_hom_rel.
  split.
  simpl. rewrite (empty_rel_elem sort X Y). auto. auto.
  simpl. rewrite (union_rel_elem false sort Y).
  apply eq_ord.
  simpl.
  apply (pdom_elem_eq_eq false Y sort).
  simpl. auto.
  destruct a as [x y].
  apply PLT.compose_hom_rel in H.
  destruct H as [q [??]].
  destruct q.
  apply (PLT.pair_hom_rel false _ _ _ _ _ x c c0) in H.
  destruct H.
  simpl in H.
  rewrite (empty_rel_elem sort X Y) in H.
  assert ((empty_elem sort Y, c0, y) ∈ PLT.hom_rel (union false sort Y)).
  revert H0. apply PLT.hom_order; auto.
  split; auto.
  clear c H H0.
  simpl in H2.
  apply (union_rel_elem false sort Y) in H2.
  revert H1. apply PLT.hom_order; auto.
  rewrite H2.
  apply eq_ord.
  apply (pdom_elem_eq_eq false Y sort).
  simpl. auto.
Qed.

Lemma empty_join1 sort (X Y:PLT) :
  join false sort Y ∘ empty sort X (pdomain false sort Y) ≈ empty sort X Y.
Proof.
  split; hnf; intros [x y] ?.
  apply PLT.compose_hom_rel in H.
  destruct H as [q[??]].
  simpl in H. apply (empty_rel_elem sort X) in H.
  simpl in H0. apply (join_rel_elem false sort) in H0.  
  simpl. apply (empty_rel_elem sort).
  rewrite H0.
  clear H0.
  destruct sort.

  hnf; simpl; intros. hnf in H. simpl in *.
  destruct H0 as [x0' [??]].
  apply concat_in in H0.
  destruct H0 as [t [??]].
  apply in_map_iff in H0.   destruct H0 as [t' [??]]. subst t.
  destruct (H t') as [z [??]].
  exists t'; split; auto.
  apply nil_elem in H0. elim H0.

  hnf; simpl; intros. apply nil_elem in H0. elim H0.

  split. 
  hnf; simpl; intros. hnf in H. simpl in *.
  destruct H0 as [x0' [??]].
  apply concat_in in H0.
  destruct H0 as [t [??]].
  apply in_map_iff in H0. destruct H0 as [t' [??]]. subst t.
  destruct H.
  destruct (H t') as [z [??]].
  exists t'; split; auto.
  apply nil_elem in H4. elim H4.
  hnf; simpl; intros. apply nil_elem in H0. elim H0.

  simpl in H. apply (empty_rel_elem sort) in H.
  apply PLT.compose_hom_rel.
  exists (empty_elem sort (pdomain false sort Y)).
  split.
  simpl. apply (empty_rel_elem sort). auto.
  simpl. apply (join_rel_elem false sort).
  rewrite H. clear H.
  destruct sort.

  hnf; simpl; intros.
  apply nil_elem in H. elim H.
  hnf; simpl; intros.
  apply nil_elem in H. elim H.
  split.
  hnf; simpl; intros.
  apply nil_elem in H. elim H.
  hnf; simpl; intros.
  apply nil_elem in H. elim H.
Qed.
  
Lemma empty_join2 sort (X Y:PLT) :
  join false sort Y ∘ pdomain false sort·empty sort X Y 
  ≈ empty sort (pdomain false sort X) Y.
Proof.
  split; hnf; intros [x y] ?.
  apply PLT.compose_hom_rel in H.
  destruct H as [q[??]].
  simpl in H. 
  apply (fmap_rel_elem false _ _ (empty sort X Y) sort) in H.
  simpl in H0. apply (join_rel_elem false sort) in H0.  
  simpl. apply (empty_rel_elem sort).
  rewrite H0.
  clear H0.
  destruct sort.
  
  hnf; simpl; intros. hnf in H. simpl in *.
  destruct H0 as [x0' [??]].
  apply concat_in in H0.
  destruct H0 as [t [??]].
  apply in_map_iff in H0. destruct H0 as [t' [??]]. subst t.
  destruct (H t') as [z [??]].
  exists t'; split; auto.
  rewrite (empty_rel_elem Lower X Y) in H4.
  hnf in H4.
  destruct (H4 x0') as [r [??]].
  exists x0'; split; auto.
  simpl in H5. apply nil_elem in H5. elim H5.

  hnf; simpl; intros. hnf in H. simpl in *.
  apply nil_elem in H0. elim H0.
  
  split.
  hnf; simpl; intros. hnf in H. simpl in *.
  destruct H0 as [x0' [??]].
  apply concat_in in H0.
  destruct H0 as [t [??]].
  apply in_map_iff in H0. destruct H0 as [t' [??]]. subst t.
  destruct H.
  destruct (H t') as [z [??]].
  exists t'; split; auto.
  rewrite (empty_rel_elem Convex X Y) in H5.
  hnf in H5.
  destruct H5.
  destruct (H5 x0') as [r [??]].
  exists x0'; split; auto.
  simpl in H7. apply nil_elem in H7. elim H7.
  hnf; simpl; intros.
  apply nil_elem in H0. elim H0.
  
  simpl in H.
  apply (empty_rel_elem sort) in H.
  apply PLT.compose_hom_rel.
  case_eq (elem false X x). intros.
  exists (empty_elem sort (pdomain false sort Y)).
  split.
  apply (fmap_rel_elem _ _ _ (empty sort X Y) sort).
  destruct sort.

  hnf; simpl; intros.
  apply nil_elem in H1. elim H1.
  hnf; simpl; intros.
  rewrite H0 in H1.
  apply nil_elem in H1. elim H1.
  split.
  hnf; simpl; intros.
  apply nil_elem in H1. elim H1.
  hnf; simpl; intros.
  rewrite H0 in H1.
  apply nil_elem in H1. elim H1.

  simpl. rewrite (join_rel_elem false sort Y).
  simpl.
  rewrite H.
  apply eq_ord.
  apply (pdom_elem_eq_eq false Y sort). simpl. auto.

  intros.
  exists (single_elem false (pdomain false sort Y) (empty_elem sort Y)).
  split.
  simpl.
  apply (fmap_rel_elem _ _ _ (empty sort X Y) sort).
  destruct sort.

  hnf; simpl; intros.
  apply cons_elem in H1. destruct H1.
  2: apply nil_elem in H1; elim H1.
  exists c. split.
  rewrite H0. apply cons_elem; auto.
  apply (empty_rel_elem Lower). auto.
  hnf; simpl; intros.
  exists (empty_elem Upper Y).
  split. apply cons_elem; auto.
  apply (empty_rel_elem Upper). auto.
  split.
  hnf; simpl; intros.
  apply cons_elem in H1. destruct H1.
  2: apply nil_elem in H1; elim H1.
  exists c. split.
  rewrite H0. apply cons_elem; auto.
  apply (empty_rel_elem Convex). auto.
  hnf; simpl; intros.
  exists (empty_elem Convex Y).
  split. apply cons_elem; auto.
  apply (empty_rel_elem Convex). auto.
  
  simpl. rewrite (join_rel_elem false sort Y).
  rewrite H. simpl.
  apply eq_ord.
  apply (pdom_elem_eq_eq false Y sort). simpl. auto.
Qed.

Lemma union_commute_le hf sort (X Y:PLT.PLT hf) (f g:X → pdomain hf sort Y) :
  union hf sort Y ∘ PLT.pair f g ≤
  union hf sort Y ∘ PLT.pair g f.
Proof.
  red; intros [??] ?.
  apply PLT.compose_hom_rel in H.
  apply PLT.compose_hom_rel.
  destruct H as [[q1 q2] [??]].
  exists (q2,q1). split.
  apply (PLT.pair_hom_rel hf _ _ _ f g) in H.
  destruct H.
  apply (PLT.pair_hom_rel hf _ _ _ g f). split; auto.
  simpl in H0. simpl.
  rewrite (union_rel_elem hf sort Y) in H0.
  rewrite (union_rel_elem hf sort Y).
  rewrite H0.
  apply eq_ord.
  apply (pdom_elem_eq_eq hf Y sort). simpl.
  split; hnf; intros.
  apply app_elem in H1. apply app_elem; intuition.
  apply app_elem in H1. apply app_elem; intuition.
Qed.

Lemma union_commute hf sort (X Y:PLT.PLT hf) (f g:X → pdomain hf sort Y) :
  union hf sort Y ∘ PLT.pair f g ≈
  union hf sort Y ∘ PLT.pair g f.
Proof.
  split; apply union_commute_le; auto.
Qed.

Lemma empty_unit2 sort (X Y:PLT) (f:X → pdomain false sort Y) :
  f ≈ union false sort Y ∘ 〈 f, empty sort X Y 〉.
Proof.
  rewrite union_commute. apply empty_unit.
Qed.

Lemma union_idem hf sort (X Y:PLT.PLT hf) (f:X → pdomain hf sort Y) :
  union hf sort Y ∘ PLT.pair f f ≈ f.
Proof.
  split; hnf; simpl; intros [x y] ?.
  apply PLT.compose_hom_rel in H. destruct H as [[q1 q2] [??]].
  apply (PLT.pair_hom_rel _ _ _ _ f f) in H. destruct H.
  simpl in H0.
  rewrite (union_rel_elem hf sort Y) in H0.
  destruct (PLT.hom_directed hf X _ f x (q1::q2::nil)) as [q [??]].
  apply directed.elem_inh with q1. apply cons_elem; auto.
  red; simpl; intros.
  apply cons_elem in H2. destruct H2. rewrite H2.
  apply erel_image_elem. auto.
  apply cons_elem in H2. destruct H2. rewrite H2.
  apply erel_image_elem. auto.
  apply nil_elem in H2. elim H2.
  apply erel_image_elem in H3.

  destruct sort.
  apply PLT.hom_order with x q; auto.
  hnf; intros.
  destruct (H0 x0) as [t [??]]; auto.
  simpl in H5. apply app_elem in H5.
  destruct H5.
  assert (q1 ≤ q). apply H2. apply cons_elem; auto.
  destruct (H7 t) as [s [??]]; auto.
  exists s; split; auto.
  transitivity t; auto.
  assert (q2 ≤ q). apply H2. 
  apply cons_elem; right.
  apply cons_elem; auto.
  destruct (H7 t) as [s [??]]; auto.
  exists s; split; auto.
  transitivity t; auto.

  apply PLT.hom_order with x q1; auto.
  hnf; intros.
  destruct (H0 y0) as [t [??]]; auto.
  simpl. apply app_elem; auto. exists t; split; auto.
  
  apply PLT.hom_order with x q; auto.
  split; hnf; simpl; intros.
  destruct H0.
  destruct (H0 x0) as [t [??]]; auto.
  simpl in H6. apply app_elem in H6. destruct H6.
  assert (q1 ≤ q). apply H2. apply cons_elem; auto.
  destruct H8.
  destruct (H8 t) as [s[??]]; auto.
  exists s; split; auto.
  transitivity t; auto.
  assert (q2 ≤ q). apply H2. 
  apply cons_elem; right.
  apply cons_elem; auto.
  destruct H8.
  destruct (H8 t) as [s[??]]; auto.
  exists s; split; auto.
  transitivity t; auto.
  assert (q1 ≤ q). apply H2. apply cons_elem; auto.
  destruct H5.  
  destruct (H6 y0) as [t [??]]; auto.
  destruct H0.
  destruct (H9 t) as [s[??]]; auto.
  simpl. apply app_elem; auto.
  exists s; split; auto.
  transitivity t; auto.  
  
  apply PLT.compose_hom_rel.    
  exists (y,y). split.
  apply PLT.pair_hom_rel; split; auto.
  simpl. apply union_rel_elem.
  apply eq_ord.
  apply (pdom_elem_eq_eq hf Y sort). simpl.
  split; hnf; intros.
  apply app_elem; auto.
  apply app_elem in H0; destruct H0; auto.
Qed.

Lemma union_lower (X Y:PLT) (f g:X → pdomain false Lower Y) :
  f ≤ union false Lower Y ∘ PLT.pair f g.
Proof.
  intros [x y] ?.
  apply PLT.compose_hom_rel.
  assert (exists y', (x,y') ∈ PLT.hom_rel g).
    destruct (PLT.hom_directed false X _ g x nil).
    simpl; auto.
    red; intros. apply nil_elem in H0. elim H0.
    destruct H0.
    apply erel_image_elem in H1.
    exists x0. auto.

  destruct H0 as [y' ?].
  exists (y,y'). split.
  apply PLT.pair_hom_rel. split; auto.
  simpl.
  apply union_rel_elem.
  hnf. simpl; intros.
  exists x0. split; auto.
  apply app_elem; auto.
Qed.


Lemma union_upper hf (X Y:PLT.PLT hf) (f g:X → pdomain hf Upper Y) :
  f ≥ union hf Upper Y ∘ PLT.pair f g.
Proof.
  intros [x y] ?.
  
  apply PLT.compose_hom_rel in H.
  destruct H as [[??] [??]].
  rewrite (PLT.pair_hom_rel hf _ _ _ f g) in H.
  destruct H.
  simpl in H0.
  apply (union_rel_elem hf Upper Y) in H0.
  hnf in H0.

  apply PLT.hom_order with x c; auto.
  hnf; intros.
  destruct (H0 y0) as [q [??]].
  simpl. apply app_elem; auto.
  eauto.
Qed.


Lemma lower_union_natural1 hf (X Y:PLT.PLT hf) (f:X → Y) :
  union hf Lower Y ∘ PLT.pair_map (pdomain hf Lower·f) (pdomain hf Lower·f)
  ≤
  pdomain hf Lower·f ∘ union hf Lower X.
Proof.
  intros [[a b] z] ?.

  apply PLT.compose_hom_rel in H.
  destruct H as [[y1 y2] [??]].
  unfold PLT.pair_map in H.

  rewrite (PLT.pair_hom_rel hf 
    (powerdomain hf Lower Y)
    (powerdomain hf Lower Y)
    (PLT.prod (powerdomain hf Lower X) (powerdomain hf Lower X))
    _ _ (a,b)) in H.
  destruct H.
  apply PLT.compose_hom_rel in H.
  apply PLT.compose_hom_rel in H1.
  destruct H as [p [??]].
  destruct H1 as [q [??]].
  apply PLT.compose_hom_rel.
  exists (union_elem _ _ a b).
  split.
  simpl. apply union_rel_elem. auto.
  simpl.
  apply (fmap_rel_elem hf X Y f Lower).
  apply (fmap_rel_elem hf X Y f Lower) in H2.
  apply (fmap_rel_elem hf X Y f Lower) in H3.
  simpl in H0.
  rewrite (union_rel_elem hf Lower Y) in H0.

  hnf; simpl; intros.
  simpl in H.
  rewrite (pi1_rel_elem _ _ _ _ a b p) in H.
  simpl in H1.
  rewrite (pi2_rel_elem _ _ _ _ a b q) in H1.
  destruct (H0 b0) as [m [??]]; auto.
  simpl in H5. apply app_elem in H5.
  destruct H5.
  destruct (H2 m) as [n [??]]; auto.
  destruct (H n) as [r [??]]; auto.
  exists r. split.
  apply app_elem; auto.
  apply PLT.hom_order with n m; auto.

  destruct (H3 m) as [n [??]]; auto.
  destruct (H1 n) as [r [??]]; auto.
  exists r. split.
  apply app_elem; auto.
  apply PLT.hom_order with n m; auto.
Qed.

Lemma lower_union_natural2 (X Y:PLT) (f:X → Y) :
  pdomain false Lower·f ∘ union false Lower X ≈
  union false Lower Y ∘ PLT.pair_map (pdomain false Lower·f) (pdomain false Lower·f).
Proof.
  split; intros [[a b] z] ?.
  apply PLT.compose_hom_rel in H.
  apply PLT.compose_hom_rel.
  destruct H as [y [??]].
  simpl in H.
  rewrite (union_rel_elem false Lower X) in H.
  assert ((union_elem false X a b : pdomain false Lower X, z) ∈ PLT.hom_rel (pdomain false Lower·f)).
  apply PLT.hom_order with y z; auto.
  apply (fmap_rel_elem false X Y f Lower) in H1.
    
  assert (exists (ya yb:finset Y),
    (forall q, q ∈ elem _ _ z -> q ∈ ya \/ q ∈ yb) /\
    (forall y, y ∈ ya -> exists x, x ∈ elem _ _ a /\ (x,y) ∈ PLT.hom_rel f) /\
    (forall y, y ∈ yb -> exists x, x ∈ elem _ _ b /\ (x,y) ∈ PLT.hom_rel f)).

    hnf in H1.
    revert H1. generalize (elem _ _ z).
    induction c; simpl; intros.
    exists nil. exists nil.
    intuition.
    apply nil_elem in H2; elim H2.
    apply nil_elem in H2; elim H2.
    destruct IHc as [ya [yb [?[??]]]].
    intros. apply H1. apply cons_elem; auto.
    destruct (H1 a0) as [q [??]]. apply cons_elem; auto.
    apply app_elem in H5. destruct H5.
    exists (a0::ya). exists yb.
    intuition.
    apply cons_elem in H7. destruct H7.
    left. apply cons_elem; auto.
    destruct (H2 q0); auto.
    left. apply cons_elem; auto.
    apply cons_elem in H7. destruct H7.
    exists q. split; auto.
    apply PLT.hom_order with q a0; auto.
    apply H3; auto.
    exists ya. exists (a0::yb).
    intuition.
    apply cons_elem in H7. destruct H7.
    right. apply cons_elem. auto.
    destruct (H2 q0); auto.
    right. apply cons_elem; auto.
    apply cons_elem in H7. destruct H7.
    exists q. split; auto.
    apply PLT.hom_order with q a0; auto.
    apply H4; auto.

  destruct H2 as [ya [yb [?[??]]]].
  exists (PdomElem false _ ya I, PdomElem false _ yb I).
  split.
  apply PLT.pair_hom_rel.  
  split. simpl.
  apply PLT.compose_hom_rel.
  exists a.
  split.
  simpl. apply (pi1_rel_elem _ _ _ _ a b a). auto.
  rewrite (fmap_rel_elem false X Y f Lower).
  simpl. hnf; simpl; intros.
  apply H3. auto.
  simpl.
  apply PLT.compose_hom_rel.
  exists b.
  split.
  simpl. apply (pi2_rel_elem _ _ _ _ a b b). auto.
  rewrite (fmap_rel_elem false X Y f Lower).
  hnf; simpl; intros.
  apply H4. auto.
  simpl.
  simpl. apply (union_rel_elem false Lower Y).
  hnf. simpl; intros.
  destruct (H2 x); auto.
  exists x; split; auto.
  apply app_elem; auto.
  exists x; split; auto.
  apply app_elem; auto.

  apply lower_union_natural1. auto.
Qed.


Lemma upper_union_natural hf (X Y:PLT.PLT hf) (f:X → Y) :
  pdomain hf Upper·f ∘ union hf Upper X ≈
  union hf Upper Y ∘ PLT.pair_map (pdomain hf Upper·f) (pdomain hf Upper·f).
Proof.
  split; intros [[a b] z] ?.
  apply PLT.compose_hom_rel in H.
  apply PLT.compose_hom_rel.
  destruct H as [y [??]].
  simpl in H.
  rewrite (union_rel_elem hf Upper X) in H.
  assert ((union_elem hf X a b : pdomain hf Upper X, z) ∈ PLT.hom_rel (pdomain hf Upper·f)).
  apply PLT.hom_order with y z; auto.
  apply (fmap_rel_elem hf X Y f Upper) in H1.
  hnf in H1. simpl in *.

  assert (exists z1:finset Y,
    (forall x, x ∈ elem hf X a ->
      exists y, y ∈ elem hf Y z /\ y ∈ z1 /\ (x,y) ∈ PLT.hom_rel f) /\
    (forall y, y ∈ z1 -> exists y', y' ∈ elem hf Y z /\ y' ≤ y) /\
    (forall y, y ∈ z1 ->
      exists x, x ∈ elem hf X a /\ (x,y) ∈ PLT.hom_rel f)).

    revert H1. generalize (elem hf X a). induction c; intros.
    exists nil; repeat split; intros.
    apply nil_elem in H2. elim H2.
    apply nil_elem in H2. elim H2.
    apply nil_elem in H2. elim H2.
    destruct IHc as [z1 [?[??]]].
    intros. apply H1. apply cons_elem; auto.
    destruct (H1 a0) as [q [??]]. apply cons_elem; auto.
    clear H1.
    exists (q::z1). repeat split; intros.
    apply cons_elem in H1. destruct H1.
    exists q. split; auto. split. apply cons_elem; auto.
    apply PLT.hom_order with a0 q; auto.
    destruct (H2 x) as [r [?[??]]]; auto.
    exists r; split; auto. split; auto.
    apply cons_elem; auto.
    apply cons_elem in H1. destruct H1.
    exists q. split; auto.
    apply H3; auto.
    apply cons_elem in H1. destruct H1.
    exists a0. split; auto.
    apply cons_elem; auto.
    apply PLT.hom_order with a0 q; auto.
    destruct (H4 y0) as [r [??]]; auto.
    exists r; split; auto. apply cons_elem; auto.
    
  assert (exists z2:finset Y,
    (forall x, x ∈ elem hf X b ->
      exists y, y ∈ elem hf Y z /\ y ∈ z2 /\ (x,y) ∈ PLT.hom_rel f) /\
    (forall y, y ∈ z2 -> exists y', y' ∈ elem hf Y z /\ y' ≤ y) /\

    (forall y, y ∈ z2 ->
      exists x, x ∈ elem hf X b /\ (x,y) ∈ PLT.hom_rel f)).

    clear H2.
    revert H1. generalize (elem hf X b). induction c; intros.
    exists nil; repeat split; intros.
    apply nil_elem in H2. elim H2.
    apply nil_elem in H2. elim H2.
    apply nil_elem in H2. elim H2.
    destruct IHc as [z2 [?[??]]].
    intros. apply H1. 
    apply app_elem in H2. destruct H2.
    apply app_elem; auto.
    apply app_elem; right. apply cons_elem; auto.
    destruct (H1 a0) as [q [??]]. 
    apply app_elem. right. apply cons_elem; auto.
    clear H1.
    exists (q::z2). repeat split; intros.
    apply cons_elem in H1. destruct H1.
    exists q. split; auto. split. apply cons_elem; auto.
    apply PLT.hom_order with a0 q; auto.
    destruct (H2 x) as [r [?[??]]]; auto.
    exists r; split; auto. split; auto.
    apply cons_elem; auto.
    apply cons_elem in H1. destruct H1.
    exists q. split; auto.
    apply H3; auto.
    apply cons_elem in H1. destruct H1.
    exists a0. split; auto.
    apply cons_elem; auto.
    apply PLT.hom_order with a0 q; auto.
    destruct (H4 y0) as [r [??]]; auto.
    exists r; split; auto. apply cons_elem; auto.

  destruct H2 as [z1 [?[??]]].
  destruct H3 as [z2 [?[??]]].
  
  assert (inh hf z1).
  generalize (elem_inh hf X a).
  pattern hf at 2 6. case hf; simpl; auto.
  intros [??]. destruct (H2 x) as [q [?[??]]]; eauto.
  assert (inh hf z2).
  generalize (elem_inh hf X b).
  pattern hf at 2 6. case hf; simpl; auto.
  intros [??]. destruct (H3 x) as [q [?[??]]]; eauto.
  exists (PdomElem hf Y z1 H8, PdomElem hf Y z2 H9).
  split.
  apply PLT.pair_hom_rel. split; apply PLT.compose_hom_rel.
  exists a; split.
  simpl. 
  apply (pi1_rel_elem (pdomain hf Upper X) (pdomain hf Upper X) _ _ a b a). auto.
  rewrite (fmap_rel_elem hf X Y f Upper).
  simpl. hnf; simpl; intros.
  destruct (H2 a0) as [q [?[??]]]; eauto.
  exists b. split.
  simpl. apply (pi2_rel_elem (pdomain hf Upper X) (pdomain hf Upper X) _ _ a b b). auto.
  rewrite (fmap_rel_elem hf X Y f Upper).
  simpl. hnf; simpl; intros.
  destruct (H3 a0) as [q [?[??]]]; eauto.
  simpl. apply union_rel_elem.
  hnf; simpl; intros.
  apply app_elem in H10. destruct H10; eauto.


  apply PLT.compose_hom_rel in H.
  destruct H as [[y1 y2] [??]].
  unfold PLT.pair_map in H.

  rewrite (PLT.pair_hom_rel hf (powerdomain hf Upper Y) (powerdomain hf Upper Y)
    (PLT.prod (powerdomain hf Upper X) (powerdomain hf Upper X))
    _ _ (a,b)) in H.
  destruct H.
  apply PLT.compose_hom_rel in H.
  apply PLT.compose_hom_rel in H1.
  destruct H as [p [??]].
  destruct H1 as [q [??]].
  apply PLT.compose_hom_rel.
  exists (union_elem _ _ a b).
  split.
  simpl. apply union_rel_elem. auto.
  simpl.
  apply (fmap_rel_elem hf X Y f Upper).
  apply (fmap_rel_elem hf X Y f Upper) in H2.
  apply (fmap_rel_elem hf X Y f Upper) in H3.
  simpl in H0.
  rewrite (union_rel_elem hf Upper Y) in H0.

  hnf; simpl; intros.
  simpl in H.
  rewrite (pi1_rel_elem _ _ _ _ a b p) in H.
  simpl in H1.
  rewrite (pi2_rel_elem _ _ _ _ a b q) in H1.
  apply app_elem in H4. destruct H4.

  destruct (H a0) as [m [??]]; auto.
  destruct (H2 m) as [n [??]]; auto.
  destruct (H0 n) as [r [??]]; auto.
  simpl. apply app_elem; auto.
  exists r. split; auto.
  apply PLT.hom_order with m n; auto.

  destruct (H1 a0) as [m [??]]; auto.
  destruct (H3 m) as [n [??]]; auto.
  destruct (H0 n) as [r [??]]; auto.
  simpl. apply app_elem; auto.
  exists r. split; auto.
  apply PLT.hom_order with m n; auto.
Qed.

Lemma convex_union_natural hf (X Y:PLT.PLT hf) (f:X → Y) :
  pdomain hf Convex·f ∘ union hf Convex X ≈
  union hf Convex Y ∘ PLT.pair_map (pdomain hf Convex·f) (pdomain hf Convex·f).
Proof.
  split; intros [[a b] z] ?.
  apply PLT.compose_hom_rel in H.
  apply PLT.compose_hom_rel.
  destruct H as [y [??]].
  simpl in H.
  rewrite (union_rel_elem hf Convex X) in H.
  assert ((union_elem hf X a b : pdomain hf Convex X, z) ∈ PLT.hom_rel (pdomain hf Convex·f)).
  apply PLT.hom_order with y z; auto.
  apply (fmap_rel_elem hf X Y f Convex) in H1.
  hnf in H1. simpl in *.

  assert (exists z1:finset Y , exists z2:finset Y,
    (forall x, x ∈ elem hf X a ->
      exists y, y ∈ elem hf Y z /\ y ∈ z1 /\ (x,y) ∈ PLT.hom_rel f) /\
    (forall y, y ∈ z1 -> y ∈ elem hf Y z) /\
    (forall y, y ∈ z1 ->
      exists x, x ∈ elem hf X a /\ (x,y) ∈ PLT.hom_rel f) /\
    (forall x, x ∈ elem hf X b ->
      exists y, y ∈ elem hf Y z /\ y ∈ z2 /\ (x,y) ∈ PLT.hom_rel f) /\
    (forall y, y ∈ z2 -> y ∈ elem hf Y z) /\
    (forall y, y ∈ z2 ->
      exists x, x ∈ elem hf X b /\ (x,y) ∈ PLT.hom_rel f) /\
    (forall y, y ∈ elem hf Y z -> y ∈ z1 \/ y ∈ z2)).

  assert (forall ys:finset Y,
    (forall y, y ∈ ys -> y ∈ elem hf Y z /\
      exists x, x ∈ elem hf X (union_elem hf X a b) /\ (x,y) ∈ PLT.hom_rel f)
    ->
    exists z1:finset Y , exists z2:finset Y,
    (forall x, x ∈ elem hf X a ->
      exists y, y ∈ elem hf Y z /\ y ∈ z1 /\ (x,y) ∈ PLT.hom_rel f) /\
    (forall y, y ∈ z1 -> y ∈ elem hf Y z) /\
    (forall y, y ∈ z1 ->
      exists x, x ∈ elem hf X a /\ (x,y) ∈ PLT.hom_rel f) /\
    (forall x, x ∈ elem hf X b ->
      exists y, y ∈ elem hf Y z /\ y ∈ z2 /\ (x,y) ∈ PLT.hom_rel f) /\
    (forall y, y ∈ z2 -> y ∈ elem hf Y z) /\
    (forall y, y ∈ z2 ->
      exists x, x ∈ elem hf X b /\ (x,y) ∈ PLT.hom_rel f) /\
    (forall y, y ∈ ys -> y ∈ z1 \/ y ∈ z2)).

    induction ys. intros. clear H2. destruct H1 as [_ H1]. hnf in H1. simpl in H1.

    assert (exists z1:finset Y,
    (forall x, x ∈ elem hf X a ->
      exists y, y ∈ elem hf Y z /\ y ∈ z1 /\ (x,y) ∈ PLT.hom_rel f) /\
    (forall y, y ∈ z1 -> y ∈ elem hf Y z) /\
    (forall y, y ∈ z1 ->
      exists x, x ∈ elem hf X a /\ (x,y) ∈ PLT.hom_rel f)).

    revert H1. generalize (elem hf X a). induction c; intros.
    exists nil; repeat split; intros.
    apply nil_elem in H2. elim H2.
    apply nil_elem in H2. elim H2.
    apply nil_elem in H2. elim H2.
    destruct IHc as [z1 [?[??]]].
    intros. apply H1. apply cons_elem; auto.
    destruct (H1 a0) as [q [??]]. apply cons_elem; auto.
    clear H1.
    exists (q::z1). repeat split; intros.
    apply cons_elem in H1. destruct H1.
    exists q. split; auto. split. apply cons_elem; auto.
    apply PLT.hom_order with a0 q; auto.
    destruct (H2 x) as [r [?[??]]]; auto.
    exists r; split; auto. split; auto.
    apply cons_elem; auto.
    apply cons_elem in H1. destruct H1.
    rewrite H1; auto. auto.
    apply cons_elem in H1. destruct H1.
    exists a0. split; auto.
    apply cons_elem; auto.
    apply PLT.hom_order with a0 q; auto.
    destruct (H4 y0) as [r [??]]; auto.
    exists r; split; auto. apply cons_elem; auto.

  assert (exists z2:finset Y,
    (forall x, x ∈ elem hf X b ->
      exists y, y ∈ elem hf Y z /\ y ∈ z2 /\ (x,y) ∈ PLT.hom_rel f) /\
    (forall y, y ∈ z2 -> y ∈ elem hf Y z) /\
    (forall y, y ∈ z2 ->
      exists x, x ∈ elem hf X b /\ (x,y) ∈ PLT.hom_rel f)).

    clear H2.
    revert H1. generalize (elem hf X b). induction c; intros.
    exists nil; repeat split; intros.
    apply nil_elem in H2. elim H2.
    apply nil_elem in H2. elim H2.
    apply nil_elem in H2. elim H2.
    destruct IHc as [z2 [?[??]]].
    intros. apply H1. 
    apply app_elem in H2. destruct H2.
    apply app_elem; auto.
    apply app_elem; right. apply cons_elem; auto.
    destruct (H1 a0) as [q [??]]. 
    apply app_elem. right. apply cons_elem; auto.
    clear H1.
    exists (q::z2). repeat split; intros.
    apply cons_elem in H1. destruct H1.
    exists q. split; auto. split. apply cons_elem; auto.
    apply PLT.hom_order with a0 q; auto.
    destruct (H2 x) as [r [?[??]]]; auto.
    exists r; split; auto. split; auto.
    apply cons_elem; auto.
    apply cons_elem in H1. destruct H1.
    rewrite H1; auto. auto.
    apply cons_elem in H1. destruct H1.
    exists a0. split; auto.
    apply cons_elem; auto.
    apply PLT.hom_order with a0 q; auto.
    destruct (H4 y0) as [r [??]]; auto.
    exists r; split; auto. apply cons_elem; auto.

    destruct H2 as [z1 [?[??]]].   
    destruct H3 as [z2 [?[??]]].   
    exists z1. exists z2. intuition.
    apply nil_elem in H8. elim H8.
    
    intros.
    destruct IHys as [z1 [z2 [?[?[?[?[??]]]]]]].
    intros. apply H2. apply cons_elem; auto.
    destruct (H2 a0) as [?[q [??]]]. apply cons_elem; auto. clear H2.
    simpl in H10. apply app_elem in H10. destruct H10.
    exists (a0::z1). exists z2.
    intuition.
    destruct (H3 x) as [m [?[??]]]; auto.
    exists m. split; auto. split; auto. apply cons_elem; auto.
    apply cons_elem in H8. destruct H8; auto.
    rewrite H8; auto.    
    apply cons_elem in H8. destruct H8.
    exists q. split; auto.
    apply PLT.hom_order with q a0; auto.
    auto.
    apply cons_elem in H8. destruct H8.
    left. apply cons_elem; auto.
    destruct (H13 y0); auto.
    left. apply cons_elem; auto.
    exists z1. exists (a0::z2).
    intuition.
    destruct (H6 x) as [m [?[??]]]; auto.
    exists m. split; auto. split; auto. apply cons_elem; auto.
    apply cons_elem in H8. destruct H8; auto.
    rewrite H8; auto.    
    apply cons_elem in H8. destruct H8.
    exists q. split; auto.
    apply PLT.hom_order with q a0; auto.
    auto.
    apply cons_elem in H8. destruct H8.
    right. apply cons_elem; auto.
    destruct (H13 y0); auto.
    right. apply cons_elem; auto.

  apply (H2 (elem hf Y z)). destruct H1; auto.

  destruct H2 as [z1 [z2 [?[?[?[?[?[??]]]]]]]].
  
  assert (inh hf z1).
  generalize (elem_inh hf X a).
  pattern hf at 2 6. case hf; simpl; auto.
  intros [??]. destruct (H2 x) as [q [?[??]]]; eauto.
  assert (inh hf z2).
  generalize (elem_inh hf X b).
  pattern hf at 2 6. case hf; simpl; auto.
  intros [??]. destruct (H5 x) as [q [?[??]]]; eauto.
  exists (PdomElem hf Y z1 H9, PdomElem hf Y z2 H10).
  split.
  apply PLT.pair_hom_rel. split; apply PLT.compose_hom_rel.
  exists a; split.
  simpl. 
  apply (pi1_rel_elem (pdomain hf Convex X) (pdomain hf Convex X) _ _ a b a). auto.
  rewrite (fmap_rel_elem hf X Y f Convex).
  split; hnf; simpl; intros; auto.
  destruct (H2 a0) as [q [?[??]]]; eauto.
  exists b. split.
  simpl. apply (pi2_rel_elem (pdomain hf Convex X) (pdomain hf Convex X) _ _ a b b). auto.
  rewrite (fmap_rel_elem hf X Y f Convex).
  split; hnf; simpl; intros; auto.
  destruct (H5 a0) as [q [?[??]]]; eauto.
  simpl. apply union_rel_elem.
  split; hnf; simpl; intros.
  exists x. split; auto. apply app_elem.
  apply H8. auto.
  apply app_elem in H11. destruct H11; eauto.

  apply PLT.compose_hom_rel in H.
  destruct H as [[y1 y2] [??]].
  unfold PLT.pair_map in H.

  rewrite (PLT.pair_hom_rel hf (powerdomain hf Convex Y) (powerdomain hf Convex Y)
    (PLT.prod (powerdomain hf Convex X) (powerdomain hf Convex X))
    _ _ (a,b)) in H.
  destruct H.
  apply PLT.compose_hom_rel in H.
  apply PLT.compose_hom_rel in H1.
  destruct H as [p [??]].
  destruct H1 as [q [??]].
  apply PLT.compose_hom_rel.
  exists (union_elem _ _ a b).
  split.
  simpl. apply union_rel_elem. auto.
  simpl.
  apply (fmap_rel_elem hf X Y f Convex).
  apply (fmap_rel_elem hf X Y f Convex) in H2.
  apply (fmap_rel_elem hf X Y f Convex) in H3.
  simpl in H0.
  rewrite (union_rel_elem hf Convex Y) in H0.

  hnf; simpl; intros.
  simpl in H.
  rewrite (pi1_rel_elem _ _ _ _ a b p) in H.
  simpl in H1.
  rewrite (pi2_rel_elem _ _ _ _ a b q) in H1.
  split; hnf; simpl; intros.

  destruct H0 as [? _].
  destruct (H0 b0) as [m [??]]; auto.
  simpl in H5. apply app_elem in H5.
  destruct H5.
  destruct H2 as [? _].
  destruct (H2 m) as [n [??]]; auto.
  destruct H as [? _].
  destruct (H n) as [r [??]]; auto.
  exists r. split.
  apply app_elem; auto.
  apply PLT.hom_order with n m; auto.
  destruct H3 as [? _].
  destruct (H3 m) as [n [??]]; auto.
  destruct H1 as [? _].
  destruct (H1 n) as [r [??]]; auto.
  exists r. split.
  apply app_elem; auto.
  apply PLT.hom_order with n m; auto.

  apply app_elem in H4. destruct H4.
  destruct H as [_ H].
  destruct (H a0) as [m [??]]; auto.
  destruct H2 as [_ H2].
  destruct (H2 m) as [n [??]]; auto.
  destruct H0 as [_ H0].
  destruct (H0 n) as [r [??]]; auto.
  simpl. apply app_elem; auto.
  exists r. split; auto.
  apply PLT.hom_order with m n; auto.

  destruct H1 as [_ H1].
  destruct (H1 a0) as [m [??]]; auto.
  destruct H3 as [_ H3].
  destruct (H3 m) as [n [??]]; auto.
  destruct H0 as [_ H0].
  destruct (H0 n) as [r [??]]; auto.
  simpl. apply app_elem; auto.
  exists r. split; auto.
  apply PLT.hom_order with m n; auto.
Qed.


End powerdom.

Notation powerdomain := powerdom.pdomain.

Section powerdom_functor.
  Variable hf:bool.
  Variable sort:pdom_sort.
  Variables X Y:PLT.PLT hf.

  Program Definition pdom_map (f:X ⇀ Y) 
    (x:powerdomain hf sort X) : powerdomain hf sort Y
    := powerdom.PdomElem hf Y (map f (powerdom.elem _ _ x)) _.
  Next Obligation.
    intros. generalize (powerdom.elem_inh _ _ x).
    destruct hf; simpl; auto.
    intros [q ?]. destruct H as [q' [??]].
    exists (f q'). exists (f q'). split; auto.
    apply in_map. auto.
  Qed.

  Lemma pdom_map_lower_ord  (f:X⇀Y) :
    forall a b, 
      powerdom.lower_ord hf X a b <-> 
      powerdom.lower_ord hf Y (pdom_map f a) (pdom_map f b).
  Proof.
    unfold powerdom.lower_ord; simpl; intuition.
    destruct H0 as [x' [??]].
    apply in_map_iff in H0.
    destruct H0 as [q [??]].
    subst x'.
    destruct (H q) as [q' [??]].
    exists q; split; auto.
    destruct H0 as [q'' [??]].
    exists (f q''). split; auto.
    exists (f q''). split; auto.
    apply in_map. auto.
    rewrite H1.
    apply embed_mono.
    rewrite <- H4; auto.
    destruct H0 as [x' [??]].
    destruct (H (f x')) as [y [??]].
    exists (f x'). split; auto. apply in_map; auto.
    destruct H2 as [y' [??]].    
    apply in_map_iff in H2.
    destruct H2 as [x'' [??]]. subst y'.
    exists x''. split; auto.
    exists x''; split; auto.
    rewrite H1; auto.
    apply (embed_reflects f).
    rewrite H3; auto.
  Qed.
  
  Lemma pdom_map_upper_ord  (f:X⇀Y) :
    forall a b, 
      powerdom.upper_ord hf X a b <-> 
      powerdom.upper_ord hf Y (pdom_map f a) (pdom_map f b).
  Proof.
    unfold powerdom.upper_ord. intuition.
    destruct H0 as [y' [??]].
    simpl in H0.
    apply in_map_iff in H0.
    destruct H0 as [x [??]]. subst y'.
    destruct (H x) as [q [??]].   
    exists x; split; auto.
    destruct H0 as [q' [??]].
    exists (f q'). split.
    exists (f q'). split; auto.
    apply in_map. auto.
    rewrite H1.
    apply embed_mono. rewrite <- H4; auto.

    destruct H0 as [y' [??]].
    destruct (H (f y')) as [q [??]].
    exists (f y'). simpl. split; auto.
    apply in_map. auto.
    destruct H2 as [q' [??]].
    simpl in H2.
    apply in_map_iff in H2.
    destruct H2 as [q'' [??]]. subst q'.
    exists q''. split.
    exists q''. split; auto.
    rewrite H4 in H3.
    apply embed_reflects in H3. rewrite H1. auto.
  Qed.

  Program Definition pdom_fmap (f:X ⇀ Y) :
    powerdomain hf sort X ⇀ powerdomain hf sort Y
    := Embedding hf _ _ (pdom_map f) _ _ _ _.
  Next Obligation.
    intros. destruct sort.
    apply pdom_map_lower_ord. auto.
    apply pdom_map_upper_ord. auto.
    destruct H; split.
    apply pdom_map_lower_ord. auto.
    apply pdom_map_upper_ord. auto.
  Qed.
  Next Obligation.
    intros. destruct sort.
    red in H. simpl in H.
    rewrite <- (pdom_map_lower_ord f a) in H. auto.
    red in H. simpl in H.
    rewrite <- (pdom_map_upper_ord f a) in H. auto.
    destruct H. split.
    rewrite <- (pdom_map_lower_ord f a) in H. auto.
    rewrite <- (pdom_map_upper_ord f a) in H0. auto.
  Qed.
  Next Obligation.
    intros. generalize (refl_equal hf).
    pattern hf at 1 3. case hf; intros. auto.
    destruct y. simpl.
    assert (exists (xs:finset X),
      (forall x, In x xs -> exists y, In y elem /\ f x ≤ y) /\
      (forall y, In y elem -> exists x, In x xs /\ f x ≤ y)).
    generalize (embed_directed0 f).
    pattern hf at 2. rewrite <- H. intros.
    clear elem_inh. induction elem.
    exists nil. simpl; intuition.
    destruct IHelem as [xs [??]].
    destruct (H0 a) as [q ?].
    exists (q::xs). simpl; intuition; subst; eauto.
    destruct (H1 x) as [y [??]]; auto.
    exists y; split; auto.
    destruct (H2 y) as [x [??]]; auto.
    exists x; split; auto.
    destruct H0 as [xs [??]].
    assert (inh hf xs).
    rewrite <- H at 2. red. auto.
    exists (powerdom.PdomElem hf X xs H2).
    destruct sort; hnf; simpl; intros.
    destruct H3 as [x' [??]].
    apply in_map_iff in H3. destruct H3 as [q [??]].
    subst x'.
    destruct (H0 q) as [q' [??]]; auto.
    exists q'. split. exists q'; split; auto. rewrite H4. auto.
    destruct H3 as [y' [??]].
    destruct (H1 y') as [q' [??]]. auto.
    exists (f q'). split; auto.
    exists (f q'); split; auto.
    apply in_map; auto.
    rewrite H4; auto.

    split. hnf; simpl; intros.
    destruct H3 as [x' [??]].
    apply in_map_iff in H3. destruct H3 as [q [??]]. subst x'.
    destruct (H0 q) as [q' [??]]; auto.
    exists q'; split; auto.
    exists q'; split; auto. rewrite H4. auto.
    hnf; simpl; intros.
    destruct H3 as [x' [??]].
    destruct (H1 x') as [q [??]]. auto.
    exists (f q). split; auto.
    exists (f q). split; auto.
    apply in_map. auto.
    rewrite H4; auto.    
  Qed.
  Next Obligation.
    intros.

    set (M := a :: b :: nil).
    set (Q m := 
      (exists n, n ∈ powerdom.elem _ _ a /\ n ≤ m) /\
      (exists n, n ∈ powerdom.elem _ _ b /\ n ≤ m) /\
      (exists n, n ∈ powerdom.elem _ _ y /\ f m ≤ n)).

    assert (Hqelems : exists qelems:finset X,
      forall m, m ∈ qelems <-> Q m /\ 
        m ∈ powerdom.all_tokens hf X (PLT.plotkin X) sort M).
  
      assert (Qdec : forall m, {Q m}+{~Q m}).
      intro m. unfold Q. apply dec_conj.
      destruct (finset_find_dec _ (fun n => n ≤ m)) with (powerdom.elem _ _ a).
      intros. rewrite <- H1; auto.
      intro. apply (eff_ord_dec X (PLT.effective X)).
      left. destruct s; eauto.
      right. intros [??]. apply (n x); auto.
      destruct H1; auto. destruct H1; auto.
      apply dec_conj.
      destruct (finset_find_dec _ (fun n => n ≤ m)) with (powerdom.elem _ _ b).
      intros. rewrite <- H1; auto.
      intro. apply (eff_ord_dec X (PLT.effective X)).
      left. destruct s; eauto.
      right. intros [??]. apply (n x); auto.
      destruct H1; auto. destruct H1; auto.
      destruct (finset_find_dec _ (fun n => f m ≤ n)) with (powerdom.elem _ _ y).
      intros. rewrite <- H1; auto.
      intro. apply (eff_ord_dec Y (PLT.effective Y)).
      left. destruct s; eauto.
      right. intros [??]. apply (n x); auto.
      destruct H1; auto. destruct H1; auto.

      exists (finsubset X Q Qdec (powerdom.all_tokens hf X (PLT.plotkin X) sort M)).
      intro. rewrite finsubset_elem. intuition.
      intros. destruct H2 as [?[??]].
      split.
      destruct H2 as [n [??]]. exists n. rewrite <- H1; auto.
      split.
      destruct H3 as [n [??]]. exists n. rewrite <- H1; auto.
      destruct H4 as [n [??]]. exists n. rewrite <- H1; auto.

    destruct Hqelems as [qelems Hq].

    assert (Hq' : forall qa qb qy,
      qa ∈ powerdom.elem _ _ a ->
      qb ∈ powerdom.elem _ _ b ->
      qy ∈ powerdom.elem _ _ y ->
      f qa ≤ qy -> f qb ≤ qy ->
      exists q, q ∈ qelems /\ qa ≤ q /\ qb ≤ q /\ f q ≤ qy).
      
      intros.
      destruct (embed_directed2 f qy qa qb) as [q [?[??]]]; auto.
      destruct (mub_complete (PLT.plotkin X) (qa::qb::nil) q) as [q0 [??]].
      apply elem_inh with qa. apply cons_elem; auto.
      apply ub_cons; auto. apply ub_cons; auto. apply ub_nil.
      exists q0. split.
      apply Hq.
      split. split.
      exists qa. split. auto.
      apply H9. apply cons_elem; auto.
      split.
      exists qb. split. auto.
      apply H9. apply cons_elem; right. apply cons_elem; auto.
      exists qy. split; auto.
      transitivity (f q); auto.
      apply embed_mono. auto.
      unfold powerdom.all_tokens.
      apply (mub_clos_mub (PLT.plotkin X)  _ (qa::qb::nil)); auto.
      eapply elem_inh. apply cons_elem; auto.
      apply cons_subset; auto.
      apply mub_clos_incl.
      simpl.
      apply app_elem.
      left. auto.
      apply cons_subset; auto.
      apply mub_clos_incl.
      simpl.
      apply app_elem. right.
      apply app_elem. left.
      auto.
      apply nil_subset.
      split; auto.
      apply H9. apply cons_elem; auto.
      split.
      apply H9. 
      apply cons_elem; right.
      apply cons_elem; auto.
      transitivity (f q); auto.
      apply embed_mono; auto.

    assert (Hq'':sort <> Lower -> inh hf qelems).
      generalize (refl_equal hf).
      pattern hf at 1 4. case hf; intros; hnf; auto.
      destruct sort. elim H2; auto.

      generalize (powerdom.elem_inh _ _ y).
      pattern hf at 2. rewrite <- H1.
      intros [q ?].
      destruct (H q) as [q1 [??]]; auto.
      destruct (H0 q) as [q2 [??]]; auto.
      simpl in H4. simpl in H6.
      destruct H4 as [q1' [??]].
      destruct H6 as [q2' [??]].
      apply in_map_iff in H4.
      destruct H4 as [qa [??]]. subst q1'.
      apply in_map_iff in H6.
      destruct H6 as [qb [??]]. subst q2'.

      destruct (Hq' qa qb q) as [q0 [?[?[??]]]]; auto.
      exists qa; split; auto.
      exists qb; split; auto.
      rewrite <- H8; auto.
      rewrite <- H9; auto.
      exists q0; auto.

      generalize (powerdom.elem_inh _ _ a).
      pattern hf at 2. rewrite <- H1.
      intros [qa ?].
      destruct H as [H H'].
      destruct H0 as [H0 H0'].
      destruct H3 as [qa' [??]].
      destruct (H (f qa')) as [q [??]]; auto.
      simpl. exists (f qa'). split; auto.
      apply in_map. auto.
      destruct (H0' q) as [zb [??]]; auto.
      simpl in H7.
      destruct H7 as [zb' [??]].
      apply in_map_iff in H7.
      destruct H7 as [qb [??]]. subst zb'.
      rewrite H9 in H8. clear zb H9.
      destruct (Hq' qa' qb q) as [q0 [?[?[??]]]]; auto.
      exists qa'; split; auto.
      exists qb; split; auto.
      exists q0; auto.

    destruct sort.

    exists (powerdom.union_elem _ _ a b).
    split.
    hnf; simpl; intros.
    destruct H1 as [x' [??]].
    rewrite map_app in H1.
    apply in_app_or in H1. destruct H1.
    destruct (H x') as [q [??]]; auto.
    exists x'. split; auto.
    exists q; split; auto.
    rewrite H2; auto.
    destruct (H0 x') as [q [??]]; auto.
    exists x'; split; auto.
    exists q; split; auto. rewrite H2; auto.
    split; hnf; simpl; intros.
    exists x. split; auto.
    apply app_elem; auto.
    exists x. split; auto.
    apply app_elem; auto.

    assert (inh hf qelems).
    apply Hq''; auto. discriminate.
    exists (powerdom.PdomElem _ _ qelems H1).
    split; hnf; simpl; intros.
    destruct (H y0) as [qa [??]]; auto.
    destruct (H0 y0) as [qb [??]]; auto.
    destruct H3 as [qa' [??]].
    destruct H5 as [qb' [??]].
    simpl in H3.
    apply in_map_iff in H3.
    destruct H3 as [za [??]]. subst qa'.
    simpl in H5.
    apply in_map_iff in H5.
    destruct H5 as [zb [??]]. subst qb'.
    destruct (Hq' za zb y0) as [q0 [?[?[??]]]].
    exists za; split; auto.
    exists zb; split; auto.
    auto.
    rewrite <- H7; auto.
    rewrite <- H8; auto.
    destruct H3 as [q0' [??]].
    exists (f q0'); split; auto.
    exists (f q0'); split; auto.
    apply in_map. auto.
    transitivity (f q0); auto.
    apply embed_mono; auto.
    split; hnf; simpl; intros.
    apply Hq in H2.
    destruct H2 as [[?[??]] ?].
    auto.
    apply Hq in H2.
    destruct H2 as [[?[??]] ?].
    auto.

    assert (inh hf qelems).
    apply Hq''; auto. discriminate.
    exists (powerdom.PdomElem _ _ qelems H1).
    destruct H. destruct H0.

    split; hnf; simpl; intros.
    split; hnf; simpl; intros.
    destruct H4 as [x' [??]].        
    apply in_map_iff in H4. destruct H4 as [q [??]]. subst x'.
    assert (q ∈ qelems). exists q; split; auto.
    apply Hq in H4.
    destruct H4 as [[?[??]] ?].
    destruct H8 as [qy [??]].
    exists qy. split; auto.
    rewrite H5. auto.
    destruct (H2 y0) as [qa [??]]; auto.
    destruct (H3 y0) as [qb [??]]; auto.
    destruct H5 as [qa' [??]].
    destruct H7 as [qb' [??]].
    simpl in H5.
    apply in_map_iff in H5.
    destruct H5 as [za [??]]. subst qa'.
    simpl in H7.
    apply in_map_iff in H7.
    destruct H7 as [zb [??]]. subst qb'.
    destruct (Hq' za zb y0) as [q0 [?[?[??]]]]; auto.
    exists za; split; auto.
    exists zb; split; auto.
    rewrite <- H9; auto.
    rewrite <- H10; auto.
    destruct H5 as [q0' [??]].
    exists (f q0'). split.
    exists (f q0'). split; auto.
    apply in_map. auto.
    transitivity (f q0); auto.
    apply embed_mono; auto.
    split.
    split; hnf; simpl; intros.
    destruct H4 as [x' [??]].
    destruct (H (f x')) as [qy [??]]; auto.
    exists (f x'). split; auto. apply in_map; auto.
    destruct (H3 qy) as [qb [??]]; auto.
    destruct H8 as [qb' [??]].
    simpl in H8.
    apply in_map_iff in H8.
    destruct H8 as [zb [??]]. subst qb'.
    destruct (Hq' x' zb qy) as [q0 [?[?[??]]]]; auto.
    exists x'; split; auto.
    exists zb; split; auto.    
    rewrite <- H10; auto.
    exists q0. split; auto.
    rewrite H5; auto.
    apply Hq in H4.   
    destruct H4 as [[?[??]] ?]. auto.
    split; hnf; simpl; intros.
    destruct H4 as [x' [??]].
    destruct (H0 (f x')) as [qy [??]]; auto.
    exists (f x'). split; auto. apply in_map; auto.
    destruct (H2 qy) as [qa [??]]; auto.
    destruct H8 as [qa' [??]].
    simpl in H8. apply in_map_iff in H8. destruct H8 as [za [??]]. subst qa'.
    rewrite H10 in H9.
    destruct (Hq' za x' qy) as [q0 [?[?[??]]]]; auto.
    exists za; split; auto. 
    exists x'; split; auto.
    exists q0; split; auto.
    rewrite H5; auto.
    apply Hq in H4.
    destruct H4 as [[?[??]] ?]; auto.
  Qed.
End powerdom_functor.


Program Definition powerdomainF (hf:bool) (sort:pdom_sort) :
  functor (EMBED hf) (EMBED hf) :=
  Functor (EMBED hf) (EMBED hf) 
    (powerdomain hf sort)
    (pdom_fmap hf sort)
    _ _ _.
Next Obligation.
  intros.
  split; hnf; simpl; intros.
  apply (powerdom.pdom_elem_eq_le hf A sort).
  simpl.
  generalize (powerdom.elem hf A x).
  induction c; simpl; auto.
  split; hnf; simpl; intros.
  apply cons_elem in H0.
  apply cons_elem. intuition; auto.
  rewrite H in H1. simpl in H1. auto.
  rewrite IHc in H1. auto.
  apply cons_elem in H0.
  apply cons_elem. intuition.
  left. rewrite H. auto.
  right. rewrite IHc; auto.
  apply (powerdom.pdom_elem_eq_le hf A sort).

  simpl.
  generalize (powerdom.elem hf A x).
  induction c; simpl; auto.
  split; hnf; simpl; intros.
  apply cons_elem in H0.
  apply cons_elem. intuition; auto.
  left. rewrite H. auto.
  right. rewrite <- IHc; auto.
  apply cons_elem in H0.
  apply cons_elem. intuition.
  left. rewrite H in H1. auto.
  right. rewrite IHc. auto.
Qed.
Next Obligation.
  intros.
  split; hnf; simpl; intros.
  apply (powerdom.pdom_elem_eq_le hf C sort).
  simpl.
  generalize (powerdom.elem hf A x).
  intros.
  induction c; simpl; auto.
  split; hnf; simpl; intros.
  apply cons_elem in H0.
  apply cons_elem. intuition; auto.
  rewrite H in H1. simpl in H1. auto.
  rewrite IHc in H1. auto.
  apply cons_elem in H0.
  apply cons_elem. intuition.
  left. rewrite H. auto.
  right. rewrite IHc; auto.

  apply (powerdom.pdom_elem_eq_le hf C sort).
  simpl.
  generalize (powerdom.elem hf A x).
  induction c; simpl; auto.
  split; hnf; simpl; intros.
  apply cons_elem in H0.
  apply cons_elem. intuition; auto.
  left. rewrite H. auto.
  right. rewrite <- IHc; auto.
  apply cons_elem in H0.
  apply cons_elem. intuition.
  left. rewrite H in H1. auto.
  right. rewrite IHc. auto.
Qed.
Next Obligation.
  intros.
  split; hnf; simpl; intros.
  apply (powerdom.pdom_elem_eq_le hf B sort).
  simpl.
  generalize (powerdom.elem hf A x).
  intros.
  induction c; simpl; auto.
  split; hnf; simpl; intros.
  apply cons_elem in H0.
  apply cons_elem. intuition; auto.
  rewrite H in H1. simpl in H1. auto.
  rewrite IHc in H1. auto.
  apply cons_elem in H0.
  apply cons_elem. intuition.
  left. rewrite H. auto.
  right. rewrite IHc; auto.

  apply (powerdom.pdom_elem_eq_le hf B sort).
  simpl.
  generalize (powerdom.elem hf A x).
  induction c; simpl; auto.
  split; hnf; simpl; intros.
  apply cons_elem in H0.
  apply cons_elem. intuition; auto.
  left. rewrite H. auto.
  right. rewrite <- IHc; auto.
  apply cons_elem in H0.
  apply cons_elem. intuition.
  left. rewrite H in H1. auto.
  right. rewrite IHc. auto.
Qed.

Require Import cont_functors.
Require Import bilimit.

Section powerdom_decompose.
  Variable hf:bool.
  Variable I:directed_preord.
  Variables DS : directed_system I (EMBED hf).
  Variable CC : cocone DS.

  Hypothesis decompose : forall x:cocone_point CC,
    { i:I & { a:ds_F DS i | cocone_spoke CC i a ≈ x }}.

  Lemma finset_decompose
    (X:finset (PLT.ord (cocone_point CC))) :
    { k:I & { Y:finset (PLT.ord (ds_F DS k)) |
       X ≈ map (cocone_spoke CC k) Y }}.
  Proof.
    induction X.
    destruct (choose_ub_set I nil). exists x.
    exists nil. simpl. auto.
    destruct IHX as [k [Y ?]].
    destruct (decompose a) as [k' [??]].
    destruct (choose_ub I k k') as [k'' [??]].
    exists k''.
    exists (ds_hom DS k' k'' H0 x :: map (ds_hom DS k k'' H) Y).
    simpl.
    apply cons_morphism.
    rewrite <- e0.
    destruct (cocone_commute CC k' k'' H0).
    split. apply H1. apply H2.
    rewrite e.
    rewrite map_map.
    generalize (cocone_commute CC k k'' H).
    clear. induction Y; simpl; intros; auto.
    apply cons_morphism; auto.
    destruct H0. split.
    apply H0. apply H1.
  Qed.
End powerdom_decompose.

Lemma powerdomain_continuous hf sort : continuous_functor (powerdomainF hf sort).
Proof.
  repeat intro.
  apply decompose_is_colimit. intros.
  simpl in x.
  destruct (finset_decompose hf I DS CC) with (powerdom.elem _ _ x)
    as [k [Y ?]].
  apply colimit_decompose. auto.
  assert (inh hf Y).
  generalize (powerdom.elem_inh _ _ x).
  clear -e.
  destruct hf; intros; auto.
  destruct Y.
  destruct x. simpl in *.
  destruct H.
  rewrite e in H. apply nil_elem in H. elim H.
  exists c. apply cons_elem; auto.
  simpl. exists k.
  exists (powerdom.PdomElem _ _ Y H).
  simpl in *.
  apply (powerdom.pdom_elem_eq_eq hf (cocone_point CC) sort).
  simpl. auto.
Qed.
