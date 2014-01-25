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

Lemma nil_subset X (Q:finset X) :
  (nil : finset X) ⊆ Q.
Proof.
  repeat intro. apply nil_elem in H. elim H.
Qed.

Lemma ub_nil : forall (X:preord) (a:X),
  upper_bound a (nil : finset X).
Proof.
  repeat intro. apply nil_elem in H. elim H.
Qed.

Lemma dec_conj (P Q : Prop) :
  {P}+{~P} -> {Q}+{~Q} -> {P/\Q}+{~(P/\Q)}.
Proof.
  intros. destruct H. destruct H0.
  left; auto.
  right; intros [??]; contradiction.
  right; intros [??]; contradiction.
Qed.

Lemma ub_cons (X:preord) (x:X) (xs:finset X) (a:X) :
  x ≤ a ->
  upper_bound a xs ->
  upper_bound a (x::xs : finset X).
Proof.
  repeat intro.
  apply cons_elem in H1. destruct H1.
  rewrite H1. auto. apply H0; auto.
Qed.


Module powerdom.

Inductive pdom :=
  | Lower
  | Upper
  | Convex.

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

    Definition pdom_ord (sort:pdom) := 
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
Lemma cons_subset (x:X) (xs ys:finset X) :
  x ∈ ys -> xs ⊆ ys -> (x::xs : finset X) ⊆ ys.
Proof.
  repeat intro.
  apply cons_elem in H1. destruct H1.
  rewrite H1; auto. apply H0; auto.
Qed.
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

End powerdom.
End powerdom.
