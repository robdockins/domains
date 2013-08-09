Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import plotkin.

Definition is_joinable_relation {A B:preord} (R:finset (A × B)) :=
  forall G:finset (A × B), G ⊆ R ->
    forall x, minimal_upper_bound x (image π₁ G) ->
      exists y, (x,y) ∈ R /\ upper_bound y (image π₂ G).

Definition joinable_relation (A B:preord)
  := { R:finset (A × B) | is_joinable_relation R }.

Definition joinable_rel_ord (A B:preord) (R S:joinable_relation A B) :=
  forall a b, (a,b) ∈ proj1_sig R -> 
    exists a' b', (a',b') ∈ proj1_sig S /\ a' ≤ a /\ b ≤ b'.

Program Definition joinable_rel_ord_mixin (A B:preord) :
  Preord.mixin_of (joinable_relation A B) :=
  Preord.Mixin (joinable_relation A B) (joinable_rel_ord A B) _ _.
Next Obligation.
  repeat intro. exists a. exists b. split; auto.
Qed.
Next Obligation.
  repeat intro.
  destruct (H a b) as [a' [b' [?[??]]]]; auto.
  destruct (H0 a' b') as [a'' [b'' [?[??]]]]; auto.
  exists a''. exists b''. split; auto.
  split; etransitivity; eauto.
Qed.  

Canonical Structure joinable_rel_order (A B:preord) : preord :=
  Preord.Pack (joinable_relation A B) (joinable_rel_ord_mixin A B).

Lemma joinable_ord_dec
  (A B:preord)
  (HAeff : effective_order A)
  (HBeff : effective_order B)
  (R S:joinable_relation A B) :
  { R ≤ S }+{ R ≰ S }.
Proof.
  intros.
  destruct (finset_find_dec' (A×B)
    (fun z => exists w, w ∈ proj1_sig S /\ π₁#w ≤ π₁#z /\ π₂#z ≤ π₂#w))
    with (proj1_sig R).
  intros.
  destruct H0 as [w [??]]. exists w. intuition.
  rewrite <- H. auto.
  rewrite <- H. auto.
  intro.
  destruct (finset_find_dec (A×B)
    (fun w => π₁#w ≤ π₁#x /\ π₂#x ≤ π₂#w))
    with (proj1_sig S).
  intros.
  destruct H0 as [??].
  rewrite H in H0.
  rewrite H in H1.
  split; auto.
  intros.
  assert (Hdec : ord_dec (A × B)).
  constructor. intros.
  destruct x1 as [a b]. destruct y as [c d].
  destruct (eff_ord_dec A HAeff a c).
  destruct (eff_ord_dec B HBeff b d).
  left. split; auto.
  right. intros [??]. apply n; auto.
  right. intros [??]. apply n; auto.
  destruct (eff_ord_dec _ HAeff (π₁ # x0) (π₁ # x)).
  destruct (eff_ord_dec _ HBeff (π₂ # x) (π₂ # x0)).
  left. auto.
  right. intros [??]. apply n; auto.
  right. intros [??]. apply n; auto.
  destruct s as [z [?[??]]].
  left. exists z.  split; auto.
  right.
  intros [w [?[??]]].
  apply (n w); auto.
  destruct s as [z [??]].
  right.
  red. intros.
  destruct (H1 (fst z) (snd z)) as [p [q [?[??]]]].
  destruct z; auto.
  apply H0. exists (p,q). split; auto.
  left.
  repeat intro.
  destruct (e (a,b)) as [[p q] [?[??]]]; auto.
  exists p. exists q. split; auto.
Qed.

Lemma is_joinable_rel_dec0
  (A B:preord)
  (HAeff : effective_order A)
  (HBeff : effective_order B)
  (HAplt : plotkin_order A)
  (R:finset (A × B)) :
  { is_joinable_relation R } +
  { exists G:finset (A×B), G ⊆ R /\exists z : A,
     minimal_upper_bound z (image π₁ G) /\
     (forall q : B, (z, q) ∈ R -> ~ upper_bound q (image π₂ G)) }.
Proof.
  assert (Hdec : ord_dec (A × B)).
  constructor. intros.
  destruct x; destruct y.
  destruct (eff_ord_dec A HAeff c c1);
    destruct (eff_ord_dec B HBeff c0 c2).
  left. split; auto.
  right. intros [??]. apply n; auto.
  right. intros [??]. apply n; auto.
  right. intros [??]. apply n; auto.

  set (H:=I).

  set (P (G:finset (A×B)) := 
    forall x:A, minimal_upper_bound x (image π₁ G) ->
      exists y, (x,y) ∈ R /\ upper_bound y (image π₂ G)).

  assert (Hrespects : forall x y:finset (A×B), x ≈ y -> P x -> P y).
  unfold P; intros.
  destruct (H1 x0); auto.
  destruct H2.
  split.
  red; intros. apply H2.
  apply image_axiom2 in H4.
  destruct H4 as [q[??]].
  rewrite H5. apply image_axiom1.
  rewrite <- H0; auto.
  intros. apply H3.
  red; intros.
  apply image_axiom2 in H6.
  destruct H6 as [q [??]].
  apply H4.
  rewrite H7. apply image_axiom1. rewrite H0; auto.
  auto.
  destruct H3.
  exists x1. split; auto.
  red; intros.
  apply image_axiom2 in H5.
  destruct H5 as [a [??]].
  apply H4.
  rewrite H6.
  apply image_axiom1.
  rewrite H0. auto.

  destruct (finsubset_dec' (A × B) Hdec P) with R; auto.
  unfold P. intro G.
  set (Q x0 := minimal_upper_bound x0 (image π₁ G) -> exists y, (x0,y) ∈ R /\ upper_bound y (image π₂ G)).
  destruct (finset_find_dec' A Q) with (mub_closure HAplt (image π₁ G)).
  unfold Q; intros.
  destruct H1 as [q [??]].
  revert H2. apply minimal_upper_bound_ok; auto.
  exists q; split; auto.
  apply member_eq with (x,q); auto.
  destruct H0; split; split; auto.

  intro x.
  unfold Q.
  destruct (mub_finset_dec A HAeff HAplt (image π₁ G) x).
  destruct (finset_find_dec (A×B) (fun q => fst q ≈ x /\ upper_bound (snd q) (image π₂ G))) with R.
  intros. destruct H1; split.
  rewrite <- H1.
  destruct H0 as [[??][??]]; auto.
  revert H2. apply upper_bound_ok.
  destruct H0 as [[??][??]]; split; auto.
  intros [a b]. simpl.
  destruct (eff_ord_dec A HAeff a x).
  destruct (eff_ord_dec A HAeff x a).
  destruct (upper_bound_dec B HBeff (image π₂ G) b).
  left. split; auto.
  right. intros [??]. apply n; auto.
  right. intros [[??]?]. apply n; auto.
  right. intros [[??]?]. apply n; auto.

  destruct s as [z [??]].
  destruct H1.
  destruct z as [a b]. simpl in H1, H2.
  left. intros.
  exists b. split.
  apply member_eq with (a,b); auto.
  destruct H1; split; split; auto.
  auto.
  right; intro.
  destruct H0. auto.
  destruct H0.
  apply n in H0.
  apply H0.
  split; auto.
  left. intro. elim n; auto.
  destruct s as [z [??]].
  right. intro.
  apply H1. intro.
  apply H2; auto.
  left. intros.
  apply q; auto.
  apply (mub_clos_mub A HAplt (image π₁ G) (image π₁ G)); auto.
  apply mub_clos_incl.
  right. 
  destruct e as [G [??]].
  exists G. split; auto.
      
  set (Q x0 := minimal_upper_bound x0 (image π₁ G) -> exists y, (x0,y) ∈ R /\ upper_bound y (image π₂ G)).
  destruct (finset_find_dec' A Q) with (mub_closure HAplt (image π₁ G)).
  unfold Q; intros.
  destruct H3 as [q [??]].
  revert H4. apply minimal_upper_bound_ok; auto.
  exists q; split; auto.
  apply member_eq with (x,q); auto.
  destruct H2; split; split; auto.
  intro x.
  unfold Q.
  destruct (mub_finset_dec A HAeff HAplt (image π₁ G) x).
  destruct (finset_find_dec (A×B) (fun q => fst q ≈ x /\ upper_bound (snd q) (image π₂ G))) with R.
  intros. destruct H3; split.
  rewrite <- H3.
  destruct H2 as [[??][??]]; auto.
  revert H4. apply upper_bound_ok.
  destruct H2 as [[??][??]]; split; auto.
  intros [a b]. simpl.
  destruct (eff_ord_dec A HAeff a x).
  destruct (eff_ord_dec A HAeff x a).
  destruct (upper_bound_dec B HBeff (image π₂ G) b).
  left. split; auto.
  right. intros [??]. apply n; auto.
  right. intros [[??]?]. apply n; auto.
  right. intros [[??]?]. apply n; auto.
  
  destruct s as [z [??]].
  destruct H3.
  destruct z as [a b]. simpl in H3, H4.
  left. intros.
  exists b. split.
  apply member_eq with (a,b); auto.
  destruct H3; split; split; auto.
  auto.
  right; intro.
  destruct H2. auto.
  destruct H2.
  apply n in H2.
  apply H2.
  split; auto.
  left. intro. elim n; auto.
  destruct s as [z [??]].
  destruct (mub_finset_dec A HAeff HAplt (image π₁ G) z).
  exists z. split; auto.
  repeat intro.
  apply H3. red. intros.
  exists q. split; auto.
  elim H3; red; intros. elim n; auto.
  elim H1. red; intros.
  apply q; auto.
  apply (mub_clos_mub A HAplt (image π₁ G) (image π₁ G)); auto.
  apply mub_clos_incl.
Qed.


Lemma is_joinable_rel_dec
  (A B:preord)
  (HAeff : effective_order A)
  (HBeff : effective_order B)
  (HAplt : plotkin_order A)
  (R:finset (A × B)) :
  { is_joinable_relation R } + { ~is_joinable_relation R }.
Proof.
  destruct (is_joinable_rel_dec0 A B HAeff HBeff HAplt R).
  left; auto.
  right; intro.
  red in H.
  destruct e as [G [? [z [??]]]].
  destruct (H G H0 z H1) as [y [??]].
  apply (H2 y); auto.
Qed.


Program Definition joinable_rel_effective
  (A B:preord)
  (HAeff : effective_order A)
  (HBeff : effective_order B)
  (HAplt : plotkin_order A) :
  effective_order (joinable_rel_order A B)
  := EffectiveOrder _ _ _ _.
Next Obligation.
  intros.
  apply joinable_ord_dec; auto.
Qed.
Next Obligation.
  intros.
  set (X := finsubsets (A×B) (eprod (eff_enum A HAeff) (eff_enum B HBeff))).
  exact (fun n => match X n with
           | None => None
           | Some a => 
               match is_joinable_rel_dec A B HAeff HBeff HAplt a with
               | left H => Some (exist _ a H)
               | right _ => None
               end
           end).
Defined.
Next Obligation.
  intros.
  unfold joinable_rel_effective_obligation_2.
  red. simpl.
  destruct x as [x H].
  assert (x ∈ finsubsets (A×B) (eprod (eff_enum A HAeff) (eff_enum B HBeff))).
  apply finsubsets_complete.
  red; intros.
  destruct a as [a b].
  apply elem_eprod.
  split; apply eff_complete.
  destruct H0 as [n ?].
  exists n.
  destruct (finsubsets (A×B) (eprod (eff_enum A HAeff) (eff_enum B HBeff)) n).
  destruct (is_joinable_rel_dec A B HAeff HBeff HAplt c).
  destruct H0.
  split; red; simpl; auto. red.
  simpl; intros.
  apply H0 in H2.
  exists a. exists b. split; auto.
  red; simpl; intros.
  apply H1 in H2.
  exists a. exists b. auto.
  apply n0; auto.
  red; intros.
  destruct (H G) with x0 as [y [??]]; auto.
  rewrite H0; auto.
  exists y. split; auto.
  rewrite <- H0; auto.
  auto.
Qed.


Section joinable_plt.
  Variables A B:preord.
  Variable HAeff : effective_order A.
  Variable HAplt : plotkin_order A.
  Variable HBeff : effective_order B.
  Variable HBplt : plotkin_order B.

  Lemma intersect_approx
    (R:A×B -> Prop)
    (Hdec : forall x, {R x}+{~R x})
    (HR : forall a a' b b', a ≤ a' -> b' ≤ b -> R (a,b) -> R (a',b'))
    (HRdir : forall a (M:finset B), (forall b, b ∈ M -> R (a,b)) ->
      exists z, R (a,z) /\ upper_bound z M)
    (P:finset A) (Q:finset B)
    (HP:mub_closed A P) (HQ:mub_closed B Q) :
    is_joinable_relation (finsubset (A×B) R Hdec (finprod P Q)).
  Proof.
    assert (HR2 : forall x y : Preord_Eq (A × B), x ≈ y -> R x -> R y).
    intros.
    destruct x; destruct y.
    apply HR with c c0; auto.
    destruct H as [[??][??]]; auto.
    destruct H as [[??][??]]; auto.

    repeat intro. 
    assert (x ∈ P). apply HP with (image π₁ G); auto.
    red; intros.
    apply image_axiom2 in H1. destruct H1 as [y [??]].
    apply H in H1.
    apply finsubset_elem in H1.
    destruct H1.
    destruct y.
    apply finprod_elem in H1.
    destruct H1. simpl in H2.
    rewrite <- H2 in H1. auto.
    intros.
    destruct x0; destruct y0.
    eapply HR. 3: apply H4.
    destruct H3 as [[??][??]]; auto.
    destruct H3 as [[??][??]]; auto.

    destruct (HRdir x (image π₂ G)).
    intros. 
    apply image_axiom2 in H2.
    destruct H2 as [q [??]].
    generalize H2; intro H2'.
    apply H in H2.
    apply finsubset_elem in H2.
    destruct H2.
    destruct q.
    simpl in H3.
    apply HR with c c0; auto.
    apply H0.
    change c with (π₁#((c,c0):A×B)).
    apply image_axiom1. auto.
    intros. 
    destruct x0; destruct y.
    apply HR with c c0; auto.
    destruct H4 as [[??][??]]; auto.
    destruct H4 as [[??][??]]; auto.
    destruct H2.
    destruct (mub_complete B HBplt (image π₂ G) x0) as [y [??]]; auto.
    exists y. split; auto.
    apply finsubset_elem.
    intros.
    destruct x1. destruct y0.
    apply HR with c c0; auto.
    destruct H6 as [[??][??]]; auto.
    destruct H6 as [[??][??]]; auto.
    split.
    apply finprod_elem; split; auto.
    apply (HQ (image π₂ G)); auto.
    red; intros.
    apply image_axiom2 in H6.
    destruct H6 as [q [??]].
    apply H in H6.
    apply finsubset_elem in H6.
    destruct H6.
    destruct q.
    apply finprod_elem in H6.
    destruct H6.
    rewrite H7; simpl; auto.
    intros.
    destruct x1; destruct y0.
    apply HR with c c0; auto.
    destruct H8 as [[??][??]]; auto.
    destruct H8 as [[??][??]]; auto.
    apply HR with x x0; auto.
    destruct H4; auto.
  Qed.

  Definition mkrel (R:joinable_relation A B) (x:A×B) :=
    exists a b, (a,b) ∈ proj1_sig R /\ a ≤ fst x /\ snd x ≤ b.

  Lemma mkrel_dec R : forall x, {mkrel R x}+{~mkrel R x}.
  Proof.
    intros.
    unfold mkrel.
    destruct (finset_find_dec (A×B) (fun y => fst y ≤ fst x /\ snd x ≤ snd y))
      with (proj1_sig R).
    intros.
    destruct H. destruct H0.
    destruct H; destruct H1.
    split; eauto.
    intros.
    destruct (eff_ord_dec A HAeff (fst x0) (fst x)).
    destruct (eff_ord_dec B HBeff (snd x) (snd x0)).
    left. split; auto.
    right; intros [??]; apply n; auto.
    right; intros [??]; apply n; auto.
    destruct s.
    left. exists (fst x0). exists (snd x0). auto.
    right; intros [a [b [?[??]]]].
    apply (n (a,b)); auto.
  Qed.

  Lemma mkrel_dir R : 
    forall a (M:finset B), (forall b, b ∈ M -> mkrel R (a,b)) ->
      exists z, mkrel R (a,z) /\ upper_bound z M.
  Proof.
    intros.
    set (P q := mkrel R q /\ snd q ∈ M /\ fst q ≤ a).
    assert (POK : forall x y, x ≈ y -> P x -> P y).
    clear. unfold P; intros.
    destruct H as [[??][??]].
    intuition.
    destruct H4 as [m [n [?[??]]]].
    exists m. exists n. intuition eauto.
    apply member_eq with (snd x); auto.
    eauto.
    assert (Pdec : forall q, { P q }+{ ~P q }).
    intro q.
    destruct (mkrel_dec R q).
    destruct (eff_in_dec HBeff M (snd q)).
    destruct (eff_ord_dec A HAeff (fst q) a).
    left. split; auto.
    right; intros [?[??]]; apply n; auto.
    right; intros [?[??]]; apply n; auto.
    right; intros [?[??]]; apply n; auto.

    set (R' := finsubset (A×B) (fun q => fst q ≤ a)
      (fun q => eff_ord_dec A HAeff (fst q) a) (proj1_sig R)).
    destruct (mub_complete A HAplt (image π₁ R') a).
    red; intros.
    apply image_axiom2 in H0.
    destruct H0. destruct H0.
    unfold R' in H0.
    apply finsubset_elem in H0.
    destruct H0.
    rewrite H1; auto.
    intros.
    transitivity (fst x1); auto.
    destruct H2 as [[??][??]]; auto.
    destruct H0.
    assert (is_joinable_relation (proj1_sig R)). apply proj2_sig.
    destruct (H2 R') with x; auto.
    red; intros.
    unfold R' in H3.
    apply finsubset_elem in H3.
    destruct H3; auto.
    intros.
    transitivity (fst x0); auto.
    destruct H4 as [[??][??]]; auto.
    destruct H3.
    exists x0. split.
    exists x. exists x0.
    split; auto.
    red; intros.
    generalize (H x1 H5). intros.
    destruct H6 as [p [q [?[??]]]].
    simpl in H7, H8.
    transitivity q; auto.
    apply H4.
    change q with (π₂#((p,q):A×B)).
    apply image_axiom1.
    unfold R'.
    apply finsubset_elem; auto.
    intros.
    transitivity (fst x2); auto.
    destruct H9 as [[??][??]]; auto.
  Qed.

  Lemma mkrel_ord R : forall a a' b b', a ≤ a' -> b' ≤ b -> mkrel R (a,b) -> mkrel R (a',b').
  Proof.
    unfold mkrel; intros.
    destruct H1 as [p [q [?[??]]]].
    exists p. exists q. split; auto. split.
    transitivity a; auto.
    transitivity b; auto.
  Qed.

  Lemma mkrel_mono : forall R S, R ≤ S ->
    forall x, mkrel R x -> mkrel S x.
  Proof.
    unfold mkrel; intros.
    destruct H0 as [a [b [?[??]]]].
    destruct (H a b) as [a' [b' [?[??]]]]; auto.
    exists a'. exists b'. split; auto.
    split.
    transitivity a; auto.
    transitivity b; auto.
  Qed.

  Lemma mkrel_mono' : forall (R S:joinable_relation A B),
    (forall x, x ∈ proj1_sig R -> mkrel S x) -> R ≤ S.
  Proof.
    repeat intro.
    destruct (H (a,b)) as [a' [b' [?[??]]]]. auto.
    exists a'. exists b'. split; auto.
  Qed.


  Section join_rel_normal.
    Variable (P:finset A).
    Variable (Q:finset B).
    Variable (HP:mub_closed A P).
    Variable (HQ:mub_closed B Q).

    Fixpoint select_jrels (l:finset (finset (A×B))) : finset (joinable_rel_order A B) :=
      match l with
      | nil => nil
      | cons R l' =>
         match is_joinable_rel_dec A B HAeff HBeff HAplt R with
         | left H => cons (exist _ R H) (select_jrels l')
         | right _ => select_jrels l'
         end
      end.

    Lemma select_jrels_elem1 : forall R (H:is_joinable_relation R) XS,
      R ∈ XS -> (exist _ R H : joinable_rel_order A B) ∈ select_jrels XS.
    Proof.
      induction XS; simpl; intros.
      apply nil_elem in H0. elim H0.
      destruct (is_joinable_rel_dec A B HAeff HBeff HAplt a).
      apply cons_elem in H0. destruct H0.
      apply cons_elem. left.
      split. red; simpl; intros.
      red; simpl; intros.
      exists a0. exists b. split; auto.
      destruct H0. apply H0; auto.
      red; simpl; intros.
      red; simpl; intros.
      exists a0. exists b. split; auto.
      destruct H0. apply H2; auto.
      apply cons_elem. right.
      apply IHXS. auto.
      apply cons_elem in H0.
      destruct H0.
      elim n.
      red; intros.
      destruct (H G) with x; auto.
      rewrite H0; auto.
      destruct H3.
      exists x0; split; auto.
      rewrite <- H0; auto.
      apply IHXS; auto.
    Qed.

    Lemma select_jrels_elem2 : forall R XS,
      R ∈ select_jrels XS -> exists R', R ≈ R' /\ proj1_sig R' ∈ XS.
    Proof.
      induction XS; simpl; intros.
      apply nil_elem in H. elim H.
      destruct (is_joinable_rel_dec A B HAeff HBeff HAplt a).
      apply cons_elem in H.
      destruct H.
      exists (exist is_joinable_relation a i).
      split; auto.
      simpl. apply cons_elem; auto.
      destruct IHXS as [R' [??]]; auto.
      exists R'; split; auto.
      apply cons_elem; auto.
      destruct IHXS as [R' [??]]; auto.
      exists R'; split; auto.
      apply cons_elem; auto.
    Qed.      

    Definition all_jrels := select_jrels (list_finsubsets (finprod P Q)).

    Lemma all_jrels_complete : forall R,
      R ∈ all_jrels <->
        exists R', R ≈ R' /\ (proj1_sig R' ⊆ finprod P Q).
    Proof.
      intros. split; intros.
      unfold all_jrels in H.
      apply select_jrels_elem2 in H.
      destruct H as [R' [??]].
      exists R'. split; auto.
      apply list_finsubsets_correct in H0. auto.
      destruct H as [R' [??]].      
      unfold all_jrels.
      rewrite H.
      destruct R'.
      apply select_jrels_elem1.
      apply list_finsubsets_complete; auto.
      constructor.
      apply effective_prod; auto.
    Qed.

    Lemma joinable_rels_normal : 
      normal_set (joinable_rel_order A B) (joinable_rel_effective A B HAeff HBeff HAplt) all_jrels.
    Proof.
      red; intros.
      red. simpl; intros.
      set (R := finsubset (A×B) (mkrel z) (mkrel_dec z) (finprod P Q)).
      assert (is_joinable_relation R).
      apply intersect_approx; auto.
      apply mkrel_ord.
      apply mkrel_dir.

      exists (exist _ R H0).
      split.
      red; intros.
      generalize (H x H1).
      intros.
      apply finsubset_elem in H2.
      destruct H2; auto.
      apply all_jrels_complete in H2.
      destruct H2 as [R' [??]].
      rewrite H2 in H3.
      rewrite H2.
      red; simpl; intros.
      red; simpl; intros.
      exists a. exists b. split; auto.
      unfold R.
      apply finsubset_elem.
      clear. intros.
      destruct x. destruct y.
      apply mkrel_ord with c c0; auto.
      destruct H as [[??][??]]; auto.
      destruct H as [[??][??]]; auto.
      split; auto.
      eapply mkrel_mono with R'; auto.
      exists a. exists b. auto.
      clear. intros. rewrite <- H; auto.
      
      apply finsubset_elem.
      intros. rewrite <- H1. auto.
      split.
      apply all_jrels_complete.
      exists (exist _ R H0).
      split; auto.
      red; intros.
      simpl in H1.
      unfold R in H1.
      apply finsubset_elem in H1.
      destruct H1; auto.
      clear. intros.
      destruct x. destruct y.
      apply mkrel_ord with c c0; auto.
      destruct H as [[??][??]]; auto.
      destruct H as [[??][??]]; auto.
      red; simpl; intros.
      red; simpl; intros.
      unfold R in H1.
      apply finsubset_elem in H1.
      destruct H1; auto.
      clear. intros.
      destruct x. destruct y.
      apply mkrel_ord with c c0; auto.
      destruct H as [[??][??]]; auto.
      destruct H as [[??][??]]; auto.
    Qed.
  End join_rel_normal.

  Lemma joinable_rel_has_normals : 
    has_normals (joinable_rel_order A B) (joinable_rel_effective A B HAeff HBeff HAplt).
  Proof.
    red. intro M.
    set (XS := (concat A (List.map (fun R => List.map (@fst _ _) (proj1_sig R)) M) : finset A)).
    set (YS := (concat B (List.map (fun R => List.map (@snd _ _) (proj1_sig R)) M) : finset B)).
    set (MS := mub_closure HAplt XS).
    set (NS := mub_closure HBplt YS).
    assert (HXYS : forall R x y, List.In R M -> (x,y) ∈ proj1_sig R -> x ∈ XS /\ y ∈ YS).
    subst XS YS.
    clear. induction M; simpl; intros.
    elim H. destruct H. subst R.
    split.
    apply app_elem.
    left.
    destruct H0 as [q [??]].
    exists (fst q).
    split; auto.
    apply List.in_map. auto.
    destruct H0 as [[??][??]]; split; auto.
    apply app_elem.
    left.
    destruct H0 as [q [??]].
    exists (snd q).
    split; auto.
    apply List.in_map. auto.
    destruct H0 as [[??][??]]; split; auto.
    split.
    apply app_elem. right.
    eapply IHM; eauto.
    apply app_elem. right.
    eapply IHM; eauto.

    exists (all_jrels MS NS).
    split.
    red; intros.
    destruct H as [q [??]].
    apply all_jrels_complete.
    exists q. split; auto.
    red; intros.
    destruct a0 as [x y].
    apply finprod_elem.
    split.
    unfold MS.
    apply mub_clos_incl.
    eapply HXYS; eauto.
    unfold NS.
    apply mub_clos_incl.
    eapply HXYS; eauto.
    apply joinable_rels_normal.
    unfold MS. apply mub_clos_mub.
    unfold NS. apply mub_clos_mub.
  Qed.

  Definition joinable_rel_plt : plotkin_order (joinable_rel_order A B)
    := norm_plt 
         (joinable_rel_order A B)
         (joinable_rel_effective A B HAeff HBeff HAplt)
         joinable_rel_has_normals.

End joinable_plt.



Section directed_joinables.
  Variables A B:preord.
  Variable HAeff : effective_order A.
  Variable HAplt : plotkin_order A.
  Variable HBeff : effective_order B.
  Variable HBplt : plotkin_order B.

  Let OD := OrdDec A (eff_ord_dec A HAeff).

  Variable R:erel A B.
  Hypothesis HR : forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R.
  Hypothesis HRdir : forall a, directed (erel_image A B OD R a).

  Section swell.

  Variable RS : finset (A×B).

  Let RS' := finprod
     (mub_closure HAplt (image π₁ RS))
     (mub_closure HBplt (image π₂ RS)).

  Section swell_relation.
    Variable G:finset (A×B).
    Hypothesis HG : G ⊆ R.
    Hypothesis HG' : G ⊆ RS'.

    Variable G0:finset (A×B).
    Hypothesis HG0 : G0 ⊆ G.

    Variable z:A.
    Hypothesis Hz : minimal_upper_bound z (image π₁ G0).

    Lemma swell_row :
      exists q,
        (z,q) ∈ RS' /\ (z,q) ∈ R /\
        upper_bound q (image π₂ G0).
    Proof.
      destruct (HRdir z (image π₂ G0)) as [q [??]].
      red; intros.
      apply image_axiom2 in H.
      destruct H as [q[??]].
      apply erel_image_elem.
      destruct q as [x y]. simpl in H0.
      apply HR with x y.      
      apply Hz. change x with (π₁#((x,y):A×B)).
      apply image_axiom1. auto.
      destruct H0; auto.
      apply HG; auto.
      apply erel_image_elem in H0.
      destruct (mub_complete B HBplt (image π₂ G0) q) as [q0 [??]]; auto.
      exists q0. split.      
      unfold RS'. apply finprod_elem. split.
      apply (mub_clos_mub A HAplt (image π₁ RS) (image π₁ G0)); auto.
      red; intros.
      apply image_axiom2 in H3. destruct H3 as [y [??]].
      apply HG0 in H3.
      apply HG' in H3.
      unfold RS' in H3.
      destruct y as [x y].
      apply finprod_elem in H3.
      rewrite H4. simpl.
      destruct H3; auto.
      apply (mub_clos_mub B HBplt (image π₂ RS) (image π₂ G0)); auto.
      red; intros.
      apply image_axiom2 in H3. destruct H3 as [y [??]].
      apply HG0 in H3.
      apply HG' in H3.
      unfold RS' in H3.
      destruct y as [x y].
      apply finprod_elem in H3.
      rewrite H4. simpl.
      destruct H3; auto.
      split. apply HR with z q; auto.
      destruct H1; auto.
    Qed.

    Variable XS : finset (A×B).
    Hypothesis HXS : forall x, x ∈ XS <-> x ∈ RS' /\ x ∉ G.    

    Let ODAB := OrdDec (A×B) (eff_ord_dec _ (effective_prod HAeff HBeff)).

    Hypothesis noub : forall q, (z,q) ∈ G -> ~upper_bound q (image π₂ G0).

    Lemma swell_relation :
      exists G':finset (A×B), exists XS':finset (A×B),
        length XS' < length XS /\
        G ⊆ G' /\ G' ⊆ R /\ G' ⊆ RS' /\
        (forall x, x ∈ XS' <-> x ∈ RS' /\ x ∉ G').
    Proof.
      destruct swell_row as [r [?[??]]].
      exists ((z,r)::G)%list.
      exists (finset_remove ODAB XS (z,r)).
      split. apply finset_remove_length2.
      apply HXS. split; auto.
      red; intro. apply (noub r); auto.
      split. red; intros. apply cons_elem; auto.
      split. red; intros.
      apply cons_elem in H2. destruct H2.
      rewrite H2; auto. apply HG; auto.
      split. red; intros.
      apply cons_elem in H2. destruct H2.
      rewrite H2; auto. apply HG'; auto.
      intro. split; intros.
      apply finset_remove_elem in H2.
      destruct H2.
      apply HXS in H2. destruct H2.
      split. auto.
      intro.
      apply cons_elem in H5. destruct H5.
      apply H3; auto.
      apply H4; auto.
      apply finset_remove_elem.
      destruct H2.
      split.
      apply HXS.
      split; auto.
      intro. apply H3. apply cons_elem. auto.
      intro. apply H3. apply cons_elem. auto.
    Qed.
  End swell_relation.

  Lemma swell_inductive_step
    (G:finset (A×B))
    (HG : G ⊆ R) (HG': G ⊆ RS')
    (XS:finset (A×B))
    (HXS: forall x, x ∈ XS <-> x ∈ RS' /\ x ∉ G) :

    is_joinable_relation G \/
    exists G':finset (A×B), exists XS':finset (A×B),
        length XS' < length XS /\
        G ⊆ G' /\ G' ⊆ R /\ G' ⊆ RS' /\
        (forall x, x ∈ XS' <-> x ∈ RS' /\ x ∉ G').
  Proof.
    destruct (is_joinable_rel_dec0 A B HAeff HBeff HAplt G).
    left. auto.
    destruct e as [G0 [? [z [??]]]].
    destruct swell_relation with G G0 z XS
      as [G' [XS' [?[?[?[??]]]]]]; auto.
    right.
    exists G'. exists XS'. intuition.
  Qed.

  Lemma swell_aux (n:nat) : forall
    (G:finset (A×B))
    (HG : G ⊆ R)
    (HG': G ⊆ RS')
    (XS : finset (A×B))
    (HXS: forall x, x ∈ XS <-> x ∈ RS' /\ x ∉ G)
    (Hn : n = length XS),
    exists G':finset (A×B),
      G ⊆ G' /\ G' ⊆ R /\ is_joinable_relation G'.
  Proof.      
    induction n using (well_founded_induction Wf_nat.lt_wf); intros.
    destruct (swell_inductive_step G HG HG' XS HXS).
    exists G. split; auto.
    red; auto.
    destruct H0 as [G' [XS' [?[?[?[??]]]]]].
    destruct (H (length XS')) with G' XS' as [G'' [?[??]]]; auto.
    rewrite Hn. auto.
    exists G''. split; auto.
    red; intros. apply H5. apply H1. auto.
  Qed.

  Hypothesis HRS : RS ⊆ R.

  Lemma swell : exists G:finset (A×B),
    RS ⊆ G /\ G ⊆ R /\ is_joinable_relation G.
  Proof.
    assert (HRdec : forall x, { x ∉ RS }+{ ~x ∉ RS }).
    intro. destruct (eff_in_dec (effective_prod HAeff HBeff) RS x).
    right; auto. left; auto.
    set (XS := finsubset _ (fun x => x ∉ RS) HRdec RS').
    destruct (swell_aux (length XS)) with RS XS as [G [?[??]]]; auto.
    red; intros.
    unfold RS'.
    destruct a. apply finprod_elem.
    split.
    apply (mub_clos_incl A HAplt (image π₁ RS)).
    change c with (π₁#((c,c0):A×B)).
    apply image_axiom1. auto.
    apply (mub_clos_incl B HBplt (image π₂ RS)).
    change c0 with (π₂#((c,c0):A×B)).
    apply image_axiom1. auto.
    split; intros.    
    unfold XS in H.
    apply finsubset_elem in H; auto.
    intros. rewrite <- H0. auto.
    unfold XS.
    apply finsubset_elem; auto.
    intros. rewrite <- H0. auto.
    exists G. auto.
  Qed.

  End swell.

  Variable M:finset (joinable_rel_order A B).
  Hypothesis HM : forall S, S ∈ M -> proj1_sig S ⊆ R.
  Let RS := concat _ (List.map (fun R => proj1_sig R) M) : finset (A×B).

  Lemma RS_elem :
    forall a, a ∈ RS -> (exists S, S ∈ M /\ a ∈ proj1_sig S).
  Proof.
    intro a.
    unfold RS.
    clear -HM.
    induction M; simpl in *; intros.
    apply nil_elem in H. elim H.
    apply app_elem in H. destruct H.
    exists a0. split.
    exists a0; split; simpl; auto. auto.
    destruct IHc.
    intros. apply HM.
    apply cons_elem; auto.
    auto.
    exists x. 
    destruct H0.
    split; auto.
    apply cons_elem; auto.
  Qed.

  Lemma RS_elem' : forall S a, List.In S M -> a ∈ proj1_sig S -> a ∈ RS.
  Proof.
    intros. unfold RS.
    clear -M HM H H0.
    induction M; simpl. elim H.
    destruct H. subst a0.
    apply app_elem. left. auto.
    apply app_elem. right.
    apply IHc. intros.
    apply HM; auto.
    apply cons_elem; auto.
    auto.
  Qed.

  Theorem directed_joinables :
    exists Q, upper_bound Q M /\ proj1_sig Q ⊆ R.
  Proof.
    destruct (swell RS) as [G [?[??]]]; auto.
    red; intros.
    apply RS_elem in H.
    destruct H as [S [??]].
    apply (HM S); auto.
    exists (exist _ G H1). split.
    red; intros.
    destruct H2 as [q [??]].
    rewrite H3.
    red; simpl; intros.
    red; simpl; intros.
    exists a. exists b. split; auto.
    apply H.
    apply RS_elem' with q; auto.
    simpl. auto.
  Qed.
End directed_joinables.
