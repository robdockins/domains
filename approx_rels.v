Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import plotkin.
Require Import joinable.

Definition ident_rel {A:preord} (HAeff:effective_order A) : erel A A :=
  esubset_dec _ (fun x => snd x ≤ fst x) (fun x => eff_ord_dec _ HAeff (snd x) (fst x))
    (eprod (eff_enum _ HAeff) (eff_enum _ HAeff)).

Definition compose_rel {A B C:preord} (HBeff:effective_order B)
  (S:erel B C) (R:erel A B) : erel A C :=
  image (mk_pair (π₁ ∘ π₁) (π₂ ∘ π₂))
   (esubset_dec _ (fun x => fst (snd x) ≤ snd (fst x)) 
            (fun x => eff_ord_dec _ HBeff (fst (snd x)) (snd (fst x)))
    (eprod R S)).

Lemma ident_elem A (HAeff:effective_order A) :
  forall x y, (x,y) ∈ ident_rel HAeff <-> y ≤ x.
Proof.
  intros; split; intro.
  unfold ident_rel in H.
  apply esubset_dec_elem in H.
  destruct H; auto.
  clear; intros. destruct H as [[??][??]]; eauto.
  unfold ident_rel.
  apply esubset_dec_elem.
  clear; intros. destruct H as [[??][??]]; eauto.
  split; auto.
  apply elem_eprod. split; apply eff_complete.
Qed.

Lemma compose_elem A B C (HBeff:effective_order B) (S:erel B C) (R:erel A B) :
  (forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R) ->
  forall x z, (x,z) ∈ compose_rel HBeff S R <-> (exists y, (x,y) ∈ R /\ (y,z) ∈ S).
Proof.
  intros HR.
  unfold compose_rel.
  intros; split; intro.
  apply image_axiom2 in H.
  destruct H as [[p q] [??]].
  apply esubset_dec_elem in H. 
  destruct H.
  simpl in H1.
  simpl in H0.
  apply elem_eprod in H.
  destruct H.
  destruct p as [m n].
  destruct q as [r s].
  simpl in H1.
  simpl in H0.
  exists r. split; auto.
  apply HR with m n; auto.
  destruct H0 as [[??][??]]; auto.
  apply member_eq with (r,s); auto.
  destruct H0 as [[??][??]]; split; split; auto.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]].
  eauto.

  destruct H as [q [??]].
  change (x,z) with
    (mk_pair (π₁ ∘ π₁) (π₂ ∘ π₂)
      #
      (((x,q),(q,z)):((A×B)×(B×C)))).
  apply image_axiom1.
  apply esubset_dec_elem.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]].
  eauto.
  split.
  apply elem_eprod; auto.
  simpl. auto.
Qed.

Lemma ident_ordering A (HAeff:effective_order A) :
  forall x x' y y', x ≤ x' -> y' ≤ y ->
    (x,y) ∈ ident_rel HAeff -> (x',y') ∈ ident_rel HAeff.
Proof.
  unfold ident_rel. intros.
  apply esubset_dec_elem in H1. destruct H1.
  simpl in H2.
  apply esubset_dec_elem.
  clear. intros. destruct H as [[??][??]]; eauto.
  split; simpl; auto.
  apply elem_eprod; split; apply eff_complete.
  transitivity y; auto.
  transitivity x; auto.
  clear. intros. destruct H as [[??][??]]; eauto.
Qed.

Definition directed_rel A B (HAeff:effective_order A) (R:erel A B):=
  forall x, directed (erel_image A B (OrdDec A (eff_ord_dec A HAeff)) R x).  

Lemma ident_image_dir A (HAeff:effective_order A) : directed_rel A A HAeff (ident_rel HAeff).
Proof.
  repeat intro.
  exists x. split.
  red; intros.
  apply H in H0.
  apply erel_image_elem in H0.
  unfold ident_rel in H0.
  apply esubset_dec_elem in H0.
  destruct H0; auto.
  clear; intros. destruct H as [[??][??]]; eauto.
  apply erel_image_elem.
  unfold ident_rel.
  apply esubset_dec_elem.
  clear; intros. destruct H as [[??][??]]; eauto.
  split; auto.
  apply elem_eprod; split; apply eff_complete.
Qed.  

Lemma compose_ordering A B C (HBeff:effective_order B) (S:erel B C) (R:erel A B) :
  (forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R) ->
  (forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S) ->
  (forall x x' y y', x ≤ x' -> y' ≤ y -> 
    (x,y) ∈ compose_rel HBeff S R -> (x',y') ∈ compose_rel HBeff S R).
Proof.
  unfold compose_rel. repeat intro.
  apply image_axiom2 in H3.
  destruct H3 as [q [??]].
  apply esubset_dec_elem in H3.
  destruct H3.
  destruct q as [q1 q2].
  apply elem_eprod in H3.
  simpl in H5.
  simpl in H4.
  destruct H3.
  assert ((x',snd q1) ∈ R).
  apply H with (fst q1) (snd q1); auto.
  destruct H4.
  destruct H7.
  transitivity x; auto.
  assert ((fst q2, y') ∈ S).
  apply H0 with (fst q2) (snd q2); auto.
  destruct H4. destruct H4.
  transitivity y; auto.
  change (x',y') with
    ((mk_pair (π₁ ∘ π₁) (π₂ ∘ π₂))# (((x',snd q1),(fst q2,y')) : (A×B)×(B×C))).
  apply image_axiom1.
  apply esubset_dec_elem.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]]; eauto.
  split; simpl; auto.
  apply elem_eprod. split; auto.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]]; eauto.
Qed.  

Lemma compose_directed A B C (HAeff:effective_order A) (HBeff:effective_order B) (S:erel B C) (R:erel A B) :
  (forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R) ->
  (forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S) ->
  directed_rel B C HBeff S -> directed_rel A B HAeff R ->
  directed_rel A C HAeff (compose_rel HBeff S R).
Proof.
  intros HR HS. intros.
  repeat intro.
  assert (exists G:finset (B×C),
    (forall b c, (b,c) ∈ G -> (x,b) ∈ R /\ (b,c) ∈ S) /\
    (forall c, (exists b, (b,c) ∈ G) <-> c ∈ M)).
  induction M.
  exists nil. split; simpl; intros.
  apply nil_elem in H2; elim H2.
  split; intuition.
  destruct H2 as [??]. apply nil_elem in H2; elim H2.
  apply nil_elem in H2; elim H2.
  assert (a ∈ ((a::M)%list:finset C)).
  apply cons_elem; auto.
  apply H1 in H2.
  apply erel_image_elem in H2.
  apply compose_elem in H2.
  destruct H2 as [y [??]].
  destruct IHM as [G ?].
  red; intros. apply H1.
  apply cons_elem; auto.
  exists ((y,a)::G)%list.
  split. intros.
  apply cons_elem in H5.
  destruct H5.
  split. apply member_eq with (x,y); auto.
  destruct H5 as [[??][??]].
  split; split; auto.
  apply member_eq with (y,a); auto.
  destruct H4. apply H4; auto.
  intros. split; intros.
  destruct H5 as [p ?].
  apply cons_elem in H5.
  destruct H5.
  apply cons_elem. left.
  destruct H5 as [[??][??]].
  split; auto.
  apply cons_elem. right. apply H4; eauto.
  apply cons_elem in H5.
  destruct H5.
  exists y.
  apply cons_elem. left.
  destruct H5; split; split; auto.
  apply H4 in H5.
  destruct H5 as [p ?].
  exists p. apply cons_elem. auto.
  auto.

  destruct H2 as [G [??]].
  destruct (H0 x (image π₁ G)).
  red; intros.
  apply image_axiom2 in H4.
  destruct H4 as [y [??]].
  destruct y. apply H2 in H4.
  apply erel_image_elem. destruct H4.
  apply member_eq with (x,c); auto.
  simpl in H5.
  destruct H5; split; split; auto.
  destruct H4.  
  apply erel_image_elem in H5.
  destruct (H x0 (image π₂ G)).
  red; intros.
  apply image_axiom2 in H6.
  destruct H6 as [y [??]].
  destruct y.
  generalize H6; intros H6'.
  apply H2 in H6.
  apply erel_image_elem.
  destruct H6.
  apply HS with c c0; auto.
  apply H4.
  change c with (π₁#((c,c0):B×C)).
  apply image_axiom1. auto.
  destruct H6.
  apply erel_image_elem in H7.
  exists x1. split; auto.
  red; intros.
  apply H3 in H8.
  destruct H8.
  apply H6.
  change x2 with (π₂#((x3,x2):B×C)).
  apply image_axiom1. auto.
  apply erel_image_elem.
  apply compose_elem; auto.
  exists x0. split; auto.
Qed.


Lemma compose_assoc A B C D (HBeff:effective_order B) (HCeff:effective_order C)
  (T:erel C D) (S:erel B C) (R:erel A B) :
  compose_rel HCeff T (compose_rel HBeff S R) ≈
  compose_rel HBeff (compose_rel HCeff T S) R.
Proof.
  unfold compose_rel.
  split; red; simpl; intros.
  apply image_axiom2 in H.
  destruct H as [q [??]].
  apply esubset_dec_elem in H.
  destruct H.
  destruct q as [q1 q2]; simpl in *.
  apply elem_eprod in H. destruct H.
  apply image_axiom2 in H.
  destruct H as [q' [??]].
  apply esubset_dec_elem in H.
  destruct H.
  destruct q' as [q1' q2']. simpl in *.
  apply elem_eprod in H. destruct H.
  assert ((a:A×D) ≈ (fst q1', snd q2)).
  rewrite H0.
  split; split; simpl; auto.
  destruct H3. destruct H3; auto.
  destruct H3. destruct H6; auto.
  rewrite H6.
  change (fst q1',snd q2) with
    ((mk_pair (π₁ ∘ π₁) (π₂ ∘ π₂))# ((q1',(fst q2',snd q2)) : (A×B)×(B×D))).
  apply image_axiom1.
  apply esubset_dec_elem.
  clear.
  intros. destruct H as [[[??][??]][[??][??]]].
  eauto.
  split.
  apply elem_eprod. split.
  auto.
  change (fst q2',snd q2) with
    ((mk_pair (π₁ ∘ π₁) (π₂ ∘ π₂))# ((q2',q2) : (B×C)×(C×D))).
  apply image_axiom1.
  apply esubset_dec_elem.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]]; eauto.
  split; simpl; auto.
  apply elem_eprod; auto.
  transitivity (snd q1); auto.
  rewrite H0 in H6.
  destruct H3.
  destruct H3; auto.
  simpl. auto.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]]; eauto.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]]; eauto.
  
  apply image_axiom2 in H.  
  destruct H as [q [??]].
  apply esubset_dec_elem in H. destruct H.
  destruct q as [q1 q2].
  apply elem_eprod in H. destruct H.
  apply image_axiom2 in H2.
  destruct H2 as [q' [??]].
  apply esubset_dec_elem in H2. destruct H2.
  destruct q' as [q1' q2'].
  apply elem_eprod in H2. destruct H2.
  simpl in *.
  assert ((a:A×D) ≈ 
    (mk_pair (π₁ ∘ π₁) (π₂ ∘ π₂))#
    (((fst q1, snd q1'), q2'):((A×C)×(C×D)))).
  simpl.
  rewrite H0.
  split; split; simpl; auto.
  destruct H3. destruct H3; auto.
  destruct H3. destruct H6; auto.
  rewrite H6.
  apply image_axiom1.
  apply esubset_dec_elem.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]]; eauto.
  split; simpl; auto.
  apply elem_eprod. split; auto.
  change (fst q1, snd q1') with
    ((mk_pair (π₁ ∘ π₁) (π₂ ∘ π₂))#
     ((q1, q1'):((A×B)×(B×C)))).
  apply image_axiom1.
  apply esubset_dec_elem.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]]; eauto.
  split; simpl; auto.
  apply elem_eprod; auto.
  transitivity (fst q2); auto.
  destruct H3.
  destruct H7; auto.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]]; eauto.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]]; eauto.
Qed.
  
Lemma compose_ident_rel2 : forall A B HBeff (f:erel A B),
  (forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ f -> (x',y') ∈ f) ->
  compose_rel HBeff f (ident_rel HBeff) ≈ f.
Proof.
  intros. split.
  red; simpl; intros.
  unfold compose_rel in H0.
  apply image_axiom2 in H0.
  destruct H0 as [q [??]].
  apply esubset_dec_elem in H0.
  destruct H0.
  destruct q.
  apply elem_eprod in H0. destruct H0.
  simpl in *.
  unfold ident_rel in H0.
  apply esubset_dec_elem in H0.
  destruct H0.
  destruct c. simpl in *.
  destruct a.
  destruct c0. simpl in *.
  apply H with c0 c4; auto.
  transitivity c1; auto.  
  transitivity c; auto.  
  destruct H1. destruct H5; auto.
  destruct H1. destruct H1; auto.
  clear.
  intros. destruct H as [[??][??]]. eauto.
  clear.
  intros. destruct H as [[[??][??]][[??][??]]]. eauto.
  
  red; simpl; intros.
  unfold compose_rel.
  destruct a.
  change (c,c0) with
    ((mk_pair (π₁ ∘ π₁) (π₂ ∘ π₂))# (((c,c),(c,c0)) : (A×A)×(A×B))).
  apply image_axiom1.
  apply esubset_dec_elem.
  clear.
  intros. destruct H as [[[??][??]][[??][??]]]. eauto.
  simpl; split; auto.
  apply elem_eprod. split; auto.
  unfold ident_rel.
  apply esubset_dec_elem.
  clear.
  intros. destruct H as [[??][??]]. eauto.
  split; simpl; auto.
  apply elem_eprod; split; apply eff_complete; auto.
Qed.

Lemma compose_ident_rel1 : forall A B HAeff (f:erel A B),
  (forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ f -> (x',y') ∈ f) ->
  compose_rel HAeff (ident_rel HAeff) f ≈ f.
Proof.
  intros. split.
  red; simpl; intros.
  unfold compose_rel in H0.
  apply image_axiom2 in H0.
  destruct H0 as [q [??]].
  apply esubset_dec_elem in H0.
  destruct H0.
  destruct q.
  apply elem_eprod in H0. destruct H0.
  simpl in *.
  unfold ident_rel in H3.
  apply esubset_dec_elem in H3.
  destruct H3.
  destruct c0. simpl in *.
  destruct a.
  destruct c. simpl in *.
  apply H with c c4; auto.
  destruct H1. destruct H5; auto.
  transitivity c1; auto.
  destruct H1. destruct H1; auto.
  transitivity c0; auto.
  intros.
  destruct H4. destruct H4. destruct H6.
  transitivity (snd x); auto.
  transitivity (fst x); auto.
  intros.
  destruct H2. destruct H2. destruct H4.
  destruct H2. destruct H5. destruct H4. destruct H6.
  eauto.
  
  red; simpl; intros.
  unfold compose_rel.
  destruct a.
  change (c,c0) with
    ((mk_pair (π₁ ∘ π₁) (π₂ ∘ π₂))# (((c,c0),(c0,c0)) : (A×B)×(B×B))).
  apply image_axiom1.
  apply esubset_dec_elem.
  intros.
  destruct H1. destruct H1. destruct H1. destruct H4.
  destruct H3. destruct H3. destruct H7.
  eauto.
  simpl; split; auto.
  apply elem_eprod. split; auto.
  unfold ident_rel.
  apply esubset_dec_elem.
  intros.
  destruct H1. destruct H1. destruct H3. eauto.
  split; simpl; auto.
  apply elem_eprod; split; apply eff_complete; auto.
Qed.


Definition apply_acceptable (A B:preord) 
  (tuple:(joinable_rel_order A B × A) × B) :=
  match tuple with
  | ((R,a),b) => exists a' b', (a',b') ∈ proj1_sig R /\ a' ≤ a /\ b ≤ b'
  end.

Lemma apply_acceptable_dec (A B:preord)
  (HAeff:effective_order A)
  (HBeff:effective_order B) :
  forall t, {apply_acceptable A B t} + { ~apply_acceptable A B t}.
Proof.  
  intros.
  destruct t as [[R a] b].
  destruct (finset_find_dec (A×B) (fun x => a ≥ π₁#x /\ π₂#x ≥ b))
    with (proj1_sig R).
  intros.  destruct H0; split.
  rewrite <- H; auto.
  rewrite <- H; auto.
  intros.
  destruct x as [a' b']. simpl.
  destruct (eff_ord_dec A HAeff a' a).
  destruct (eff_ord_dec B HBeff b b').
  left. split; auto.
  right. intros [??]; apply n; auto.
  right. intros [??]; apply n; auto.
  destruct s as [z [?[??]]].
  left. red. destruct z as [a' b']. simpl in *.
  exists a'. exists b'. auto.
  right. intro.
  hnf in H.
  destruct H as [a' [b' [?[??]]]].
  apply (n (a',b')); auto.
Qed.

Lemma apply_acceptable_ok (A B:preord) :
  forall x y, x ≈ y -> apply_acceptable A B x -> apply_acceptable A B y.
Proof.
  unfold apply_acceptable.
  clear; intros.
  destruct x; destruct y.
  destruct c; destruct c1.
  destruct H0 as [a' [b' [?[??]]]].
  destruct H.
  destruct H. destruct H. simpl in *.
  destruct (H a' b') as [p [q [?[??]]]]; auto.
  exists p. exists q. split; auto.
  split.
  transitivity a'; auto.
  transitivity c3; auto.
  transitivity b'; auto.
  transitivity c0; auto.
  destruct H3. auto.
Qed.  



Definition apply_rel (A B:preord) 
  (HAeff:effective_order A)
  (HBeff:effective_order B)
  (HAplt:plotkin_order A)
  : erel (joinable_rel_order A B × A) B :=
      esubset_dec _ (apply_acceptable A B) (apply_acceptable_dec A B HAeff HBeff)
         (eprod 
             (eprod (eff_enum _ (joinable_rel_effective A B HAeff HBeff HAplt))
                    (eff_enum A HAeff))
             (eff_enum B HBeff)).

Lemma apply_rel_elem A B HAeff HBeff HAplt :
  forall x y R,
    ((R,x),y) ∈ apply_rel A B HAeff HBeff HAplt <->
    exists x', exists y', (x',y') ∈ proj1_sig R /\ x' ≤ x /\ y ≤ y'.
Proof.
  intros. split; intros.
  unfold apply_rel in H.
  apply esubset_dec_elem in H. destruct H.
  red in H0. auto.
  apply apply_acceptable_ok.
  destruct H as [x' [y' [?[??]]]].
  unfold apply_rel.
  apply esubset_dec_elem.
  apply apply_acceptable_ok.
  split.
  apply elem_eprod. split.
  apply elem_eprod.
  split; apply eff_complete.
  apply eff_complete.
  red. eauto.
Qed.

Lemma apply_rel_ordering (A B:preord) 
  (HAeff:effective_order A)
  (HBeff:effective_order B)
  (HAplt:plotkin_order A) :
  forall R R' b b',
    R ≤ R' ->
    b' ≤ b -> 
    (R,b) ∈ apply_rel A B HAeff HBeff HAplt ->
    (R',b') ∈ apply_rel A B HAeff HBeff HAplt.
Proof.
  intros.
  destruct R.
  apply apply_rel_elem in H1.
  destruct R'.
  apply apply_rel_elem .
  destruct H1 as [x' [y' [?[??]]]].
  destruct H. simpl in *.
  destruct (H x' y') as [p [q [?[??]]]]; auto.
  exists p. exists q. split; auto.
  split.
  transitivity x'; auto.
  transitivity c0; auto.
  transitivity y'; auto.
  transitivity b; auto.
Qed.  


Lemma apply_rel_dir (A B:preord) 
  (HAeff:effective_order A)
  (HBeff:effective_order B)
  (HAplt:plotkin_order A) :
  directed_rel 
    ((joinable_rel_order A B)×A) B
    (effective_prod (joinable_rel_effective A B HAeff HBeff HAplt) HAeff)
    (apply_rel A B HAeff HBeff HAplt).
Proof.
  intros [R a] X ?.
  assert (forall b, b ∈ X -> apply_acceptable A B (R,a,b)).
  intros.
  apply H in H0.
  apply erel_image_elem in H0.
  unfold apply_rel in H0.
  apply esubset_dec_elem in H0.
  destruct H0; auto.
  apply apply_acceptable_ok.
  unfold apply_acceptable in H0.
  rename a into z.

  assert (exists G:finset (A×B), G ⊆ proj1_sig R /\
    (forall a b, (a,b) ∈ G -> a ≤ z /\ exists b', b' ≤ b /\ b' ∈ X) /\
    (forall b', b' ∈ X -> exists a b, b' ≤ b /\ (a,b) ∈ G)).
  clear H.
  induction X.
  exists nil. split.
  red; intros. apply nil_elem in H. elim H.
  split; simpl; intros.
  apply nil_elem in H. elim H.
  apply nil_elem in H. elim H.
  destruct IHX as [G [?[??]]]; auto.
  intros. apply H0. apply cons_elem; auto.
  destruct (H0 a) as [a' [b' [?[??]]]].
  apply cons_elem; auto.
  exists ((a',b')::G)%list.
  split.
  red; intros.
  apply cons_elem in H6. destruct H6.
  rewrite H6; auto.
  apply H. auto.
  split; intros.
  apply cons_elem in H6.
  destruct H6.
  split.
  transitivity a'; auto.
  destruct H6 as [[??][??]]; auto.
  exists a. split.
  transitivity b'; auto.
  destruct H6 as [[??][??]]; auto.
  apply cons_elem. auto.
  destruct (H1 a0 b) as [? [q ?]]; auto. destruct H8.
  split; auto.
  exists q. split; auto.
  apply cons_elem; auto.
  apply cons_elem in H6. destruct H6.
  exists a'. exists b'.
  rewrite H6.
  split; auto.
  apply cons_elem; auto.
  destruct (H2 b'0) as [p [q [??]]]; auto.
  exists p. exists q. split; auto.
  apply cons_elem; auto.
  destruct H1 as [G [?[??]]].
  assert (is_joinable_relation (proj1_sig R)). apply proj2_sig.
  destruct (mub_complete A HAplt (image π₁ G) z).
  red; intros.
  apply image_axiom2 in H5.
  destruct H5 as [y [??]].
  destruct y.
  destruct (H2 c c0) as [? [b' [??]]]; auto.
  rewrite H6; simpl.
  generalize H8; intros; auto.
  destruct H5.
  destruct (H4 G) with x as [y [??]]; auto.
  exists y. split.
  red; intros.
  destruct (H3 x0) as [p [q [??]]]; auto.
  transitivity q. auto.
  apply H8.
  change q with (π₂#((p,q):A×B)).
  apply image_axiom1. auto.
  apply erel_image_elem.
  unfold apply_rel.
  apply esubset_dec_elem.
  apply apply_acceptable_ok.
  split. apply elem_eprod. split.
  apply elem_eprod. split; apply eff_complete. apply eff_complete.
  red. exists x. exists y.
  split; auto.
Qed.

Definition pair_rel {A B C:preord} (HCeff:effective_order C) 
  (R:erel C A) (S:erel C B) : erel C (A×B) :=
  image (mk_pair (π₁ ∘ π₁) (mk_pair (π₂ ∘ π₁) (π₂ ∘ π₂)))
   (esubset_dec _ (fun x => fst (fst x) ≈ fst (snd x))
            (fun x => PREORD_EQ_DEC _ (OrdDec _ (eff_ord_dec _ HCeff)) (fst (fst x)) (fst (snd x)))
    (eprod R S)).

Definition pair_rel' {A B C D:preord}
  (R:erel A B) (S:erel C D) : erel (A×C) (B×D) :=
  image (mk_pair 
          (mk_pair (π₁ ∘ π₁) (π₁ ∘ π₂))           
          (mk_pair (π₂ ∘ π₁) (π₂ ∘ π₂)))
    (eprod R S).

Program Definition const {A B:preord} (b:B) : A → B :=
  Preord.Hom A B (fun _ => b) _.
Next Obligation. auto. Qed.

Definition inset_decset (A:preord) (HA:effective_order A) (X:eset A) (x:A) 
  : eset unitpo :=
  image (const tt) (esubset_dec _ _
    (PREORD_EQ_DEC _ (OrdDec _ (eff_ord_dec _ HA)) x) X).

Program Definition in_semidec (A:preord) (HA:effective_order A) (X:eset A)
  : semidec (fun x => x ∈ X) 
  := Semidec _ _ (inset_decset A HA X) _ _.
Next Obligation.
  intros. rewrite <- H; auto.
Qed.
Next Obligation.
  intros.
  split; intros.
  unfold inset_decset in H.
  apply image_axiom2 in H.
  destruct H as [y [??]].
  apply esubset_dec_elem in H.
  destruct H.
  rewrite H1; auto.
  intros. rewrite H2. auto.
  unfold inset_decset.
  destruct x.
  change tt with (const tt # a).
  apply image_axiom1.
  apply esubset_dec_elem.
  eauto.
  split; auto.
Qed.

Lemma all_finset_setdec_elem : forall A P X a
  (HP:forall x y a, x ≈ y -> a ∈ P x -> a ∈ P y),
  (a ∈ all_finset_setdec A P X <->
   (forall x, x ∈ X -> a ∈ P x)).
Proof.
  intros. induction X; simpl; intros.
  split; simpl; intros.
  destruct H0 as [?[??]]. elim H0.
  apply single_axiom. destruct a; auto.
  split; intros.
  apply intersection_elem in H.
  destruct H.
  rewrite IHX in H1.
  destruct H0 as [q [??]].
  simpl in H0; destruct H0; subst.
  apply HP with q; auto.
  apply H1.
  exists q; split; auto.
  apply intersection_elem.
  split.
  apply H.
  exists a0. split; simpl; auto.
  rewrite IHX.
  intros. apply H.
  destruct H0 as [q[??]].
  exists q; split; simpl; auto.
Qed.

Section curry.
  Variables A B C:preord.
  Variable HAeff:effective_order A.
  Variable HBeff:effective_order B.
  Variable HCeff:effective_order C.
  Variable HAplt:plotkin_order A.

  Variable R:erel (C×A) B.
  Hypothesis HR :
    forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R.

  Definition curry_acceptable (tuple:C×(joinable_rel_order A B)) :=
    match tuple with
    | (c,R') => forall ab, ab ∈ proj1_sig R' -> ((c,fst ab),snd ab) ∈ R
    end.

  Let Reff : effective_order ((C×A)×B) :=
    effective_prod (effective_prod HCeff HAeff) HBeff.

  Definition curry_acceptable_decset (tuple: C × (joinable_rel_order A B)) :=
    match tuple with
    | (c,R') => 
        all_finset_setdec (A×B) 
             (fun ab => inset_decset ((C×A)×B) Reff R
                        (((c,fst ab),snd ab):((C×A)×B))) (proj1_sig R')
    end.

  Program Definition  curry_acceptable_semidec : semidec curry_acceptable
    := Semidec _ _ curry_acceptable_decset _ _.
  Next Obligation.
    unfold curry_acceptable; intros.
    destruct x; destruct y. intros.
    destruct H. destruct H; destruct H2. simpl in *.
    destruct ab as [a b].
    destruct (H4 a b) as [p [q [?[??]]]]; auto.
    generalize (H0 (p,q) H5). simpl.
    apply HR; auto.
    split; auto.
  Qed.
  Next Obligation.
    intros. split; intros.
    destruct a as [c R'].
    red. intros [a b]. simpl; intros.
    unfold curry_acceptable_decset in H.
    rewrite all_finset_setdec_elem in H.
    apply H in H0.
    simpl in H0.
    unfold inset_decset in H0.
    apply image_axiom2 in H0.
    destruct H0 as [y [??]].
    apply esubset_dec_elem in H0.
    destruct H0.
    rewrite <- H2 in H0.
    auto.
    intros. eauto.
    intros.
    apply in_semidec_obligation_2 in H2.
    apply in_semidec_obligation_2.
    apply member_eq with (c,fst x0, snd x0); auto.
    destruct H1 as [[??][??]]; split; split; simpl; auto; split; auto.

    unfold curry_acceptable_decset.
    destruct a as [c R'].
    rewrite all_finset_setdec_elem.
    intros [a b] ?.
    unfold inset_decset.
    destruct x.
    simpl fst. simpl snd.
    change tt with (const tt # ((c,a,b):((C×A)×B))).
    apply image_axiom1.
    apply esubset_dec_elem.
    intros. eauto.
    split; auto.
    red in H.
    apply H in H0. simpl in H0. auto.
    clear; intros.
    apply in_semidec_obligation_2 in H0.
    apply in_semidec_obligation_2.
    apply member_eq with (c,fst x, snd x); auto.
    destruct H as [[??][??]]; split; split; simpl; auto; split; auto.
  Qed.

  Definition curry_rel : erel C (joinable_rel_order A B) :=
    esubset _ curry_acceptable_semidec 
      (eprod (eff_enum C HCeff)
             (eff_enum _ (joinable_rel_effective A B HAeff HBeff HAplt))).

  Lemma curry_rel_elem : forall c (R':joinable_relation A B),
    (c,R') ∈ curry_rel <-> (forall a b, (a,b) ∈ proj1_sig R' -> ((c,a),b) ∈ R).
  Proof.
    intros. split; intros.
    unfold curry_rel in H.
    apply esubset_elem in H. destruct H.
    red in H1.
    apply H1 in H0. auto.
    unfold curry_rel.
    apply esubset_elem. split.
    apply elem_eprod.
    split; apply eff_complete.
    red; simpl; intros.
    destruct ab. simpl.
    apply H; auto.
  Qed.

  Lemma curry_rel_ordering : 
    forall x x' y y',
      x ≤ x' ->
      y' ≤ y ->
      (x,y) ∈ curry_rel ->
      (x',y') ∈ curry_rel.
  Proof.
    intros. 
    rewrite curry_rel_elem in H1.
    rewrite curry_rel_elem.
    intros.
    destruct (H0 a b) as [a' [b' [?[??]]]]; auto.
    apply HR with (x,a') b'; auto.
    split; auto.
  Qed.

  Hypothesis HRdir : directed_rel (C×A) B (effective_prod HCeff HAeff) R.
  Variable HBplt:plotkin_order B.

  Let R' c :=
    image (mk_pair (π₂ ∘ π₁) π₂)
    (esubset_dec ((C×A)×B) (fun q => fst (fst q) ≈ c) 
    (fun q => 
      PREORD_EQ_DEC _ (OrdDec C (eff_ord_dec C HCeff)) (fst (fst q)) c)
    R).

  Lemma R'_R : forall a b c, 
    ((c,a),b) ∈ R <-> (a,b) ∈ R' c.
  Proof.
    intros; split; intros.
    unfold R'.
    change (a,b) with
    (mk_pair (π₂ ∘ π₁) π₂ # (((c,a),b):((C×A)×B))).
    apply image_axiom1.
    apply esubset_dec_elem.
    intros.
    rewrite <- H1.
    destruct H0 as [[??][??]].
    destruct H0. destruct H3.
    split; auto.
    split; auto.
    unfold R' in H.
    apply image_axiom2 in H.
    destruct H as [[[m n] r] [??]].
    apply esubset_dec_elem in H.
    destruct H. simpl in H1. simpl in H0.
    apply member_eq with (m,n,r); auto.
    destruct H0 as [[??][??]]. destruct H1. simpl in *.
    split; split; simpl; auto.
    split; auto. split; auto.
    intros.
    rewrite <- H2.
    destruct H1 as [[??][??]].
    destruct H1. destruct H4.
    split; auto.
  Qed.

  Lemma curry_rel_dir :
    directed_rel C (joinable_rel_order A B) HCeff curry_rel.
  Proof.
    intros c X ?.
    destruct (directed_joinables A B HAeff HAplt HBeff HBplt (R' c)) with X
      as [Q [??]]; auto.
    intros.
    apply R'_R in H2. apply R'_R.
    apply HR with (c,x) y; auto.
    split; auto.
    intros a M HM.
    destruct (HRdir (c,a) M).
    red; intros.
    apply erel_image_elem.
    apply HM in H0.
    apply erel_image_elem in H0.
    apply R'_R in H0. auto.
    destruct H0.
    exists x. split; auto.
    apply erel_image_elem in H1.
    apply erel_image_elem. apply R'_R. auto.
    intros.
    apply H in H0.
    apply erel_image_elem in H0.
    rewrite curry_rel_elem in H0.
    red; intros.
    destruct a.
    apply R'_R.
    apply H0. auto.
    exists Q. split; auto.
    apply erel_image_elem.
    rewrite curry_rel_elem.
    intros.
    apply H1 in H2.
    apply R'_R in H2.
    auto.
  Qed.

  Lemma curry_apply :
    (compose_rel (effective_prod (joinable_rel_effective A B HAeff HBeff HAplt) HAeff)
           (apply_rel A B HAeff HBeff HAplt)
           (pair_rel' curry_rel (ident_rel HAeff)))
    ≈ R.
  Proof.
    split; red; simpl; intros.
    unfold compose_rel in H.
    apply image_axiom2 in H.
    destruct H as [q[??]].
    apply esubset_dec_elem in H. destruct H.
    destruct q as [q1 q2].
    simpl in H1.
    apply elem_eprod in H. destruct H.
    rewrite H0.
    simpl.
    unfold pair_rel' in H.
    apply image_axiom2 in H.
    destruct H as [q' [??]].
    simpl in H3.
    destruct q' as [q1' q2']. simpl in H3.
    apply elem_eprod in H. destruct H.
    unfold ident_rel in H4.
    apply esubset_dec_elem in H4. destruct H4.
    clear H4.    
    destruct q2 as [[??] ?].
    rewrite apply_rel_elem in H2.
    destruct H2 as [w [z [?[??]]]].
    destruct q1' as [??].
    rewrite curry_rel_elem in H.
    simpl. 
    
    assert (c ≤ c3).
    simpl in H1.
    destruct q1 as [[??][??]]; simpl in *.
    destruct H1. simpl in *.
    transitivity c6; auto.
    destruct H3. destruct H3. simpl in *.
    destruct H9; simpl in *; auto.
    destruct (H7 w z) as [w' [z' [?[??]]]]; auto.
    assert ((c2,w',z') ∈ R).
    apply H; auto.
    revert H11. apply HR.
    destruct q1. simpl.
    destruct c4. simpl.
    split; simpl.
    simpl in H3.
    destruct H3. destruct H11.
    simpl in *.
    destruct H11. auto.
    transitivity w; auto.
    transitivity c0; auto.
    simpl in H1.
    destruct c5. simpl in *.
    transitivity c7.
    destruct H1; auto.
    destruct H3.
    destruct H3. destruct H12. simpl in *.
    transitivity (snd q2'); auto.
    transitivity (fst q2'); auto.
    destruct H11. simpl in *.
    destruct H11. auto.
    transitivity z; auto.
    clear. intros.
    destruct H as [[??][??]]; eauto.
    clear. intros.
    destruct H as [[[??][??]][[??][??]]]; eauto.
    
    unfold compose_rel.
    destruct a as [[c a] b].
    assert (exists R':joinable_relation A B,
      (a,b) ∈ proj1_sig R' /\
      (forall x y, (x,y) ∈ proj1_sig R' -> ((c,x),y) ∈ R)).

      destruct (swell A B HAeff HAplt HBeff HBplt (R' c)) with ((a,b)::nil)%list
        as [G [?[??]]].
      intros. apply R'_R in H2. apply R'_R.
      apply HR with (c,x) y; auto.
      split; auto.
      intros z M ?. 
      destruct (HRdir (c,z) M).
      red; intros. apply H0 in H1.
      apply erel_image_elem in H1. apply R'_R in H1.
      apply erel_image_elem. auto.
      destruct H1.
      exists x; split; auto.
      apply erel_image_elem in H2.
      apply erel_image_elem. apply R'_R. auto.
      red; intros.
      apply cons_elem in H0. destruct H0.
      rewrite H0. apply R'_R. auto.
      apply nil_elem in H0. elim H0.
      exists (exist _ G H2).
      split; simpl; auto.
      apply H0. apply cons_elem; auto.
      intros.
      apply R'_R. apply H1. auto.

    destruct H0 as [S ?].
    change (c,a,b) with
      (mk_pair (π₁ ∘ π₁) (π₂ ∘ π₂) #
        ( ( ((c,a),(S,a)), ((S,a),b) )
        : (((C×A) × joinable_rel_order A B × A) ×
            (joinable_rel_order A B × A) × B)
        )).
    apply image_axiom1.
    apply esubset_dec_elem.
    clear. intros.
    destruct H as [[[??][??]][[??][??]]]; eauto.
    split; simpl; auto.
    apply elem_eprod. split.
    unfold pair_rel'.
    change (c,a,(S,a)) with
      ((mk_pair (mk_pair (π₁ ∘ π₁) (π₁ ∘ π₂)) (mk_pair (π₂ ∘ π₁) (π₂ ∘ π₂)))
      #
      ( ((c,S),(a,a))
      :  (C × joinable_rel_order A B) × (A×A)
      )).
    apply image_axiom1.
    apply elem_eprod. split.
    rewrite curry_rel_elem.
    intros.
    destruct H0; auto.
    unfold ident_rel.
    apply esubset_dec_elem.
    clear. intros. destruct H as [[??][??]]; eauto.
    split; simpl; auto.
    apply elem_eprod. split; apply eff_complete.
    apply apply_rel_elem.
    exists a. exists b. intuition.
  Qed.
End curry.
