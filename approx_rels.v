(* Copyright (c) 2014, Robert Dockins *)

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

(**  * Constructions of approximable relations for the category PLT.

     In this module we construct approxmiable relations to be used in
     the construction of the category PLT in profinite.v.

     These include : identity, composition, pairing, pair projection,
     sum injection, sum case analysis, and the curry and apply operations.
  
     All these relations work uniformly in both the category of pointed
     and unpointed effective Plotkin orders.
  *)

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
  apply eprod_elem. split; apply eff_complete.
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
  apply eprod_elem in H.
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
  apply eprod_elem; auto.
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
  apply eprod_elem; split; apply eff_complete.
  transitivity y; auto.
  transitivity x; auto.
  clear. intros. destruct H as [[??][??]]; eauto.
Qed.

Definition directed_rel hf A B (HAeff:effective_order A) (R:erel A B):=
  forall x, directed hf (erel_image A B (OrdDec A (eff_ord_dec A HAeff)) R x).  

Lemma ident_image_dir hf A (HAeff:effective_order A) : directed_rel hf A A HAeff (ident_rel HAeff).
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
  apply eprod_elem; split; apply eff_complete.
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
  apply eprod_elem in H3.
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
  apply eprod_elem. split; auto.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]]; eauto.
Qed.  

Lemma compose_directed hf A B C (HAeff:effective_order A) (HBeff:effective_order B) (S:erel B C) (R:erel A B) :
  (forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R) ->
  (forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S) ->
  directed_rel hf B C HBeff S ->
  directed_rel hf A B HAeff R ->
  directed_rel hf A C HAeff (compose_rel HBeff S R).
Proof.
  intros HR HS. intros.
  repeat intro.
  assert (exists G:finset (B×C),
    (forall b c, (b,c) ∈ G -> (x,b) ∈ R /\ (b,c) ∈ S) /\
    (forall c, (exists b, (b,c) ∈ G) <-> c ∈ M)).
  clear Hinh.
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
  apply inh_image; auto.
  destruct hf; auto.
  destruct Hinh as [z ?].
  apply H3 in H4.
  destruct H4. red; eauto.

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
  apply inh_image; auto.
  destruct hf; auto.
  destruct Hinh as [z ?].
  apply H3 in H6.
  destruct H6. red; eauto.

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
  apply eprod_elem in H. destruct H.
  apply image_axiom2 in H.
  destruct H as [q' [??]].
  apply esubset_dec_elem in H.
  destruct H.
  destruct q' as [q1' q2']. simpl in *.
  apply eprod_elem in H. destruct H.
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
  apply eprod_elem. split.
  auto.
  change (fst q2',snd q2) with
    ((mk_pair (π₁ ∘ π₁) (π₂ ∘ π₂))# ((q2',q2) : (B×C)×(C×D))).
  apply image_axiom1.
  apply esubset_dec_elem.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]]; eauto.
  split; simpl; auto.
  apply eprod_elem; auto.
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
  apply eprod_elem in H. destruct H.
  apply image_axiom2 in H2.
  destruct H2 as [q' [??]].
  apply esubset_dec_elem in H2. destruct H2.
  destruct q' as [q1' q2'].
  apply eprod_elem in H2. destruct H2.
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
  apply eprod_elem. split; auto.
  change (fst q1, snd q1') with
    ((mk_pair (π₁ ∘ π₁) (π₂ ∘ π₂))#
     ((q1, q1'):((A×B)×(B×C)))).
  apply image_axiom1.
  apply esubset_dec_elem.
  clear. intros.
  destruct H as [[[??][??]][[??][??]]]; eauto.
  split; simpl; auto.
  apply eprod_elem; auto.
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
  apply eprod_elem in H0. destruct H0.
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
  apply eprod_elem. split; auto.
  unfold ident_rel.
  apply esubset_dec_elem.
  clear.
  intros. destruct H as [[??][??]]. eauto.
  split; simpl; auto.
  apply eprod_elem; split; apply eff_complete; auto.
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
  apply eprod_elem in H0. destruct H0.
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
  apply eprod_elem. split; auto.
  unfold ident_rel.
  apply esubset_dec_elem.
  intros.
  destruct H1. destruct H1. destruct H3. eauto.
  split; simpl; auto.
  apply eprod_elem; split; apply eff_complete; auto.
Qed.


(****************)

Program Definition iota1_rel (A B:preord)
  (HA:effective_order A) : erel A (sum_preord A B) :=
  image (Preord.Hom (A×A) (A×sum_preord A B) (fun x => (fst x, inl (snd x))) _)
  (esubset_dec 
    (A×A) (fun x => fst x ≥ snd x)
    (fun x => eff_ord_dec A HA (snd x) (fst x))
    (eprod (eff_enum A HA) (eff_enum A HA))).
Next Obligation.
  intros.
  destruct H; split; simpl; auto.
Qed.

Program Definition iota2_rel (A B:preord)
  (HB:effective_order B) : erel B (sum_preord A B) :=
  image (Preord.Hom (B×B) (B×sum_preord A B) (fun x => (fst x, inr (snd x))) _)
  (esubset_dec 
    (B×B) (fun x => fst x ≥ snd x)
    (fun x => eff_ord_dec B HB (snd x) (fst x))
    (eprod (eff_enum B HB) (eff_enum B HB))).
Next Obligation.
  intros.
  destruct H; split; simpl; auto.
Qed.

Program Definition sum_cases (C A B:preord)
  (f: erel A C) (g:erel B C) : erel (sum_preord A B) C :=
  union2
    (image (Preord.Hom (A×C) (sum_preord A B × C) (fun x => (inl (fst x), snd x)) _) f)
    (image (Preord.Hom (B×C) (sum_preord A B × C) (fun x => (inr (fst x), snd x)) _) g).
Next Obligation.
  simpl; intros.
  destruct H; split; simpl; auto.
Qed.
Next Obligation.
  simpl; intros.
  destruct H; split; simpl; auto.
Qed.

Lemma sum_cases_elem (C A B:preord) (f:erel A C) (g:erel B C) x y :
  (x,y) ∈ sum_cases C A B f g <-> 
  match x with
  | inl a => (a,y) ∈ f
  | inr b => (b,y) ∈ g
  end.
Proof.  
  split; intros.
  unfold sum_cases in H.
  apply union2_elem in H.
  destruct H; apply image_axiom2 in H; destruct H as [[??] [??]]; simpl in *.
  destruct x.
  apply member_eq with (c,c0); auto.
  destruct H0 as [[??][??]]. simpl in *. elim H0.
  destruct x.
  destruct H0 as [[??][??]]. simpl in *. elim H0.
  apply member_eq with (c,c0); auto.
  unfold sum_cases.
  apply union2_elem.
  destruct x.
  left. apply image_axiom1'; simpl. exists (c,y). split; auto.
  right. apply image_axiom1'; simpl. exists (c,y). split; auto.
Qed.


Lemma iota1_elem : forall A B HA x y,
  (x,y) ∈ iota1_rel A B HA <-> exists x', y ≈ inl x' /\ x' ≤ x.
Proof.
  intros; split; intros.
  unfold iota1_rel in H.
  apply image_axiom2 in H.
  destruct H as [[a a'] ?]. destruct H.
  simpl in H0.
  apply esubset_dec_elem in H. destruct H. simpl in *.
  exists a'. split.
  destruct H0 as [[??][??]]; split; auto.
  rewrite H1.   destruct H0 as [[??][??]]; auto.
  intros ? ? [[??][??]] ?; eauto.
  destruct H as [x' [??]].  
  unfold iota1_rel.
  apply image_axiom1'.
  simpl.
  exists (x, x'). simpl.
  split. split; split; auto.
  apply esubset_dec_elem.
  intros ? ? [[??][??]] ?; eauto.
  split; auto.  
  apply eprod_elem. split; apply eff_complete.
Qed.

Lemma iota2_elem : forall A B HB x y,
  (x,y) ∈ iota2_rel A B HB <-> exists x', y ≈ inr x' /\ x' ≤ x.
Proof.
  intros; split; intros.
  unfold iota2_rel in H.
  apply image_axiom2 in H.
  destruct H as [[a a'] ?]. destruct H.
  simpl in H0.
  apply esubset_dec_elem in H. destruct H. simpl in *.
  exists a'. split.
  destruct H0 as [[??][??]]; split; auto.
  rewrite H1.  destruct H0 as [[??][??]]; auto.
  intros ? ? [[??][??]] ?; eauto.
  destruct H as [x' [??]].  
  unfold iota2_rel.
  apply image_axiom1'.
  simpl.
  exists (x, x'). simpl.
  split. split; split; auto.
  apply esubset_dec_elem.
  intros ? ? [[??][??]] ?; eauto.
  split; auto.  
  apply eprod_elem. split; apply eff_complete.
Qed.
  

Lemma iota1_ordering (A B:preord) 
  (HAeff:effective_order A) :
  forall a a' b b',
    a ≤ a' ->
    b' ≤ b -> 
    (a,b) ∈ iota1_rel A B HAeff ->
    (a',b') ∈ iota1_rel A B HAeff.
Proof.
  intros.
  apply iota1_elem in H1. apply iota1_elem.
  destruct H1 as [x' [??]].
  rewrite H1 in H0.
  destruct b'. 2: elim H0.
  exists c. split; auto.
  transitivity x'; auto.
  transitivity a; auto.
Qed.

Lemma iota2_ordering (A B:preord) 
  (HBeff:effective_order B) :
  forall a a' b b',
    a ≤ a' ->
    b' ≤ b -> 
    (a,b) ∈ iota2_rel A B HBeff ->
    (a',b') ∈ iota2_rel A B HBeff.
Proof.
  intros.
  apply iota2_elem in H1.
  apply iota2_elem.
  destruct H1 as [x' [??]].
  rewrite H1 in H0.
  destruct b'. elim H0.
  exists c. split; auto.
  transitivity x'; auto.
  transitivity a; auto.
Qed.

Lemma sum_cases_ordering (C A B:preord) (f:erel A C) (g:erel B C) :
  (forall a a' b b', a ≤ a' -> b' ≤ b -> (a,b) ∈ f -> (a',b') ∈ f) ->
  (forall a a' b b', a ≤ a' -> b' ≤ b -> (a,b) ∈ g -> (a',b') ∈ g) ->
  (forall a a' b b', a ≤ a' -> b' ≤ b -> 
    (a,b) ∈ sum_cases C A B f g -> (a',b') ∈ sum_cases C A B f g).
Proof.
  intros.
  apply sum_cases_elem in H3. apply sum_cases_elem.
  destruct a; destruct a'.
  apply H with c b; auto.
  elim H1.
  elim H1.
  apply H0 with c b; auto.
Qed.

Lemma iota1_dir A B HAeff hf :
  directed_rel hf A (sum_preord A B) HAeff (iota1_rel A B HAeff).
Proof.
  intro. apply prove_directed.
  destruct hf. auto.
  simpl.
  exists (inl x).
  apply erel_image_elem.
  apply iota1_elem. exists x; split; auto.
  intros.
  apply erel_image_elem in H.
  apply erel_image_elem in H0.
  apply iota1_elem in H.
  apply iota1_elem in H0.
  destruct H as [p [??]].
  destruct H0 as [q [??]].
  exists (inl x).
  split. rewrite H. auto.
  split. rewrite H0. auto.
  apply erel_image_elem.
  apply iota1_elem. exists x; split; auto.
Qed.

Lemma iota2_dir A B HBeff hf :
  directed_rel hf B (sum_preord A B) HBeff (iota2_rel A B HBeff).
Proof.
  intro. apply prove_directed.
  destruct hf. auto.
  simpl.
  exists (inr x).
  apply erel_image_elem.
  apply iota2_elem. exists x; split; auto.
  intros.
  apply erel_image_elem in H.
  apply erel_image_elem in H0.
  apply iota2_elem in H.
  apply iota2_elem in H0.
  destruct H as [p [??]].
  destruct H0 as [q [??]].
  exists (inr x).
  split. rewrite H. auto.
  split. rewrite H0. auto.
  apply erel_image_elem.
  apply iota2_elem. exists x; split; auto.
Qed.

Lemma sum_cases_dir C A B HAeff HBeff hf (f:erel A C) (g:erel B C) :
  directed_rel hf A C HAeff f ->
  directed_rel hf B C HBeff g ->
  directed_rel hf (sum_preord A B) C (effective_sum HAeff HBeff) (sum_cases C A B f g).
Proof.
  intros. intro x.
  apply prove_directed.
  destruct hf. auto.
  destruct x.
  destruct (H c nil). hnf. auto.
  hnf; simpl; intros. apply nil_elem in H1. elim H1.
  destruct H1.
  apply erel_image_elem in H2.
  exists x. apply erel_image_elem.
  apply sum_cases_elem. auto.
  destruct (H0 c nil). hnf. auto.
  hnf; simpl; intros. apply nil_elem in H1. elim H1.
  destruct H1.
  apply erel_image_elem in H2.
  exists x. apply erel_image_elem.
  apply sum_cases_elem. auto.
  
  intros.
  apply erel_image_elem in H1.
  apply erel_image_elem in H2.
  apply sum_cases_elem in H1.
  apply sum_cases_elem in H2.
  destruct x.
  destruct (H c (x0::y::nil)%list).
  apply elem_inh with x0. apply cons_elem; auto.
  hnf; simpl; intros.
  apply erel_image_elem.
  apply cons_elem in H3. destruct H3.
  apply member_eq with (c,x0); auto.
  split; split; auto.
  apply cons_elem in H3. destruct H3.
  apply member_eq with (c,y); auto.
  split; split; auto.
  apply nil_elem in H3. elim H3.
  destruct H3.
  apply erel_image_elem in H4.
  exists x.
  split. apply H3. apply cons_elem; auto.
  split. apply H3. apply cons_elem. right. apply cons_elem; auto.
  apply erel_image_elem.
  apply sum_cases_elem. auto.

  destruct (H0 c (x0::y::nil)%list).
  apply elem_inh with x0. apply cons_elem; auto.
  hnf; simpl; intros.
  apply erel_image_elem.
  apply cons_elem in H3. destruct H3.
  apply member_eq with (c,x0); auto.
  split; split; auto.
  apply cons_elem in H3. destruct H3.
  apply member_eq with (c,y); auto.
  split; split; auto.
  apply nil_elem in H3. elim H3.
  destruct H3.
  apply erel_image_elem in H4.
  exists x.
  split. apply H3. apply cons_elem; auto.
  split. apply H3. apply cons_elem. right. apply cons_elem; auto.
  apply erel_image_elem.
  apply sum_cases_elem. auto.
Qed.

Lemma iota1_cases_commute C A B HAeff HBeff (f:erel A C) (g:erel B C) :
  (forall a a' b b', a ≤ a' -> b' ≤ b -> (a,b) ∈ f -> (a',b') ∈ f) ->
  compose_rel (effective_sum HAeff HBeff) 
      (sum_cases C A B f g) (iota1_rel A B HAeff) ≈ f.
Proof.
  intros Hf.
  split; hnf; simpl; intros.
  destruct a as [a c].
  apply compose_elem in H.
  destruct H as [x [??]].  
  apply iota1_elem in H.
  destruct H as [x' [??]].
  apply sum_cases_elem in H0.
  destruct x.
  apply Hf with c0 c; auto.
  transitivity x'; auto.
  destruct H. elim H.
  apply iota1_ordering.
  destruct a.
  apply compose_elem.
  apply iota1_ordering.
  exists (inl c).
  split.
  apply iota1_elem.
  exists c. split; auto.
  apply sum_cases_elem. auto.
Qed.

Lemma iota2_cases_commute C A B HAeff HBeff (f:erel A C) (g:erel B C) :
  (forall a a' b b', a ≤ a' -> b' ≤ b -> (a,b) ∈ g -> (a',b') ∈ g) ->
  compose_rel (effective_sum HAeff HBeff) 
      (sum_cases C A B f g) (iota2_rel A B HBeff) ≈ g.
Proof.
  intros Hg.
  split; hnf; simpl; intros.
  destruct a as [a c].
  apply compose_elem in H.
  destruct H as [x [??]].  
  apply iota2_elem in H.
  destruct H as [x' [??]].
  apply sum_cases_elem in H0.
  destruct x.
  destruct H. elim H.
  apply Hg with c0 c; auto.
  transitivity x'; auto.
  apply iota2_ordering.
  destruct a.
  apply compose_elem.
  apply iota2_ordering.
  exists (inr c).
  split.
  apply iota2_elem.
  exists c. split; auto.
  apply sum_cases_elem. auto.
Qed.

Lemma sum_cases_univ C A B HAeff HBeff (f:erel A C) (g:erel B C) (h:erel (sum_preord A B) C):
  (forall a a' b b', a ≤ a' -> b' ≤ b -> (a,b) ∈ h -> (a',b') ∈ h) ->
  compose_rel (effective_sum HAeff HBeff) h (iota1_rel A B HAeff) ≈ f ->
  compose_rel (effective_sum HAeff HBeff) h (iota2_rel A B HBeff) ≈ g ->
  sum_cases C A B f g ≈ h.
Proof.
  intros Hh Hh1 Hh2.
  split; hnf; simpl; intros.
  destruct a as [x c].
  apply sum_cases_elem in H.  
  destruct x.
  destruct Hh1. apply H1 in H.
  apply compose_elem in H.
  destruct H as [y [??]].
  apply iota1_elem in H.
  destruct H as [x' [??]].
  apply Hh with y c; auto.  
  transitivity (@inl A B x'); auto.
  apply iota1_ordering.
  destruct Hh2. apply H1 in H.
  apply compose_elem in H.
  destruct H as [y [??]].
  apply iota2_elem in H.
  destruct H as [x' [??]].
  apply Hh with y c; auto.  
  transitivity (@inr A B x'); auto.
  apply iota2_ordering.    
  destruct a.
  apply sum_cases_elem.
  destruct s.
  destruct Hh1. apply H0.
  apply compose_elem.
  apply iota1_ordering.
  exists (inl c0). split; auto.
  apply iota1_elem. exists c0; split; auto.
  destruct Hh2.
  apply H0.
  apply compose_elem.
  apply iota2_ordering.
  exists (inr c0). split; auto.
  apply iota2_elem. exists c0; split; auto.
Qed.


Definition apply_acceptable hf (A B:preord) 
  (tuple:(joinable_rel_order hf A B × A) × B) :=
  match tuple with
  | ((R,a),b) => exists a' b', (a',b') ∈ proj1_sig R /\ a' ≤ a /\ b ≤ b'
  end.

Lemma apply_acceptable_dec hf (A B:preord)
  (HAeff:effective_order A)
  (HBeff:effective_order B) :
  forall t, {apply_acceptable hf A B t} + { ~apply_acceptable hf A B t}.
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

Lemma apply_acceptable_ok hf (A B:preord) :
  forall x y, x ≈ y -> apply_acceptable hf A B x -> apply_acceptable hf A B y.
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



Definition apply_rel hf (A B:preord) 
  (HAeff:effective_order A)
  (HBeff:effective_order B)
  (HAplt:plotkin_order hf A)
  : erel (joinable_rel_order hf A B × A) B :=
      esubset_dec _ (apply_acceptable hf A B) (apply_acceptable_dec hf A B HAeff HBeff)
         (eprod 
             (eprod (eff_enum _ (joinable_rel_effective hf A B HAeff HBeff HAplt))
                    (eff_enum A HAeff))
             (eff_enum B HBeff)).

Lemma apply_rel_elem hf A B HAeff HBeff HAplt :
  forall x y R,
    ((R,x),y) ∈ apply_rel hf A B HAeff HBeff HAplt <->
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
  apply eprod_elem. split.
  apply eprod_elem.
  split; apply eff_complete.
  apply eff_complete.
  red. eauto.
Qed.

Lemma apply_rel_ordering hf (A B:preord) 
  (HAeff:effective_order A)
  (HBeff:effective_order B)
  (HAplt:plotkin_order hf A) :
  forall R R' b b',
    R ≤ R' ->
    b' ≤ b -> 
    (R,b) ∈ apply_rel hf A B HAeff HBeff HAplt ->
    (R',b') ∈ apply_rel hf A B HAeff HBeff HAplt.
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


Lemma apply_rel_dir hf (A B:preord) 
  (HAeff:effective_order A)
  (HBeff:effective_order B)
  (HAplt:plotkin_order hf A) :
  directed_rel hf
    ((joinable_rel_order hf A B)×A) B
    (effective_prod (joinable_rel_effective hf A B HAeff HBeff HAplt) HAeff)
    (apply_rel hf A B HAeff HBeff HAplt).
Proof.
  intros [R a] X Hinh ?.
  assert (forall b, b ∈ X -> apply_acceptable hf A B (R,a,b)).
  intros.
  red.
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
  clear H Hinh.
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
  assert (is_joinable_relation hf (proj1_sig R)). apply proj2_sig.
  destruct (mub_complete HAplt (image π₁ G) z).
  apply inh_image; auto.
  destruct hf; auto.
  destruct Hinh as [q ?].
  apply H3 in H5.
  destruct H5 as [a [b [??]]]. red; eauto.

  red; intros.
  apply image_axiom2 in H5.
  destruct H5 as [y [??]].
  destruct y.
  destruct (H2 c c0) as [? [b' [??]]]; auto.
  rewrite H6; simpl.
  generalize H8; intros; auto.
  destruct H5.
  destruct H4 as [HR H4].
  destruct (H4 G) with x as [y [??]]; auto.
  destruct hf; auto.
  destruct Hinh as [q ?].
  apply H3 in H7.
  destruct H7 as [a [b [??]]]; red; eauto.

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
  split. apply eprod_elem. split.
  apply eprod_elem. split; apply eff_complete. apply eff_complete.
  red. exists x. exists y.
  split; auto.
Qed.

Definition pair_rel {A B C:preord} (HCeff:effective_order C) 
  (R:erel C A) (S:erel C B) : erel C (A×B) :=
  image (mk_pair (π₁ ∘ π₁) (mk_pair (π₂ ∘ π₁) (π₂ ∘ π₂)))
   (esubset_dec _ (fun x => fst (fst x) ≈ fst (snd x))
            (fun x => PREORD_EQ_DEC _ (OrdDec _ (eff_ord_dec _ HCeff)) (fst (fst x)) (fst (snd x)))
    (eprod R S)).

Definition pi1_rel {A B:preord}
  (HA:effective_order A) (HB:effective_order B) 
  : erel (A×B) A :=
  esubset_dec 
    ((A×B)×A) (fun x => fst (fst x) ≥ snd x)
    (fun x => eff_ord_dec A HA (snd x) (fst (fst x)))
  (eprod (eprod (eff_enum A HA) (eff_enum B HB)) (eff_enum A HA)).

Definition pi2_rel {A B:preord}
  (HA:effective_order A) (HB:effective_order B) 
  : erel (A×B) B :=
  esubset_dec 
    ((A×B)×B) (fun x => snd (fst x) ≥ snd x)
    (fun x => eff_ord_dec B HB (snd x) (snd (fst x)))
  (eprod (eprod (eff_enum A HA) (eff_enum B HB)) (eff_enum B HB)).

Lemma pi1_rel_elem A B (HA:effective_order A) (HB:effective_order B) :
  forall a b a', ((a,b),a') ∈ pi1_rel HA HB <-> a ≥ a'.
Proof.
  intuition.
  unfold pi1 in H.
  apply esubset_dec_elem in H.
  destruct H. auto.
  clear; intros. destruct H as [[??][??]]. destruct H.
  simpl in *; eauto.
  unfold pi1.
  apply esubset_dec_elem.
  clear; intros. destruct H as [[??][??]]. destruct H.
  simpl in *; eauto.
  split; auto.
  apply eprod_elem. split.
  apply eprod_elem. split; apply eff_complete.
  apply eff_complete.
Qed.

Lemma pi2_rel_elem A B (HA:effective_order A) (HB:effective_order B) :
  forall a b b', ((a,b),b') ∈ pi2_rel HA HB <-> b ≥ b'.
Proof.
  intuition.
  unfold pi2 in H.
  apply esubset_dec_elem in H.
  destruct H. auto.
  clear; intros. destruct H as [[??][??]]. destruct H.
  simpl in *; eauto.
  unfold pi2.
  apply esubset_dec_elem.
  clear; intros. destruct H as [[??][??]]. destruct H.
  simpl in *; eauto.
  split; auto.
  apply eprod_elem. split.
  apply eprod_elem. split; apply eff_complete.
  apply eff_complete.
Qed.

Lemma pair_rel_elem  A B C (HCeff:effective_order C)
  (R:erel C A) (S:erel C B) :
  forall c x y, (c,(x,y)) ∈ pair_rel HCeff R S <-> ((c,x) ∈ R /\ (c,y) ∈ S).
Proof.
  intros. split; intros.
  unfold pair_rel in H.
  apply image_axiom2 in H.
  destruct H as [q [??]].
  destruct q.
  apply esubset_dec_elem in H. simpl in H0.
  destruct H. simpl in H1.
  apply eprod_elem in H.
  destruct H. split.
  apply member_eq with c0; auto.
  destruct H0 as [[??][??]]. simpl in*.
  destruct H1 as [??].
  destruct H5; destruct H3.
  split; split; simpl; auto.
  apply member_eq with c1; auto.
  destruct H0 as [[??][??]]. simpl in*.
  destruct H5; destruct H3.
  destruct H1.
  split; split; simpl; eauto.
  clear; intros.
  destruct H as [[[??][??]][[??][??]]].
  split; eauto.
  unfold pair_rel.
  change (c,(x,y)) with
      ((mk_pair (π₁ ∘ π₁) (mk_pair (π₂ ∘ π₁) (π₂ ∘ π₂)))
      #
      ( ((c,x),(c,y))
      :  (C × A) × (C×B)
      )).
  apply image_axiom1.
  apply esubset_dec_elem.
  clear; intros.
  destruct H as [[[??][??]][[??][??]]].
  split; eauto.
  split.
  apply eprod_elem. auto.
  simpl. auto.
Qed.

Lemma pi1_rel_ordering A B (HA:effective_order A) (HB:effective_order B) :
  forall x x' y y', x ≤ x' -> y' ≤ y ->
    (x,y) ∈ pi1_rel HA HB -> (x',y') ∈ pi1_rel HA HB.
Proof.
  intros.
  destruct x. destruct x'.
  apply pi1_rel_elem in H1.
  apply pi1_rel_elem.
  destruct H; eauto.
Qed.

Lemma pi2_rel_ordering A B (HA:effective_order A) (HB:effective_order B) :
  forall x x' y y', x ≤ x' -> y' ≤ y ->
    (x,y) ∈ pi2_rel HA HB -> (x',y') ∈ pi2_rel HA HB.
Proof.
  intros.
  destruct x. destruct x'.
  apply pi2_rel_elem in H1.
  apply pi2_rel_elem.
  destruct H; eauto.
Qed.

Lemma pair_rel_ordering A B C (HCeff:effective_order C)
  (R:erel C A) (S:erel C B)
  (HR:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R)
  (HS:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S) :
  forall x x' y y', x ≤ x' -> y' ≤ y ->
    (x,y) ∈ pair_rel HCeff R S -> (x',y') ∈ pair_rel HCeff R S.
Proof.
  repeat intro.
  destruct y.
  rewrite pair_rel_elem in H1.
  destruct y'.
  rewrite pair_rel_elem.
  destruct H0. destruct H1. split.
  apply HR with x c; auto.
  apply HS with x c0; auto.
Qed.

Lemma pi1_rel_dir hf A B (HA:effective_order A) (HB:effective_order B) :
  directed_rel hf (A×B) A (effective_prod HA HB) (pi1_rel HA HB).
Proof.
  repeat intro.
  destruct x as [a b].
  exists a. split.
  red; intros.
  apply H in H0.
  apply erel_image_elem in H0.
  apply pi1_rel_elem in H0. auto.
  apply erel_image_elem.
  apply pi1_rel_elem. auto.
Qed.  

Lemma pi2_rel_dir hf A B (HA:effective_order A) (HB:effective_order B) :
  directed_rel hf (A×B) B (effective_prod HA HB) (pi2_rel HA HB).
Proof.
  repeat intro.
  destruct x as [a b].
  exists b. split.
  red; intros.
  apply H in H0.
  apply erel_image_elem in H0.
  apply pi2_rel_elem in H0. auto.
  apply erel_image_elem.
  apply pi2_rel_elem. auto.
Qed.  

Lemma pair_rel_dir hf
 A B C (HCeff:effective_order C)
  (R:erel C A) (S:erel C B)
  (HR:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R)
  (HS:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S) :
  directed_rel hf C A HCeff R -> directed_rel hf C B HCeff S -> 
  directed_rel hf C (A×B) HCeff (pair_rel HCeff R S).
Proof.
  repeat intro.
  destruct (H x (image π₁ M)).
  apply inh_image; auto.
  red; intros.
  apply image_axiom2 in H2.
  destruct H2 as [y [??]].
  apply erel_image_elem.
  apply H1 in H2.
  apply erel_image_elem in H2.
  destruct y.
  apply pair_rel_elem in H2.
  destruct H2.
  simpl in H3.
  apply HR with x c; auto.
  destruct (H0 x (image π₂ M)).
  apply inh_image; auto.
  red; intros.
  apply image_axiom2 in H3.
  destruct H3 as [y [??]].
  apply erel_image_elem.
  apply H1 in H3.
  apply erel_image_elem in H3.
  destruct y.
  apply pair_rel_elem in H3.
  destruct H3.
  simpl in H4.
  apply HS with x c0; auto.
  exists (x0,x1).
  split.
  red; intros.
  destruct x2.
  destruct H2. destruct H3.  split; simpl.
  apply H2.
  change c with (π₁#((c,c0):(A×B))).
  apply image_axiom1. auto.
  apply H3.
  change c0 with (π₂#((c,c0):(A×B))).
  apply image_axiom1. auto.
  destruct H2. destruct H3.
  apply erel_image_elem in H4.
  apply erel_image_elem in H5.
  apply erel_image_elem.
  apply pair_rel_elem. split; auto.
Qed.

Lemma pair_proj_commute1_le C A B
  (HA:effective_order A) (HB:effective_order B) (HC:effective_order C)
  (R:erel C A) (S:erel C B) 
  (HR:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R)
  (HS:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S) :
  compose_rel (effective_prod HA HB) (pi1_rel HA HB) (pair_rel HC R S) ≤ R.
Proof.
  red; simpl; intros.
  destruct a as [c a].
  apply compose_elem in H.
  destruct H as [[a' b] [??]].
  apply pair_rel_elem in H.
  apply pi1_rel_elem in H0.
  destruct H.
  apply HR with c a'; auto.
  apply pair_rel_ordering; auto.
Qed.

Lemma pair_proj_commute1 C A B
  (HA:effective_order A) (HB:effective_order B) (HC:effective_order C)
  (R:erel C A) (S:erel C B) 
  (HR:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R)
  (HS:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S)
  (HSdir:directed_rel false C B HC S) :
  compose_rel (effective_prod HA HB) (pi1_rel HA HB) (pair_rel HC R S) ≈ R.
Proof.
  split.
  apply pair_proj_commute1_le; auto.
  red; simpl; intros.
  destruct a as [c a].
  apply compose_elem; auto.
  apply pair_rel_ordering; auto.
  destruct (HSdir c nil). red; auto.
  red; intros. apply nil_elem in H0. elim H0.
  exists (a,x). split.
  apply pair_rel_elem. split; auto.
  destruct H0.
  apply erel_image_elem in H1. auto.
  apply pi1_rel_elem. auto.
Qed.

Lemma pair_proj_commute2_le C A B
  (HA:effective_order A) (HB:effective_order B) (HC:effective_order C)
  (R:erel C A) (S:erel C B) 
  (HR:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R)
  (HS:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S) :
  compose_rel (effective_prod HA HB) (pi2_rel HA HB) (pair_rel HC R S) ≤ S.
Proof.
  red; simpl; intros.
  destruct a as [c b].
  apply compose_elem in H.
  destruct H as [[a b'] [??]].
  apply pair_rel_elem in H.
  apply pi2_rel_elem in H0.
  destruct H.
  apply HS with c b'; auto.
  apply pair_rel_ordering; auto.
Qed.

Lemma pair_proj_commute2 C A B
  (HA:effective_order A) (HB:effective_order B) (HC:effective_order C)
  (R:erel C A) (S:erel C B) 
  (HR:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R)
  (HS:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S)
  (HRdir:directed_rel false C A HC R) :
  compose_rel (effective_prod HA HB) (pi2_rel HA HB) (pair_rel HC R S) ≈ S.
Proof.
  split.
  apply pair_proj_commute2_le; auto.
  red; simpl; intros.
  apply compose_elem.
  apply pair_rel_ordering; auto.
  destruct a as [c b].
  destruct (HRdir c nil). red; auto.
  red; intros. apply nil_elem in H0. elim H0.
  destruct H0.
  exists (x,b).
  split. apply pair_rel_elem. split; auto.
  apply erel_image_elem in H1. auto.
  apply pi2_rel_elem. auto.
Qed.

Lemma pair_rel_universal_le C A B
  (HA:effective_order A) (HB:effective_order B) (HC:effective_order C)
  (R:erel C A) (S:erel C B) 
  (HR:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R)
  (HS:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S)
  (PAIR:erel C (A×B))
  (HPAIR :
   forall (x x' : C) (y y' : A × B),
     x ≤ x' -> y' ≤ y -> (x, y) ∈ PAIR -> (x', y') ∈ PAIR)
  (HCOMM1 : compose_rel (effective_prod HA HB) (pi1_rel HA HB) PAIR ≤ R)
  (HCOMM2 : compose_rel (effective_prod HA HB) (pi2_rel HA HB) PAIR ≤ S) :
  PAIR ≤ pair_rel HC R S.
Proof.
  red; simpl; intros.
  destruct a as [c [a b]].
  apply pair_rel_elem.
  split.
  rewrite <- HCOMM1.
  apply compose_elem; auto.
  exists (a,b). split; auto.
  apply pi1_rel_elem. auto.
  rewrite <- HCOMM2.
  apply compose_elem; auto.
  exists (a,b). split; auto.
  apply pi2_rel_elem. auto.
Qed.

Lemma pair_rel_universal hf C A B
  (HA:effective_order A) (HB:effective_order B) (HC:effective_order C)
  (R:erel C A) (S:erel C B) 
  (HR:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R)
  (HS:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S)
  (PAIR:erel C (A×B))
  (HPAIR :
   forall (x x' : C) (y y' : A × B),
     x ≤ x' -> y' ≤ y -> (x, y) ∈ PAIR -> (x', y') ∈ PAIR)
  (HPAIRdir : directed_rel hf C (A×B) HC PAIR)
  (HCOMM1 : compose_rel (effective_prod HA HB) (pi1_rel HA HB) PAIR ≈ R)
  (HCOMM2 : compose_rel (effective_prod HA HB) (pi2_rel HA HB) PAIR ≈ S) :
  PAIR ≈ pair_rel HC R S.
Proof.
  split.
  apply pair_rel_universal_le with HA HB; auto.
  red; simpl; intros.
  destruct a as [c [a b]].
  apply pair_rel_elem in H.    
  destruct H.
  rewrite <- HCOMM1 in H.
  rewrite <- HCOMM2 in H0.
  apply compose_elem in H; auto.
  apply compose_elem in H0; auto.
  destruct H as [[x y] [??]].
  destruct H0 as [[x' y'] [??]].
  apply pi1_rel_elem in H1.
  apply pi2_rel_elem in H2.
  destruct (HPAIRdir c ((x,y)::(x',y')::nil)%list).  
  destruct hf; simpl; auto.
  exists (x,y). apply cons_elem; auto.

  red; intros.
  apply erel_image_elem.
  apply cons_elem in H3. destruct H3.
  apply member_eq with (c,(x,y)); auto.
  destruct H3. split; split; auto.
  apply cons_elem in H3. destruct H3.
  apply member_eq with (c,(x',y')); auto.
  destruct H3. split; split; auto.
  apply nil_elem in H3. elim H3.
  destruct H3.
  apply erel_image_elem in H4.
  apply HPAIR with c x0; auto.
  assert ((x,y) ≤ x0).
  apply H3. apply cons_elem; auto.
  assert ((x',y') ≤ x0).
  apply H3. apply cons_elem. right. apply cons_elem; auto.
  split; simpl.
  transitivity x; auto. destruct H5; auto.
  transitivity y'; auto. destruct H6; auto.
Qed.

(*

Definition associator {A B C:preord} 
  (HA:effective_order A) (HB:effective_order B) (HC:effective_order C)
  : erel ((A×B)×C) (A×(B×C)).

Definition associator_inv {A B C:preord} 
  (HA:effective_order A) (HB:effective_order B) (HC:effective_order C)
  : erel (A×(B×C)) ((A×B)×C).

Definition unitor1 {A:preord} (HA:effective_order A) : erel (unitpo×A) A :=
  esubset_dec
    ((unitpo×A)×A) (fun x => snd (fst x) ≥ snd x)
    (fun x => eff_ord_dec A HA (snd x) (snd (fst x)))
  (eprod (eprod (eff_enum unitpo effective_unit) (eff_enum A HA)) (eff_enum A HA)).
  
Definition unitor1_inv {A:preord} (HA:effective_order A) : erel A (unitpo×A) :=
  esubset_dec
    (A×(unitpo×A)) (fun x => snd (snd x) ≥ fst x)
    (fun x => eff_ord_dec A HA (fst x) (snd (snd x)))
  (eprod (eff_enum A HA) (eprod (eff_enum unitpo effective_unit) (eff_enum A HA))).

Definition unitor2 {A:preord} (HA:effective_order A) : erel (A×unitpo) A :=
  esubset_dec
    ((A×unitpo)×A) (fun x => fst (fst x) ≥ snd x)
    (fun x => eff_ord_dec A HA (snd x) (fst (fst x)))
  (eprod (eprod (eff_enum A HA) (eff_enum unitpo effective_unit)) (eff_enum A HA)).
  
Definition unitor2_inv {A:preord} (HA:effective_order A) : erel (unitpo×A) A :=
  esubset_dec
    ((unitpo×A)×A) (fun x => snd (fst x) ≥ snd x)
    (fun x => eff_ord_dec A HA (snd x) (snd (fst x)))
  (eprod (eprod (eff_enum unitpo effective_unit) (eff_enum A HA)) (eff_enum A HA)).
*)

Definition pair_rel' {A B C D:preord}
  (R:erel A B) (S:erel C D) : erel (A×C) (B×D) :=
  image (mk_pair 
          (mk_pair (π₁ ∘ π₁) (π₁ ∘ π₂))           
          (mk_pair (π₂ ∘ π₁) (π₂ ∘ π₂)))
    (eprod R S).

Lemma pair_rel_elem' A B C D (R:erel A B) (S:erel C D)
  (HR:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R)
  (HS:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S) :
  forall a b c d, ((a,b),(c,d)) ∈ pair_rel' R S <->
    ((a,c) ∈ R /\ (b,d) ∈ S).
Proof.
  intros; split; intros.
  unfold pair_rel' in H.
  apply image_axiom2 in H.
  destruct H as [[[x y][z w]] [??]].
  simpl in H0.

  apply eprod_elem in H.
  destruct H.
  destruct H0 as [[[??][??]][[??][??]]]. simpl in *.
  split.
  apply HR with x y; auto.
  apply HS with z w; auto.

  unfold pair_rel'.
  apply image_axiom1'.
  exists ((a,c),(b,d)). split; simpl; auto.
  apply eprod_elem. auto.
Qed.    

Lemma pair_rel_order' A B C D (R:erel A B) (S:erel C D)
  (HR:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R)
  (HS:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S) :
   forall x x' y y',
   x ≤ x' ->
   y' ≤ y ->
   (x, y) ∈ pair_rel' R S ->
   (x', y') ∈ pair_rel' R S.
Proof.
  intros.
  destruct x; destruct y.
  apply (pair_rel_elem' _ _ _ _ R S) in H1.
  destruct x'; destruct y'.
  apply (pair_rel_elem' _ _ _ _ R S).
  auto. auto.
  destruct H1. split.
  apply HR with c c1; auto.
  destruct H; auto. destruct H0; auto.
  apply HS with c0 c2; auto.
  destruct H; auto. destruct H0; auto.
  auto. auto.
Qed.    


Lemma pair_rel_eq
 A B C D (R:erel A B) (S:erel C D)
  (HA:effective_order A) (HC:effective_order C)
  (HR:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R)
  (HS:forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ S -> (x',y') ∈ S) :
  pair_rel' R S ≈
  pair_rel (effective_prod HA HC) 
    (compose_rel HA R (pi1_rel HA HC)) (compose_rel HC S (pi2_rel HA HC)).
Proof.
  split; repeat intro.
  destruct a as [[a c][b d]].
  apply pair_rel_elem' in H; auto.
  destruct H.
  apply pair_rel_elem. split.
  apply compose_elem; auto.
  apply pi1_rel_ordering.
  exists a. split; auto.
  apply pi1_rel_elem. auto.
  apply compose_elem; auto.
  apply pi2_rel_ordering.
  exists c. split; auto.
  apply pi2_rel_elem. auto.

  destruct a as [[a c][b d]].
  apply pair_rel_elem in H; auto.
  destruct H.
  apply compose_elem in H; auto.
  apply compose_elem in H0; auto.
  destruct H as [y [??]].
  destruct H0 as [y' [??]].
  apply pair_rel_elem'; auto.
  apply pi1_rel_elem in H.
  apply pi2_rel_elem in H0.
  split.
  apply HR with y b; auto.
  apply HS with y' d; auto.
  apply pi2_rel_ordering.
  apply pi1_rel_ordering.
Qed.

(*
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
*)

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
  Variable hf:bool.
  Variables A B C:preord.
  Variable HAeff:effective_order A.
  Variable HBeff:effective_order B.
  Variable HCeff:effective_order C.
  Variable HAplt:plotkin_order hf A.

  Variable R:erel (C×A) B.
  Hypothesis HR :
    forall x x' y y', x ≤ x' -> y' ≤ y -> (x,y) ∈ R -> (x',y') ∈ R.

  Definition curry_acceptable (tuple:C×(joinable_rel_order hf A B)) :=
    match tuple with
    | (c,R') => forall ab, ab ∈ proj1_sig R' -> ((c,fst ab),snd ab) ∈ R
    end.

  Let Reff : effective_order ((C×A)×B) :=
    effective_prod (effective_prod HCeff HAeff) HBeff.


  Definition inset_decset (A:preord) (HA:effective_order A) (X:eset A) (x:A) 
    : eset unitpo :=
    image (const tt) (esubset_dec _ _
      (PREORD_EQ_DEC _ (OrdDec _ (eff_ord_dec _ HA)) x) X).

  Lemma curry_acceptable_semidec : 
    forall x, semidec (curry_acceptable x).
  Proof.
    intro x. destruct x as [c R']. unfold curry_acceptable.
    apply all_finset_semidec.
    intros. eapply member_eq. 2: apply H0.
    destruct H. destruct H. destruct H1.
    split; split; auto. split; auto. split; auto.
    intros. apply semidec_in.
    constructor.
    apply (eff_ord_dec _ Reff).
  Qed.

  Definition curry_rel : erel C (joinable_rel_order hf A B) :=
    esubset _ curry_acceptable_semidec 
      (eprod (eff_enum C HCeff)
             (eff_enum _ (joinable_rel_effective hf A B HAeff HBeff HAplt))).

  Lemma curry_rel_elem : forall c (R':joinable_relation hf A B),
    (c,R') ∈ curry_rel <-> (forall a b, (a,b) ∈ proj1_sig R' -> ((c,a),b) ∈ R).
  Proof.
    intros. split; intros.
    unfold curry_rel in H.
    apply esubset_elem in H. destruct H.
    red in H1.
    apply H1 in H0. auto.
    unfold curry_acceptable.
    intros. destruct a0. destruct b0.
    intros. 
    destruct H1 as [[??][??]]. simpl in *.
    destruct ab; simpl in *.
    destruct (H6 c4 c5) as [p [q [?[??]]]]; auto.
    apply H2 in H7. simpl in H7.
    revert H7. apply HR; auto.
    split; auto.

    unfold curry_rel.
    apply esubset_elem.
    unfold curry_acceptable.
    intros. destruct a. destruct b.
    intros. 
    destruct H0 as [[??][??]]. simpl in *.
    destruct ab; simpl in *.
    destruct (H5 c4 c5) as [p [q [?[??]]]]; auto.
    apply H1 in H6. simpl in H6.
    revert H6. apply HR; auto.
    split; auto.

    split; auto.
    apply eprod_elem.
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

  Hypothesis HRdir : directed_rel hf (C×A) B (effective_prod HCeff HAeff) R.
  Variable HBplt:plotkin_order hf B.

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
    directed_rel hf C (joinable_rel_order hf A B) HCeff curry_rel.
  Proof.
    intros c X ? ?.
    destruct (directed_joinables hf A B HAeff HAplt HBeff HBplt (R' c)) with X
      as [Q [??]]; auto.
    intros.
    apply R'_R in H2. apply R'_R.
    apply HR with (c,x) y; auto.
    split; auto.
    intros a M Minh HM.
    destruct (HRdir (c,a) M); auto.
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

  Lemma curry_universal
    (CURRY:erel C (joinable_rel_order hf A B))
    (HC : forall x x' y y',
      x ≤ x' -> y' ≤ y ->
      (x,y) ∈ CURRY -> (x',y') ∈ CURRY)
    (HCdir : directed_rel hf C (joinable_rel_order hf A B) HCeff CURRY) :
    (compose_rel (effective_prod (joinable_rel_effective hf A B HAeff HBeff HAplt) HAeff)
           (apply_rel hf A B HAeff HBeff HAplt)
           (pair_rel' CURRY (ident_rel HAeff)))
    ≈ R ->
    CURRY ≈ curry_rel.
  Proof.
    intros; split; red; simpl; intros.
    destruct a as [c S].
    apply curry_rel_elem. intros.
    rewrite <- H.
    apply compose_elem.
    apply pair_rel_order'; auto.
    apply ident_ordering.

    exists (S,a).
    split.
    apply pair_rel_elem'. auto.
    apply ident_ordering.
    split; auto.
    apply ident_elem. auto.
    apply apply_rel_elem.
    exists a. exists b. auto.

    destruct a as [c S].
    rewrite curry_rel_elem in H0.
    assert (exists M:finset (joinable_rel_order hf A B),
      (forall a b, (a,b) ∈ proj1_sig S -> exists T, (c,T) ∈ CURRY /\ T ∈ M /\ mkrel hf _ _ T (a,b))
      /\ 
      (forall T, T ∈ M -> (c,T) ∈ CURRY)).
    destruct S as [S HS]. simpl in *. clear HS.
    induction S.
    exists nil.
    split.
    intros. apply nil_elem in H1. elim H1.
    intros. apply nil_elem in H1. elim H1.

    destruct IHS as [M ?].
    intros. apply H0; auto.
    apply cons_elem; auto.
    destruct a as [a b].
    assert ((c,a,b) ∈ R).
    apply H0. apply cons_elem; auto.
    rewrite <- H in H2.
    apply compose_elem in H2.
    destruct H2 as [[T a'] [??]].
    apply pair_rel_elem' in H2.
    destruct H2.
    exists (T::M)%list.
    split.
    intros.
    apply cons_elem in H5. destruct H5.
    exists T. split. auto. split.
    apply cons_elem. auto.
    apply apply_rel_elem in H3.
    destruct H3 as [m [n [?[??]]]].
    red. simpl.
    exists m. exists n. split; auto.
    split.
    transitivity a'; auto.
    transitivity a.
    apply ident_elem in H4. auto.
    destruct H5 as [[??][??]]; auto. 
    transitivity b; auto.
    destruct H5 as [[??][??]]; auto. 
    destruct H1.
    destruct (H1 a0 b0) as [T' [??]]; auto.
    exists T'. split; auto.
    destruct H8. split; auto.
    apply cons_elem; auto.

    intros. apply cons_elem in H5.
    destruct H5.
    apply member_eq with (c,T); auto.
    destruct H5; split; split; auto.
    destruct H1. apply H6; auto.

    auto.
    apply ident_ordering.
    apply pair_rel_order'; auto.
    apply ident_ordering.

    destruct H1 as [M ?].
    destruct (HCdir c M).
    destruct hf; auto.
    destruct S. destruct i.
    destruct i as [[a b] ?].
    destruct H1.
    destruct (H1 a b) as [T [??]]. simpl; auto.
    destruct H4. exists T; auto.
    red; auto.

    red; intros.
    apply erel_image_elem.
    destruct H1. apply H3; auto.
    destruct H2.
    apply erel_image_elem in H3.
    apply HC with c x; auto.
    red; simpl; intros.
    red; simpl; intros.
    destruct H1.
    destruct (H1 a b) as [T [?[??]]]; auto.
    assert (T ≤ x).
    apply H2. auto.
    destruct H8 as [a' [b' [?[??]]]].
    simpl in H10, H11.
    destruct (H9 a' b') as [a'' [b'' [?[??]]]]; auto.
    exists a''. exists b''. split; auto.
    split.
    transitivity a'; auto.
    transitivity b'; auto.
  Qed.
    
  Lemma curry_apply :
    (compose_rel (effective_prod (joinable_rel_effective hf A B HAeff HBeff HAplt) HAeff)
           (apply_rel hf A B HAeff HBeff HAplt)
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
    apply eprod_elem in H. destruct H.
    rewrite H0.
    simpl.
    unfold pair_rel' in H.
    apply image_axiom2 in H.
    destruct H as [q' [??]].
    simpl in H3.
    destruct q' as [q1' q2']. simpl in H3.
    apply eprod_elem in H. destruct H.
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
    assert (exists R':joinable_relation hf A B,
      (a,b) ∈ proj1_sig R' /\
      (forall x y, (x,y) ∈ proj1_sig R' -> ((c,x),y) ∈ R)).

      destruct (swell hf A B HAeff HAplt HBeff HBplt (R' c)) with ((a,b)::nil)%list
        as [G [?[??]]].
      intros. apply R'_R in H2. apply R'_R.
      apply HR with (c,x) y; auto.
      split; auto.
      intros z M ? ?. 
      destruct (HRdir (c,z) M); auto.
      red; intros. apply H0 in H1.
      apply erel_image_elem in H1. apply R'_R in H1.
      apply erel_image_elem. auto.
      destruct H1.
      exists x; split; auto.
      apply erel_image_elem in H2.
      apply erel_image_elem. apply R'_R. auto.
      destruct hf; simpl; auto.
      exists (a,b). apply cons_elem; auto.
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
        : (((C×A) × (joinable_rel_order hf A B × A)) ×
            ((joinable_rel_order hf A B × A) × B))
        )).
    apply image_axiom1.
    apply esubset_dec_elem.
    clear. intros.
    destruct H as [[[??][??]][[??][??]]]; eauto.
    split; simpl; auto.
    apply eprod_elem. split.
    unfold pair_rel'.
    change (c,a,(S,a)) with
      ((mk_pair (mk_pair (π₁ ∘ π₁) (π₁ ∘ π₂)) (mk_pair (π₂ ∘ π₁) (π₂ ∘ π₂)))
      ( ((c,S),(a,a))
      :  (C × joinable_rel_order hf A B) × (A×A)
      )).
    apply image_axiom1.
    apply eprod_elem. split.
    rewrite curry_rel_elem.
    intros.
    destruct H0; auto.
    unfold ident_rel.
    apply esubset_dec_elem.
    clear. intros. destruct H as [[??][??]]; eauto.
    split; simpl; auto.
    apply eprod_elem. split; apply eff_complete.
    apply apply_rel_elem.
    exists a. exists b. intuition.
  Qed.
End curry.
