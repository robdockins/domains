(* Copyright (c) 2014, Robert Dockins *)

Require Import Setoid.
Require Import List.
Require Import NArith.


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
Require Import cpo.
Require Import profinite.

(**  * Flat pointed domains

     Every enumerable type can be turned into a flat profinite domain.
     These are useful for representing base types.
  *)

Module enumtype.
  Record enumtype :=
  Enumtype
  { carrier :> Type
  ; enumtype_set : N -> option carrier 
  ; enumtype_complete : forall x, exists n, enumtype_set n = Some x
  ; enumtype_dec : forall x y:carrier, {x=y}+{x<>y}
  }.

  Definition eq_mixin (X:enumtype) : Eq.mixin_of (carrier X) :=
    Eq.Mixin (carrier X) (@eq _) 
    (@Logic.refl_equal _) (@Logic.eq_sym _) (@Logic.eq_trans _).

  Definition preord_mixin (X:enumtype) : Preord.mixin_of (carrier X) :=
    Preord.Mixin (carrier X) (@eq _) (@Logic.refl_equal _) (@Logic.eq_trans _).

  Canonical Structure setoid (X:enumtype) : Eq.type :=
    Eq.Pack X (eq_mixin X).
  Canonical Structure ord (X:enumtype) : preord :=
    Preord.Pack X (preord_mixin X).

  Lemma order_discrete (X:enumtype) (x y:X) : x ≤ y -> x = y.
  Proof (fun H => H).
 
  Lemma strong_eq (X:enumtype) (x y:X) : x ≈ y -> x = y.
  Proof (fun H => H).

  Program Definition enumtype_effective X : effective_order (ord X) :=
    EffectiveOrder (ord X) (enumtype_dec X) (enumtype_set X) _.
  Next Obligation.
    intros. 
    destruct (enumtype_complete X x) as [n ?]. exists n.
    rewrite H. auto.
  Qed.

  Lemma enumtype_has_normals (X:enumtype) :
    has_normals (ord X) (enumtype_effective X) true.
  Proof.
    repeat intro. exists X0.
    split. hnf; auto.
    split; auto.
    repeat intro. exists z.
    split. red; simpl; intros.
    apply H in H0.
    apply finsubset_elem in H0. destruct H0; auto.
    intros. hnf in H1. destruct H1. eauto.
    apply finsubset_elem.
    intros. hnf in H1. subst x. destruct H0; auto.
    hnf in Hinh0.
    destruct Hinh0.
    apply H in H0.
    apply finsubset_elem in H0.
    destruct H0. hnf in H1. subst x.
    split; auto.
    intros. hnf in H2. subst z. destruct H1; auto.
  Qed.

  Definition enumtype_plotkin (X:enumtype) : plotkin_order true (ord X) :=
    norm_plt (ord X) (enumtype_effective X) true (@enumtype_has_normals X).
End enumtype.

Notation enumtype := enumtype.enumtype.
Notation Enumtype := enumtype.Enumtype.

Canonical Structure enumtype.setoid.
Canonical Structure enumtype.ord.
Coercion enumtype.carrier : enumtype >-> Sortclass.

Canonical Structure flat (X:enumtype) : ∂PLT :=
    PLT.Ob true (enumtype.carrier X)
      (PLT.Class _ _
        (enumtype.preord_mixin X)
        (enumtype.enumtype_effective X)
        (enumtype.enumtype_plotkin X)).

Program Definition flat_elem (Y:enumtype) (y:Y) : PLT.unit true → flat Y :=
  PLT.Hom true (PLT.unit true) (flat Y) (single (tt,y)) _ _.
Next Obligation.
  intros. destruct x'. destruct x.
  apply single_axiom in H1.
  apply single_axiom.
  destruct H1. destruct H1. simpl in *.
  split; split; simpl; auto.
  rewrite H0; auto.
  hnf in H0. subst y'. hnf in H3. hnf. auto.
Qed.
Next Obligation.
  repeat intro. exists y.
  split. repeat intro.
  apply H in H0. apply erel_image_elem in H0.
  apply single_axiom in H0.
  destruct H0 as [[??][??]]; auto.
  apply erel_image_elem.
  apply single_axiom. destruct x. auto.
Qed.

Lemma flat_elem_inj Y : forall y1 y2,
  flat_elem Y y1 ≈ flat_elem Y y2 -> y1 = y2.
Proof.
  intros. destruct H.
  assert ((tt,y1) ∈ PLT.hom_rel (flat_elem Y y2)).
  apply H. apply single_axiom. auto.
  simpl in H1. apply single_axiom in H1.
  destruct H1 as [[??][??]]; auto.
Qed.

Arguments flat_elem [Y] y.

Section flat_cases.
  Variable X:enumtype.
  Variables (A B:∂PLT).
  Variable f : X -> (A → B).

  Program Definition insert_index (x:X) : Preord.hom (A×B)%cat_ob ((A×flat X)×B)%cat_ob :=
    Preord.Hom (A×B)%cat_ob ((A×flat X)×B)%cat_ob (fun ab => ((fst ab, x), snd ab)) _.
  Next Obligation.
    intros x [??] [??] [??]; simpl in *; auto.
    split; simpl; auto. split; auto.
  Qed.

  Program Definition map_indexes : Preord.hom (flat X) (eset ((PLT.ord A×flat X)×PLT.ord B)%cat_ob) :=
    Preord.Hom (flat X) (eset ((A× flat X)×B)%cat_ob)
      (fun x => image (insert_index x) (PLT.hom_rel (f x))) _.
  Next Obligation.
    intros. hnf in H. subst a. auto.
  Qed.

  Definition flat_cases_rel : erel (PLT.ord A×flat X)%cat_ob (PLT.ord B) :=
    union (image map_indexes (enumtype.enumtype_set X : eset (flat X))).

  Lemma flat_cases_rel_elem : forall x a b,
    ((a,b) ∈ PLT.hom_rel (f x) <-> (a,x,b) ∈ flat_cases_rel).
  Proof.
    intros. unfold flat_cases_rel.
    rewrite union_axiom.
    intuition.
    exists (map_indexes x).
    split. apply image_axiom1. 
    destruct (enumtype.enumtype_complete X x) as [n ?].
    exists n. rewrite H0. auto.
    unfold map_indexes. simpl.
    apply image_axiom1'.
    exists (a,b). split; auto.
    destruct H as [Q [??]].
    apply image_axiom2 in H. destruct H as [y [??]].
    rewrite H1 in H0.
    simpl in H0.
    apply image_axiom2 in H0.
    destruct H0 as [?[??]].
    simpl in H2.
    destruct H2 as [??].
    destruct H2 as [??]. simpl in *.
    destruct H2. simpl in *. hnf in H5. subst y.
    destruct x0. revert H0.
    apply PLT.hom_order.
    destruct H3 as [[??]?]; auto.
    destruct H3 as [[??]?]; auto.
  Qed.

  Program Definition flat_cases : A ⊗ flat X → B :=
    PLT.Hom true (PLT.prod A (flat X)) B flat_cases_rel _ _.
  Next Obligation.
    intros. 
    destruct x. destruct x'.
    rewrite <- (flat_cases_rel_elem) in H1.
    rewrite <- flat_cases_rel_elem.
    destruct H. simpl in *. hnf in H2. subst c2.
    revert H1. apply PLT.hom_order; auto.
  Qed.
  Next Obligation.
    repeat intro.
    destruct x as [a x].
    destruct (PLT.hom_directed _ _ _ (f x) a M); auto.
    red; simpl; intros. apply H in H0.
    apply erel_image_elem in H0.
    apply erel_image_elem.    
    apply (flat_cases_rel_elem x a a0). auto.
    destruct H0.    
    apply erel_image_elem in H1.
    exists x0. split; auto.
    apply erel_image_elem.    
    apply (flat_cases_rel_elem x a x0). auto.
  Qed.

  Lemma flat_cases_elem x h : flat_cases ∘ 《h, flat_elem x》 ≈ f x ∘ h.
  Proof.
    split; intros a H. destruct a.
    apply PLT.compose_hom_rel in H.
    apply PLT.compose_hom_rel.
    destruct H as [q [??]].
    destruct q.
    apply (flat_cases_rel_elem) in H0.
    simpl in H.
    rewrite (PLT.pair_hom_rel _ _ _ _ _ _ c c1 c2) in H. destruct H.
    exists c1. split; auto.
    simpl in H1.
    apply single_axiom in H1.
    destruct H1 as [[??][??]]. simpl in *.
    hnf in H2. subst c2. auto.
    destruct a.
    apply PLT.compose_hom_rel in H.
    apply PLT.compose_hom_rel.
    destruct H as [q [??]].
    exists (q,x). split.
    apply pair_rel_elem. split; auto.
    simpl. apply single_axiom.
    destruct c. auto.
    apply (flat_cases_rel_elem).
    auto.   
  Qed.
End flat_cases.
Arguments flat_cases [X A B] f.

Definition boolset : N -> option bool :=
  fun n => match n with N0 => Some true | _ => Some false end.

Program Definition enumbool : enumtype :=
  Enumtype bool boolset _ _.
Next Obligation.
  intros. destruct x.
  exists N0. simpl. auto.
  exists 1%N. simpl; auto.
Qed.
Next Obligation.
  decide equality.
Qed.

Canonical Structure enumbool.
