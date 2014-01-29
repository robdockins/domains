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
Require Import cpo.
Require Import profinite.

(**  * Discrete unpointed domains

     Every finite type can be turned into a discrete profinite domain.
     These are useful for representing base types.
  *)

Module fintype.
  Record fintype :=
  Fintype
  { carrier :> Type
  ; fintype_list : list carrier
  ; fintype_complete : forall x, In x fintype_list
  ; fintype_dec : forall x y:carrier, {x=y}+{x<>y}
  }.

  Definition eq_mixin (X:fintype) : Eq.mixin_of (carrier X) :=
    Eq.Mixin (carrier X) (@eq _) 
    (@Logic.refl_equal _) (@Logic.eq_sym _) (@Logic.eq_trans _).

  Definition preord_mixin (X:fintype) : Preord.mixin_of (carrier X) :=
    Preord.Mixin (carrier X) (@eq _) (@Logic.refl_equal _) (@Logic.eq_trans _).

  Canonical Structure setoid (X:fintype) : Eq.type :=
    Eq.Pack X (eq_mixin X).
  Canonical Structure ord (X:fintype) : preord :=
    Preord.Pack X (preord_mixin X).

  Lemma order_discrete (X:fintype) (x y:X) : x ≤ y -> x = y.
  Proof (fun H => H).
 
  Lemma strong_eq (X:fintype) (x y:X) : x ≈ y -> x = y.
  Proof (fun H => H).

  Program Definition fintype_effective X : effective_order (ord X) :=
    EffectiveOrder (ord X) (fintype_dec X) (elist (fintype_list X)) _.
  Next Obligation.
    intros. apply elist_elem. exists x. split; auto. apply fintype_complete.
  Qed.

  Program Definition fintype_has_normals hf (X:fintype) : 
    has_normals (ord X) (fintype_effective X) hf.
  Proof.  
    hnf; intros. exists (fintype_list X). split.
    hnf; intros. exists a; split; auto. apply fintype_complete.
    hnf; simpl; intros. split.
    destruct hf.
    destruct Hinh. exists x.
    exists x. split; auto. apply fintype_complete.
    hnf; auto.
    repeat intro. exists z.
    split; repeat intro.
    apply H in H0. apply finsubset_elem in H0.
    destruct H0; auto.
    intros. hnf in H1, H2. destruct H1.
    hnf. hnf in H3. rewrite H3; auto.
    apply finsubset_elem. intros.
    destruct H0. rewrite H2. auto.
    split; auto.
    exists z; split; auto. apply fintype_complete.
  Qed.

  Definition fintype_plotkin hf (X:fintype) : plotkin_order hf (ord X) :=
    norm_plt (ord X) (fintype_effective X) hf (@fintype_has_normals hf X).
End fintype.

Notation fintype := fintype.fintype.
Notation Fintype := fintype.Fintype.

Canonical Structure fintype.setoid.
Canonical Structure fintype.ord.
Coercion fintype.carrier : fintype >-> Sortclass.

Canonical Structure disc (X:fintype) : PLT :=
    PLT.Ob false (fintype.carrier X)
      (PLT.Class _ _
        (fintype.preord_mixin X)
        (fintype.fintype_effective X)
        (fintype.fintype_plotkin false X)).

Program Definition disc_elem (Y:fintype) (y:Y) : PLT.unit false → disc Y :=
  PLT.Hom false (PLT.unit false) (disc Y) (single (tt,y)) _ _.
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

Lemma disc_elem_inj Y : forall y1 y2,
  disc_elem Y y1 ≈ disc_elem Y y2 -> y1 = y2.
Proof.
  intros. destruct H.
  assert ((tt,y1) ∈ PLT.hom_rel (disc_elem Y y2)).
  apply H. apply single_axiom. auto.
  simpl in H1. apply single_axiom in H1.
  destruct H1 as [[??][??]]; auto.
Qed.

Arguments disc_elem [Y] y.

Section disc_cases.
  Variable X:fintype.
  Variables (A B:PLT).
  Variable f : X -> (A → B).

  Program Definition insert_index (x:X) : Preord.hom (A×B) ((A×disc X)×B) :=
    Preord.Hom (A×B) ((A×disc X)×B) (fun ab => ((fst ab, x), snd ab)) _.
  Next Obligation.
    intros x [??] [??] [??]; simpl in *; auto.
    split; simpl; auto. split; auto.
  Qed.

  Fixpoint mk_disc_cases_rel (ls:list X) : eset ((PLT.ord A×disc X)×B) :=
    match ls with
    | nil => ∅
    | x::xs => union2 (image (insert_index x) (PLT.hom_rel (f x)))
                      (mk_disc_cases_rel xs)
    end.

  Lemma mk_disc_cases_elem : forall ls x a b, (In x ls) ->
    ((a,b) ∈ PLT.hom_rel (f x) <-> (a,x,b) ∈ mk_disc_cases_rel ls).
  Proof.
    induction ls; simpl; intros. elim H.
    destruct H. subst a.
    split; intros.
    apply union2_elem. left.
    apply image_axiom1'.
    exists (a0,b); split; auto.
    apply union2_elem in H.
    destruct H. apply image_axiom2 in H.
    destruct H as [[p q] [??]].
    simpl in H0.
    revert H. apply member_eq.
    destruct H0 as [[??][??]]. simpl in *.
    destruct H; destruct H1; simpl in *.
    split; split; auto.
    destruct (In_dec (fintype.fintype_dec X) x ls).
    apply IHls; auto.
    elim n. clear IHls. clear n.
    induction ls; simpl in *.
    apply empty_elem in H. auto.
    apply union2_elem in H. destruct H.
    apply image_axiom2 in H.
    destruct H as [[p q] [??]].
    simpl in H0.
    destruct H0 as [[??][??]]. simpl in *.
    destruct H0. simpl in *. hnf in H4. auto.
    right; auto.
    split; intros.
    apply union2_elem. right. apply IHls; auto.
    apply union2_elem in H0. destruct H0.
    apply image_axiom2 in H0.
    destruct H0 as [[p q] [??]]. simpl in H1.
    destruct H1 as [[??][??]]. simpl in *.
    destruct H1. simpl in *. destruct H3. simpl in *.
    hnf in H5. subst a.
    revert H0. apply member_eq.
    split; split; auto.
    apply IHls; auto.
  Qed.

  Program Definition disc_cases : PLT.prod A (disc X) → B :=
    PLT.Hom false (PLT.prod A (disc X)) B
       (mk_disc_cases_rel (fintype.fintype_list X)) _ _.
  Next Obligation.
    generalize (fintype.fintype_list X).
    induction l; simpl; intros.
    apply empty_elem in H1. elim H1.
    apply union2_elem in H1. apply union2_elem.
    destruct H1. left.
    apply image_axiom2 in H1. apply image_axiom1'.
    destruct H1 as [[p q] ?]. destruct H1.
    simpl in H2.
    destruct x; destruct x'. simpl.
    destruct H. simpl in *. hnf in H3. subst c0.
    exists (c1,y'). simpl. split.
    destruct H2 as [[??][??]]. simpl in *.
    destruct H2; destruct H4; simpl in *.
    hnf in H6. subst c2. auto.
    destruct H2 as [[??][??]]. simpl in *.
    destruct H2; destruct H4; simpl in *.
    revert H1. apply PLT.hom_order.
    rewrite H4. auto.
    rewrite H0; auto.   
    right. eapply IHl; eauto.
  Qed.
  Next Obligation.
    repeat intro.
    destruct x as [a x].
    destruct (PLT.hom_directed _ _ _ (f x) a M); auto.
    red; simpl; intros. apply H in H0.
    apply erel_image_elem in H0.
    apply erel_image_elem.    
    apply (mk_disc_cases_elem (fintype.fintype_list X) x a a0).
    apply fintype.fintype_complete. auto.
    destruct H0.    
    apply erel_image_elem in H1.
    exists x0. split; auto.
    apply erel_image_elem.    
    apply (mk_disc_cases_elem (fintype.fintype_list X) x a x0).
    apply fintype.fintype_complete. auto.
  Qed.

  Lemma disc_cases_elem x h : disc_cases ∘ PLT.pair h (disc_elem x) ≈ f x ∘ h.
  Proof.
    split; intros a H. destruct a.
    apply compose_hom_rel in H.
    apply compose_hom_rel.
    destruct H as [q [??]].
    destruct q.
    apply (mk_disc_cases_elem (fintype.fintype_list X)) in H0.
    simpl in H.
    rewrite (pair_rel_elem _ _ _ _ _ _ c c1 c2) in H. destruct H.
    exists c1. split; auto.
    apply single_axiom in H1.
    destruct H1 as [[??][??]]. simpl in *.
    hnf in H2. subst c2. auto.
    apply fintype.fintype_complete.
    destruct a.
    apply compose_hom_rel in H.
    apply compose_hom_rel.
    destruct H as [q [??]].
    exists (q,x). split.
    apply pair_rel_elem. split; auto.
    simpl. apply single_axiom.
    destruct c. auto.
    apply (mk_disc_cases_elem (fintype.fintype_list X)).
    apply fintype.fintype_complete.
    auto.   
  Qed.

End disc_cases.
Arguments disc_cases [X A B] f.

Program Definition finbool : fintype :=
  Fintype bool (true::false::nil) _ _.
Next Obligation.
  intros. destruct x; simpl; auto.
Qed.
Next Obligation.
  decide equality.
Qed.

Canonical Structure finbool.

