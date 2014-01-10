(* Copyright (c) 2014, Robert Dockins *)

Require Import List.
Require Import NArith.

Require Import basics.
Require Import categories.
Require Import preord.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import plotkin.
Require Import profinite.
Require Import embed.
Require Import joinable.
Require Import directed.
Require Import cont_functors.
Require Import bilimit.


Section prod_functor.
  Variable hf:bool.
  Variables A B C D:ob (EMBED hf).

  Variable f:A ⇀ B.
  Variable g:C ⇀ D.

  Program Definition prod_fmap : PLT.prod A C ⇀ PLT.prod B D
    := Embedding hf (PLT.prod A C) (PLT.prod B D) (fun x => (f (fst x), g (snd x)))
         _ _ _ _.
  Next Obligation.
    intros. destruct a as [a c]. destruct a' as [a' c']. simpl.
    destruct H. simpl in *.
    split; simpl; apply embed_mono; auto.
  Qed.
  Next Obligation.
    intros. destruct a as [a c]. destruct a' as [a' c']. simpl.
    destruct H. simpl in *.
    split; simpl.
    apply embed_reflects in H. auto.
    apply embed_reflects in H0. auto.
  Qed.
  Next Obligation.
    intros [b d]. simpl.
    destruct hf. auto.
    simpl.
    destruct (embed_directed0 f b).
    destruct (embed_directed0 g d).
    exists (x,x0). simpl. split; auto.
  Qed.
  Next Obligation.
    intros.
    destruct a as [a c].
    destruct b as [a' c']. simpl in *.
    destruct (embed_directed2 f (fst y) a a') as [p [?[??]]].
    destruct H; auto. destruct H0; auto.
    destruct (embed_directed2 g (snd y) c c') as [q [?[??]]].
    destruct H; auto. destruct H0; auto.
    exists (p,q). simpl. 
    repeat split; auto.
  Qed.

End prod_functor.

Program Definition prodF hf
  : functor (PROD (EMBED hf) (EMBED hf)) (EMBED hf) :=

  Functor (PROD (EMBED hf) (EMBED hf)) (EMBED hf) 
     (fun (AB:ob (PROD (EMBED hf) (EMBED hf))) =>
         PLT.prod (@obl (EMBED hf) (EMBED hf) AB)
                  (@obr (EMBED hf) (EMBED hf) AB))
     (fun (AB CD:ob (PROD (EMBED hf) (EMBED hf))) (f:AB → CD) => 
       prod_fmap hf _ _ _ _
         (@homl (EMBED hf) (EMBED hf) AB CD f)
         (@homr (EMBED hf) (EMBED hf) AB CD f))
     _ _ _.
Next Obligation.
  simpl; intros.
  destruct f; simpl in *.
  apply embed_lift'; simpl; intros.
  destruct x as [x y]. simpl.
  destruct H. simpl in *.
  destruct H; destruct H0; split; split; simpl; auto.
  apply H. apply H0. apply H1. apply H2.
Qed.
Next Obligation.
  simpl; intros.
  destruct f; simpl in *.
  destruct g; simpl in *.
  destruct h; simpl in *.
  destruct H; simpl in *.
  apply embed_lift'; simpl; intros.
  split; split; simpl.
  rewrite H. auto.
  rewrite H0; auto.
  rewrite H; auto.
  rewrite H0; auto.
Qed.
Next Obligation.
  simpl; intros.
  destruct f; simpl in *.
  destruct g; simpl in *.
  destruct H; simpl in *.
  apply embed_lift'; simpl; intros.
  split; split; simpl.
  rewrite H. auto.
  rewrite H0; auto.
  rewrite H; auto.
  rewrite H0; auto.
Qed.


Lemma prodF_continuous hf : continuous_functor (prodF hf).
Proof.
  hnf; intros.
  apply decompose_is_colimit.
  simpl. intros.
  destruct x as [x y].
  generalize (fstF_continuous _ _ I DS CC X). intros.
  generalize (sndF_continuous _ _ I DS CC X). intros.
  destruct (colimit_decompose hf I _ _ X0 x) as [i [x' ?]].
  destruct (colimit_decompose hf I _ _ X1 y) as [j [y' ?]].
  simpl in *.
  destruct (choose_ub I i j) as [k [??]].
  exists k.
  exists (homl (ds_hom DS i k H) x', homr (ds_hom DS j k H0) y').
  simpl.
  generalize (cocone_commute CC i k H).
  generalize (cocone_commute CC j k H0).
  intros. destruct H1. destruct H2.
  rewrite H2 in e.
  rewrite H3 in e0.
  simpl in *.
  destruct e; destruct e0; split; split; auto.
Qed.


Section sum_functor.
  Variable hf:bool.
  Variables A B C D:ob (EMBED hf).

  Variable f:A ⇀ B.
  Variable g:C ⇀ D.

  Definition sum_fmap_func (x:A+C) : B+D :=
    match x with
    | inl a => inl (f a)
    | inr b => inr (g b)
    end.

  Program Definition sum_fmap : PLT.sum A C ⇀ PLT.sum B D
    := Embedding hf (PLT.sum A C) (PLT.sum B D) sum_fmap_func _ _ _ _.
  Next Obligation.
    intros. destruct a as [a|c]. destruct a' as [a'|c']; simpl.
    apply embed_mono; auto.
    elim H.
    destruct a' as [a'|c']; simpl.
    elim H.
    apply embed_mono; auto.
  Qed.
  Next Obligation.
    intros.
    destruct a as [a|c]. 
    destruct a' as [a'|c']. simpl.
    simpl in H. red in H. simpl in H.
    apply embed_reflects in H. auto.
    elim H.
    destruct a' as [a'|c']. simpl.
    destruct H.
    red in H. simpl in H.
    apply embed_reflects in H. auto.
  Qed.
  Next Obligation.
    intro y. simpl in *. unfold sum_fmap_func.
    destruct hf. auto.
    destruct y as [b|d]. simpl.
    destruct (embed_directed0 f b).
    exists (inl x). auto.
    destruct (embed_directed0 g d).
    exists (inr x). auto.
  Qed.
  Next Obligation.
    intros.
    destruct y as [y|y].
    destruct a as [a|a]. 2: elim H.
    destruct b as [b|b]. 2: elim H0.
    unfold sum_fmap_func in *.
    destruct (embed_directed2 f y a b) as [p [?[??]]]; auto.
    exists (inl p). auto.
    destruct a as [a|a]. elim H.
    destruct b as [b|b]. elim H0.
    unfold sum_fmap_func in *.
    destruct (embed_directed2 g y a b) as [p [?[??]]]; auto.
    exists (inr p). auto.
  Qed.
End sum_functor.

Program Definition sumF hf
  : functor (PROD (EMBED hf) (EMBED hf)) (EMBED hf) :=

  Functor (PROD (EMBED hf) (EMBED hf)) (EMBED hf) 
     (fun (AB:ob (PROD (EMBED hf) (EMBED hf))) =>
         PLT.sum (@obl (EMBED hf) (EMBED hf) AB)
                 (@obr (EMBED hf) (EMBED hf) AB))
     (fun (AB CD:ob (PROD (EMBED hf) (EMBED hf))) (f:AB → CD) => 
       sum_fmap hf _ _ _ _
         (@homl (EMBED hf) (EMBED hf) AB CD f)
         (@homr (EMBED hf) (EMBED hf) AB CD f))
     _ _ _.
Next Obligation.
  simpl; intros.
  destruct f; simpl in *.
  apply embed_lift'; simpl; intros.
  destruct x as [x|x]. simpl.
  destruct H. simpl in *.
  destruct H; split. apply H. apply H1.
  simpl.
  destruct H. simpl in *.
  destruct H0. split. apply H0. apply H1.
Qed.
Next Obligation.
  simpl; intros.
  destruct f; simpl in *.
  destruct g; simpl in *.
  destruct h; simpl in *.
  destruct H; simpl in *.
  apply embed_lift'; simpl; intros.
  unfold sum_fmap_func.
  destruct x as [x|x].
  destruct H; split.
  apply H. apply H1.
  destruct H0; split.
  apply H0. apply H1.
Qed.
Next Obligation.
  simpl; intros.
  destruct f; simpl in *.
  destruct g; simpl in *.
  destruct H; simpl in *.
  apply embed_lift'; simpl; intros.
  unfold sum_fmap_func.
  destruct x as [x|x].
  destruct H; split.
  apply H. apply H1.
  destruct H0; split.
  apply H0. apply H1.
Qed.


Lemma sumF_continuous hf : continuous_functor (sumF hf).
Proof.
  hnf; intros.
  apply decompose_is_colimit.
  simpl. intros.
  destruct x as [x|x].
  generalize (fstF_continuous _ _ I DS CC X). intros.
  destruct (colimit_decompose hf I _ _ X0 x) as [i [x' ?]].
  exists i. exists (inl x').
  simpl. destruct e; auto.
  generalize (sndF_continuous _ _ I DS CC X). intros.
  destruct (colimit_decompose hf I _ _ X0 x) as [i [x' ?]].
  exists i. exists (inr x').
  simpl. destruct e; auto.
Qed.
