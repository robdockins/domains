(* Copyright (c) 2014, Robert Dockins *)

Require Import String.
Require Import List.

Require Import atoms.
Require Import permutations.

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
Require Import discrete.

Inductive ty :=
  | ty_bool
  | ty_arrow : ty -> ty -> ty.

Delimit Scope ty_scope with ty.

Notation "x ⇒ y" := (ty_arrow x y) : ty_scope.
Local Open Scope ty.

Inductive term : ty -> Type :=
  | tbool : forall b:bool,
                term ty_bool
  | tapp : forall σ₁ σ₂,
                term (σ₁ ⇒ σ₂) ->
                term σ₁ ->
                term σ₂
  | tI : forall σ,
                term (σ ⇒ σ)

  | tK : forall σ₁ σ₂,
                term (σ₁ ⇒ σ₂ ⇒ σ₁)

  | tS : forall σ₁ σ₂ σ₃,
                term ((σ₁ ⇒ σ₂ ⇒ σ₃) ⇒ (σ₁ ⇒ σ₂) ⇒ σ₁ ⇒ σ₃)

  | tIF : forall σ,
                term (ty_bool ⇒ σ ⇒ σ ⇒ σ).

Inductive redex : forall σ₁ σ₂, term (σ₁ ⇒ σ₂) -> term σ₁ -> term σ₂ -> Prop :=
  | redex_I : forall σ x,
                  redex _ _ (tI σ) x x
  | redex_K : forall σ₁ σ₂ x y,
                  redex σ₂ σ₁ (tapp σ₁ (σ₂ ⇒ σ₁) (tK σ₁ σ₂) y) x y
  | redex_S : forall σ₁ σ₂ σ₃ f g x,
                  redex _ _ (tapp _ _ (tapp _ _ (tS σ₁ σ₂ σ₃) f) g)
                            x
                            (tapp _ _ (tapp _ _ f x) (tapp _ _ g x))
  | redex_IFtrue : forall σ th el,
                  redex _ _ (tapp _ _ (tapp _ _ (tIF σ) (tbool true)) th) el th
  | redex_IFfalse : forall σ th el,
                  redex _ _ (tapp _ _ (tapp _ _ (tIF σ) (tbool false)) th) el el.

Inductive eval : forall τ, term τ -> term τ -> Prop :=
  | ebool : forall b, eval ty_bool (tbool b) (tbool b)
  | eI   : forall σ, eval _ (tI σ) (tI _)
  | eK   : forall σ₁ σ₂, eval _ (tK σ₁ σ₂) (tK _ _)
  | eS   : forall σ₁ σ₂ σ₃, eval _ (tS σ₁ σ₂ σ₃) (tS _ _ _)
  | eIF  : forall σ , eval _ (tIF σ) (tIF σ)
  | eapp1 : forall σ₁ σ₂ m₁ m₂ n₁ n₂ r z,
             eval (σ₁ ⇒ σ₂) m₁ n₁ ->
             eval σ₁ m₂ n₂ ->
             redex σ₁ σ₂ n₁ n₂ r ->
             eval σ₂ r z ->
             eval σ₂ (tapp σ₁ σ₂ m₁ m₂) z
  | eapp2 : forall σ₁ σ₂ m₁ m₂ n₁ n₂,
             eval (σ₁ ⇒ σ₂) m₁ n₁ ->
             eval σ₁ m₂ n₂ ->
             ~(exists r, redex σ₁ σ₂ n₁ n₂ r) ->
             eval σ₂ (tapp σ₁ σ₂ m₁ m₂) (tapp σ₁ σ₂ n₁ n₂).

Fixpoint tydom (τ:ty) : PLT :=
  match τ with
  | ty_bool => disc finbool
  | ty_arrow τ₁ τ₂ => PLT.exp (tydom τ₁) (tydom τ₂)
  end.

Fixpoint denote (τ:ty) (m:term τ) : PLT.unit false → tydom τ :=
  match m with
  | tbool b => disc_elem b
  | tapp σ₁ σ₂ m₁ m₂ => PLT.app ∘ PLT.pair (denote (σ₁ ⇒ σ₂) m₁) (denote σ₁ m₂)
  | tI σ => PLT.curry PLT.pi2
  | tK σ₁ σ₂ => PLT.curry (PLT.curry (PLT.pi2 ∘ PLT.pi1))
  | tS σ₁ σ₂ σ₃ => PLT.curry (PLT.curry (PLT.curry (
                     PLT.app ∘ PLT.pair
                       (PLT.app ∘ PLT.pair (PLT.pi2 ∘ PLT.pi1 ∘ PLT.pi1) (PLT.pi2))
                       (PLT.app ∘ PLT.pair (PLT.pi2 ∘ PLT.pi1) (PLT.pi2))
                      )))
  | tIF σ => PLT.curry (disc_cases (fun b:bool =>
                 if b then PLT.curry (PLT.curry (PLT.pi2 ∘ PLT.pi1)) 
                      else PLT.curry (PLT.curry (PLT.pi2))
             ))
  end.

Lemma redex_soundness : forall σ₁ σ₂ x y z,
  redex σ₁ σ₂ x y z ->
  PLT.app ∘ PLT.pair (denote _ x) (denote _ y) ≈ denote _ z.
Proof.
  intros. case H; simpl.
  intros.
  rewrite PLT.curry_apply2.
  rewrite pair_commute2. auto.
  intros.
  rewrite PLT.curry_apply2.
  rewrite PLT.curry_apply3.
  rewrite <- (cat_assoc (PLT.PLT false) _ _ _ _ PLT.pi2).
  rewrite pair_commute1.
  rewrite pair_commute2.
  auto.
  intros.
  rewrite PLT.curry_apply2.
  rewrite PLT.curry_apply3.
  rewrite PLT.curry_apply3.
  rewrite <- (cat_assoc (PLT.PLT false)).
  apply cat_respects. auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq.
  rewrite <- (cat_assoc (PLT.PLT false)).
  apply cat_respects. auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq.
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  rewrite pair_commute1.
  rewrite pair_commute1.
  rewrite pair_commute2. auto.
  rewrite pair_commute2. auto.
  rewrite <- (cat_assoc (PLT.PLT false)).
  apply cat_respects. auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq.
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  rewrite pair_commute1.
  rewrite pair_commute2. auto.
  rewrite pair_commute2. auto.

  intros.
  rewrite PLT.curry_apply2.
  rewrite disc_cases_elem.
  rewrite PLT.curry_apply3.
  rewrite PLT.curry_apply3.
  rewrite <- (cat_assoc (PLT.PLT false)).
  rewrite pair_commute1.  
  rewrite pair_commute2.
  auto.

  intros.
  rewrite PLT.curry_apply2.
  rewrite disc_cases_elem.
  rewrite PLT.curry_apply3.
  rewrite PLT.curry_apply3.
  rewrite pair_commute2.
  auto.
Qed.

Lemma soundness : forall τ (m z:term τ),
  eval τ m z -> denote τ m ≈ denote τ z.
Proof.
  intros. induction H; simpl; auto.
  rewrite IHeval1.
  rewrite IHeval2.
  rewrite <- IHeval3.
  apply redex_soundness. auto.
  rewrite IHeval1.
  rewrite IHeval2.
  auto.
Qed.

Lemma eval_value τ x y :
  eval τ x y -> eval τ y y.
Proof.
  intro H. induction H.
  apply ebool.
  apply eI.
  apply eK.
  apply eS.
  apply eIF.
  auto.
  apply eapp2; auto.
Qed.

Lemma inj_pair2_ty : forall (F:ty -> Type) τ x y,
  existT F τ x = existT F τ y -> x = y.
Proof.
  intros.
  apply Eqdep_dec.inj_pair2_eq_dec in H. auto.
  decide equality.
Qed.

Ltac inj_ty :=
  repeat match goal with
           [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
             apply inj_pair2_ty in H
           end.

Ltac inv H :=
  inversion H; subst; inj_ty; repeat subst.

Lemma redex_eq τ₁ τ₂ x y z1 z2 :
  redex τ₁ τ₂ x y z1 ->
  redex τ₁ τ₂ x y z2 ->
  z1 = z2.
Proof.
  intros; inv H; inv H; inv H0; auto.
Qed.

Lemma eval_app_inv σ₁ σ₂ x y z :
  eval _ (tapp σ₁ σ₂ x y) z ->
  exists x', exists y',
    eval _ x x' /\ eval _ y y' /\
    eval _ (tapp _ _ x' y') z.
Proof.
  intros. inv H.
  exists n₁. exists n₂.
  intuition.
  eapply eapp1.
  eapply eval_value; eauto.
  eapply eval_value; eauto.
  eauto. auto.
  exists n₁. exists n₂.
  intuition.
  apply eapp2.
  eapply eval_value; eauto.
  eapply eval_value; eauto.
  auto.
Qed.


Lemma eval_eq τ x y1 y2 :
  eval τ x y1 -> eval τ x y2 -> y1 = y2.
Proof.
  intro H. revert y2.
  induction H.

  intros. inv H. auto.
  intros. inv H. auto.
  intros. inv H. auto.
  intros. inv H. auto.
  intros. inv H. auto.

  intros. inv H3.
  apply IHeval1 in H9.
  apply IHeval2 in H10.
  subst n₁0 n₂0.
  assert (r = r0).
  eapply redex_eq; eauto.
  subst r0.
  apply IHeval3; auto.
  apply IHeval1 in H9.
  apply IHeval2 in H10.
  subst n₁0 n₂0.
  elim H11; eauto.

  intros. inv H2.
  apply IHeval1 in H8.
  apply IHeval2 in H9.
  subst n₁0 n₂0.
  elim H1. eauto.
  f_equal; auto.
Qed.


Lemma eval_trans τ x y z :
  eval τ x y -> eval τ y z -> eval τ x z.
Proof.
  intros.
  replace z with y; auto.
  eapply eval_eq with y; auto.
  eapply eval_value; eauto.
Qed.


Lemma eval_app_congruence σ₁ σ₂ : forall x x' y y' z,
  (forall q, eval _ x q -> eval _ x' q) ->
  (forall q, eval _ y q -> eval _ y' q) ->
  eval _ (tapp σ₁ σ₂ x y) z ->
  eval _ (tapp σ₁ σ₂ x' y') z.
Proof.
  intros.
  inv H1.
  apply H in H7.
  apply H0 in H8.
  eapply eapp1; eauto.
  apply eapp2; auto.
Qed.


Lemma eval_app_congruence' σ₁ σ₂ : forall x x' y y' z1 z2,
  (forall q, eval _ x q -> eval _ x' q) ->
  (forall q, eval _ y q -> eval _ y' q) ->
  eval _ (tapp σ₁ σ₂ x y) z1 ->
  eval _ (tapp σ₁ σ₂ x' y') z2 ->
  z1 = z2.
Proof.
  intros.
  apply eval_app_inv in H1.
  destruct H1 as [p [q [?[??]]]].
  apply H in H1.
  apply H0 in H3.
  apply eval_app_inv in H2.
  destruct H2 as [p' [q' [?[??]]]].
  assert (p = p').
  eapply eval_eq; eauto.
  assert (q = q').
  eapply eval_eq; eauto.
  subst p' q'.
  eapply eval_eq; eauto.
Qed.


Lemma eval_redex_walk : forall t1 t2 x y z q,
  redex t1 t2 x y z ->
  eval _ x x ->
  eval _ y y ->
  eval _ (tapp _ _ x y) q ->
  eval _ z q.
Proof.
  intros.
  inv H2.
  assert (x = n₁). eapply eval_eq; eauto.
  assert (y = n₂). eapply eval_eq; eauto.
  subst n₁ n₂.
  assert (r = z). eapply redex_eq; eauto.
  subst r. auto.
  assert (x = n₁). eapply eval_eq; eauto.
  assert (y = n₂). eapply eval_eq; eauto.
  subst n₁ n₂.
  elim H10.   eauto.
Qed.


Fixpoint LR (τ:ty) : term τ -> (PLT.unit false → tydom τ) -> Prop :=
  match τ as τ' return term τ' -> (PLT.unit false → tydom τ') -> Prop
  with
  | ty_bool => fun m h => exists b:bool, m = tbool b /\ h ≈ disc_elem b
  | ty_arrow σ₁ σ₂ => fun m h =>
        forall n h', LR σ₁ n h' -> eval σ₁ n n ->
                     exists z, eval _ (tapp σ₁ σ₂ m n) z /\
                      LR σ₂ z (PLT.app ∘ PLT.pair h h')

  end.


Lemma LR_equiv τ : forall m h h',
  h ≈ h' -> LR τ m h -> LR τ m h'.
Proof.
  induction τ; simpl. intros.
  destruct H0 as [b [??]]. exists b; split; auto.
  rewrite <- H; auto.
  simpl; intros.
  destruct (H0 n h'0 H1 H2) as [z [??]].
  exists z; split; auto.
  revert H4. apply IHτ2.
  apply cat_respects; auto.
  apply PLT.pair_eq; auto.
Qed.

Fixpoint lrtys (ts:list ty) (z:ty) :=
  match ts with
  | nil => z
  | t::ts' => t ⇒ (lrtys ts' z)
  end.

Fixpoint lrsyn (ts:list ty) : Type :=
  match ts with
  | nil => unit
  | t::ts' => prod (lrsyn ts') (term t)
  end.

Fixpoint lrsem (ts:list ty) : Type :=
  match ts with
  | nil => unit
  | t::ts' => prod (lrsem ts') (PLT.unit false → tydom t)
  end.

Fixpoint lrhyps (ls:list ty) : lrsyn ls -> lrsem ls -> Prop :=
  match ls with
  | nil => fun _ _ => True
  | t::ts => fun xs ys =>
    eval _ (snd xs) (snd xs) /\
    LR t (snd xs) (snd ys) /\ lrhyps ts (fst xs) (fst ys)
  end.

Fixpoint lrapp (ls:list ty) z : lrsyn ls -> term (lrtys ls z) -> term z :=
  match ls as ls' return lrsyn ls' -> term (lrtys ls' z) -> term z with
  | nil => fun _ m => m
  | t::ts => fun xs m => lrapp ts _ (fst xs) (tapp _ _ m (snd xs))
  end.

Fixpoint lrsemapp (ls:list ty) z :
  lrsem ls -> (PLT.unit false → tydom (lrtys ls z)) -> (PLT.unit false → tydom z) :=
  match ls as ls' return
    lrsem ls' ->
    (PLT.unit false → tydom (lrtys ls' z)) -> (PLT.unit false → tydom z)
  with
  | nil => fun _ h => h
  | t::ts => fun ys h => lrsemapp ts _ (fst ys) (PLT.app ∘ PLT.pair h (snd ys))
  end.


Lemma eval_lrapp_congruence ls : forall xs τ m m' z,
  (forall q, eval _ m q -> eval _ m' q) ->
  eval τ (lrapp ls τ xs m) z ->
  eval τ (lrapp ls τ xs m') z.
Proof.
  induction ls; simpl; intros.
  apply H. auto.
  fold lrtys in *.

  revert H0. apply IHls.
  intros.
  inv H0.
  apply H in H6.
  eapply eapp1; eauto.
  eapply eapp2; eauto.
Qed.

Lemma lrsemapp_equiv ls : forall τ ys h h',
  h ≈ h' -> lrsemapp ls τ ys h ≈ lrsemapp ls τ ys h'.
Proof.
  induction ls; simpl; intros; auto.
  apply IHls.
  apply cat_respects; auto.
  apply PLT.pair_eq; auto.
Qed.


Arguments tapp [_ _] _ _.

Section push_under2.
  Variables a b c d:ty.
  Variable f:term (a ⇒ b ⇒ c ⇒ d).
  Variable (x:term c).

  Notation "p @ q" := (tapp p q).
  Notation S := (tS _ _ _).
  Notation K := (tK _ _).
  Notation I := (tI _).

  Definition push_under2 : term (a ⇒ b ⇒ d) :=
    S@((S@(K@S))@(S@((S@(K@S))@((S@(K@K))@((S@(K@ f ))@I)))@(K@I)))@(K@(K@ x )).

  Definition push_under1 (z:term (b ⇒ c ⇒ d)) : term (b ⇒ d) :=
    (S@((S@(K@ z ))@I))@(K@ x ).
End push_under2.

Lemma push_under2_value : forall a b c d f x,
  eval _ f f ->
  eval _ x x ->
  eval _ (push_under2 a b c d f x) (push_under2 a b c d f x).
Proof.
  intros.
  unfold push_under2.
  repeat (apply eapp2 || apply eS || apply eK || apply eI); auto;
    try (intros [r Hr]; inversion Hr).
Qed.

Lemma eapp : forall σ₁ σ₂ m₁ m₂ n₁ n₂ z,
   eval (σ₁ ⇒ σ₂) m₁ n₁ ->
   eval σ₁ m₂ n₂ ->
   (exists r, redex σ₁ σ₂ n₁ n₂ r /\ eval σ₂ r z)
   \/
   ((forall r, ~redex σ₁ σ₂ n₁ n₂ r) /\ z = tapp n₁ n₂) ->
   eval σ₂ (tapp m₁ m₂) z.
Proof.
  intros. destruct H1.
  destruct H1 as [r [??]].
  eapply eapp1; eauto.
  destruct H1.
  subst z.
  apply eapp2; auto.
  intros [r ?]. apply (H1 r); auto.
Qed.

Lemma push_under1_plus1 : forall b c d w x p z,
  eval _ (tapp (tapp w p) x) z ->
  eval _ (tapp (push_under1 b c d x w) p) z.
Proof.
  intros.
  apply eval_app_inv in H.
  destruct H as [wp [x' [?[??]]]].
  apply eval_app_inv in H.
  destruct H as [w' [p' [?[??]]]].
  unfold push_under1.
  eapply eapp. 2: eauto.
  eapply eapp.
  apply eapp2. apply eS.
  apply eapp2. apply eapp2. apply eS.
  apply eapp2. apply eK. eauto.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  apply eI.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  apply eapp2. apply eK. eauto.
  intros [? Hr]; inv Hr.
  right. split.
  intros r Hr; inversion Hr.
  reflexivity.
  left. econstructor; split. apply redex_S.

  revert H1.
  apply eval_app_congruence. intros.
  eapply eapp.
  apply eapp2. apply eapp2.
  apply eS.
  apply eapp2. apply eK.
  eapply eval_value; eauto.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  apply eI.
  intros [? Hr]; inv Hr.
  eapply eval_value; eauto.
  left. econstructor; split. apply redex_S.
  apply eval_trans with wp; auto.
  revert H3.
  eapply eval_app_congruence.
  intros.
  eapply eapp1.
  apply eapp2. apply eK.
  apply H3.
  intros [? Hr]; inv Hr.
  eapply eval_value; eauto.
  apply redex_K.
  eapply eval_value; eauto.
  intros.
  eapply eapp1. apply eI.
  eapply eval_value; eauto.
  apply redex_I. auto.

  intros.
  eapply eapp1.
  apply eapp2. apply eK.
  eapply eval_value; eauto.
  intros [? Hr]; inv Hr.
  eapply eval_value; eauto.
  apply redex_K.
  auto.
Qed.

Lemma push_under2_plus1 : forall a b c d f x p z,
  eval _ f f ->
  eval _ x x ->
  eval _ p p ->
  eval _ (tapp f p) z ->
  eval _ (tapp (push_under2 a b c d f x) p)
         (push_under1 b c d x z).
Proof.
  intros. unfold push_under2.
  eapply eapp1. 2: eauto.
  apply push_under2_value; auto.
  unfold push_under2.
  apply redex_S.
  eapply eapp.
  eapply eapp. 2: eauto.
  apply eapp2.
  apply eapp2. apply eS.
  apply eapp2. apply eK. apply eS.
  intros [? Hr]. inv Hr.
  intros [? Hr]. inv Hr.
  apply eapp2. eapply eapp2. apply eS.
  apply eapp2. eapply eapp2. apply eS.
  apply eapp2. apply eK. apply eS.
  intros [? Hr]. inv Hr.
  intros [? Hr]. inv Hr.
  apply eapp2. apply eapp2. apply eS.
  apply eapp2. apply eK. apply eK.
  intros [? Hr]. inv Hr.
  intros [? Hr]. inv Hr.
  apply eapp2. apply eapp2. apply eS.
  apply eapp2. apply eK. eauto.
  intros [? Hr]. inv Hr.
  intros [? Hr]. inv Hr.
  apply eI.
  intros [? Hr]. inv Hr.
  intros [? Hr]. inv Hr.
  intros [? Hr]. inv Hr.
  intros [? Hr]. inv Hr.
  apply eapp2. apply eK. apply eI.
  intros [? Hr]. inv Hr.
  intros [? Hr]. inv Hr.
  intros [? Hr]. inv Hr.
  left. econstructor. split.
  apply redex_S.
  eapply eapp.
  eapply eapp.
  apply eapp2. apply eK. apply eS.
  intros [? Hr]. inv Hr.
  eauto.
  left. econstructor. split.
  apply redex_K.
  apply eS.
  eapply eapp.
  apply eapp2. apply eapp2. apply eS.
  apply eapp2. apply eapp2. apply eS.
  apply eapp2. apply eK. apply eS.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  apply eapp2. apply eapp2. apply eS.
  apply eapp2. apply eK. apply eK.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  apply eapp2. apply eapp2. apply eS.
  apply eapp2. apply eK. eauto.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  apply eI.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  apply eapp2. apply eK. apply eI.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  eauto.
  left; econstructor; split.
  apply redex_S.

  eapply eapp.
  eapply eapp.
  apply eapp2. apply eapp2. apply eS.
  apply eapp2. apply eK. apply eS.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  apply eapp2. apply eapp2. apply eS.
  apply eapp2. apply eK. apply eK.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  apply eapp2. apply eapp2. apply eS.
  apply eapp2. apply eK. eauto.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  apply eI.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  eauto.
  left; econstructor; split. apply redex_S.
  eapply eapp.
  eapply eapp.
  apply eapp2. apply eK. apply eS.
  intros [? Hr]; inv Hr. eauto.
  left; econstructor; split. apply redex_K.
  apply eS.
  eapply eapp.
  apply eapp2. apply eapp2. apply eS.
  apply eapp2. apply eK. apply eK.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  apply eapp2. apply eapp2. apply eS.
  apply eapp2. apply eK. eauto.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  apply eI.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  eauto.
  left; econstructor; split. apply redex_S.

  eapply eapp.
  eapply eapp.
  apply eapp2. apply eK. apply eK.
  intros [? Hr]; inv Hr.
  eauto.
  left; econstructor; split. apply redex_K.
  apply eK.

  eapply eapp.
  eapply eapp2. apply eapp2. apply eS.
  apply eapp2. apply eK. eauto.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  apply eI.
  intros [? Hr]; inv Hr.
  eauto.
  left; econstructor; split. apply redex_S.
  apply (eval_app_congruence) with f p.
  intros. replace q with f in *.
  eapply eapp.
  apply eapp2. apply eK. eauto.
  intros [? Hr]; inv Hr.
  eauto.
  left; econstructor; split. apply redex_K.
  auto.
  eapply eval_eq; eauto.
  intros.
  eapply eapp1. apply eI. eauto.
  apply redex_I. eapply eval_value; eauto.
  apply H2.
  right. split.
  intros r Hr; inversion Hr.
  reflexivity.
  right. split.
  intros r Hr; inversion Hr.
  reflexivity.
  eapply eapp1.
  apply eapp2. apply eK. apply eI.
  intros [? Hr]; inv Hr.
  eauto.
  apply redex_K.
  apply eI.
  right. split.
  intros r Hr; inversion Hr. reflexivity.
  right. split.
  intros r Hr; inversion Hr. reflexivity.
  eapply eapp.
  apply eapp2. apply eK.
  apply eapp2. apply eK. eauto.
  intros [? Hr]; inv Hr.
  intros [? Hr]; inv Hr.
  eauto.
  left; econstructor; split. apply redex_K.
  apply eapp2. apply eK. eauto.
  intros [? Hr]; inv Hr.

  right. split.
  intros r Hr. inversion Hr.
  reflexivity.
Qed.


Section push_under2_denote.
  Variables a b c d:ty.
  Variable f:PLT.unit false → tydom (a ⇒ b ⇒ c ⇒ d).
  Variable x:PLT.unit false → tydom c.

  Definition push_under2_denote : PLT.unit false → tydom (a ⇒ b ⇒ d) :=
    (PLT.curry (PLT.curry (
           PLT.app ∘ PLT.pair
               (PLT.app ∘ PLT.pair
                    (PLT.app ∘ PLT.pair (f ∘ PLT.pi1 ∘ PLT.pi1) (PLT.pi2 ∘ PLT.pi1))
                    (PLT.pi2))
               (x ∘ PLT.pi1 ∘ PLT.pi1)
           ))).

End push_under2_denote.

Arguments push_under2 [a b c d] f x.
Arguments push_under2_denote [a b c d] f x.
Arguments push_under1 [b c d] x z.

Lemma LR_S ls : forall σ t τ
  (xs : lrsyn (t ⇒ σ ⇒ lrtys ls τ :: t ⇒ σ :: t :: ls))
  (ys : lrsem (t ⇒ σ ⇒ lrtys ls τ :: t ⇒ σ :: t :: ls))
  (H : lrhyps (t ⇒ σ ⇒ lrtys ls τ :: t ⇒ σ :: t :: ls) xs ys),

   exists z : term τ,
     eval τ
       (lrapp (t ⇒ σ ⇒ lrtys ls τ :: t ⇒ σ :: t :: ls) τ xs
          (tS t σ (lrtys ls τ))) z /\
     LR τ z
       (lrsemapp (t ⇒ σ ⇒ lrtys ls τ :: t ⇒ σ :: t :: ls) τ ys
          (denote (lrtys (t ⇒ σ ⇒ lrtys ls τ :: t ⇒ σ :: t :: ls) τ)
             (tS t σ (lrtys ls τ)))).
Proof.
  induction ls; simpl; intros.
  destruct xs as [[[xs x3] x2] x1].
  destruct ys as [[[ys y3] y2] y1].
  simpl in *.
  destruct H as [?[?[?[?[?[??]]]]]]. clear H5.
  destruct (H2 x3 y3) as [z1 [??]]; auto; clear H2.
  destruct (H0 x3 y3) as [z2 [??]]; auto; clear H0.
  destruct (H7 z1 (PLT.app ∘ PLT.pair y2 y3)) as [z3 [??]]; auto; clear H7.
  eapply eval_value; eauto.
  exists z3.
  split.
  intros.
  eapply eapp1.
  apply eapp2.
  apply eapp2.
  apply eS.
  eauto. intros [? Hr]; inv Hr.
  eauto. intros [? Hr]; inv Hr.
  eauto.
  apply redex_S.
  revert H0.
  apply eval_app_congruence.
  intros.
  replace q with z2. auto.
  apply eval_eq with z2; auto.
  eapply eval_value; eauto.
  intros.
  replace q with z1. auto.
  apply eval_eq with z1; auto.
  eapply eval_value; eauto.
  revert H8.
  apply LR_equiv.
  rewrite PLT.curry_apply2.
  repeat rewrite PLT.curry_apply3.
  rewrite <- (cat_assoc (PLT.PLT false)).
  apply cat_respects; auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq.
  rewrite <- (cat_assoc (PLT.PLT false)).
  apply cat_respects; auto.
  rewrite (PLT.pair_compose_commute false).
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  auto.

  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  apply cat_respects; auto.
  rewrite (PLT.pair_compose_commute false).
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  auto.

  destruct xs as [[[[xs x4] x3] x2] x1].
  destruct ys as [[[[ys y4] y3] y2] y1].
  simpl in *.
  destruct H as [?[?[?[?[?[??]]]]]]. destruct H5 as [?[??]].
  fold lrtys in *.

  destruct (IHls σ t τ
    (xs,x3,x2, push_under2 x1 x4)
    (ys,y3,y2, push_under2_denote y1 y4)) as [q1 [??]]; clear IHls.

  simpl. intuition.
  apply push_under2_value; auto.
  destruct (H0 n h') as [z1 [??]]; clear H0; auto.
  exists (push_under1 x4 z1).
  split.
  apply push_under2_plus1; auto.

  intros.
  destruct (H11 n0 h'0) as [z2 [??]]; clear H11; auto.
  destruct (H14 x4 y4) as [z3 [??]]; clear H14; auto.
  exists z3. split.

  eapply push_under1_plus1; eauto.
  revert H11.
  apply eval_app_congruence; auto. intros.
  eapply eval_trans with z2; auto.

  revert H15. apply LR_equiv.
  unfold push_under2_denote. simpl.
  repeat rewrite PLT.curry_apply2.
  repeat rewrite PLT.curry_apply3.
  rewrite <- (cat_assoc (PLT.PLT false)).
  apply cat_respects; auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq.
  rewrite <- (cat_assoc (PLT.PLT false)).
  apply cat_respects; auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq.
  rewrite <- (cat_assoc (PLT.PLT false)).
  rewrite (PLT.pair_compose_commute false).
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  apply cat_respects; auto.
  apply PLT.pair_eq; auto.
  symmetry; apply cat_ident1.
  rewrite pair_commute2. auto.
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  symmetry; apply cat_ident1.

  simpl in *.
  exists q1. split.
  revert H8.
  apply eval_lrapp_congruence.
  intros.
  assert (eval (lrtys ls τ)
    (tapp (tapp (push_under2 x1 x4) x3) (tapp x2 x3)) q).

  rename H into Hx1.
  rename H1 into Hx2.
  rename H3 into Hx3.
  rename H5 into Hx4.

  clear -H8 Hx1 Hx2 Hx3 Hx4.
  inv H8. inv H4.
  inv H9.
  inv H13.
  inv H15.
  inv H13. clear H3 H16 H17. clear H13. inv H11.
  inv H9.
  inv H12.
  inv H14.
  inv H12. clear H12.
  inv H9. inv H18.
  inv H20. clear H18.
  assert (n₂1 = push_under2 x1 x4).
  eapply eval_eq. eauto.
  apply push_under2_value; auto.
  subst n₂1. clear H20.
  clear H11 H14 H21. clear H9.
  inv H6. clear H9 H11 H12.
  clear H6.
  revert H7.
  apply eval_app_congruence; auto. intro.
  apply eval_app_congruence; auto. intros.
  replace q1 with n₂; auto.
  symmetry.
  eapply eval_eq. apply H.
  eapply eval_value; eauto.
  intro.
  apply eval_app_congruence; auto; intros.
  replace q1 with n₂0; auto.
  symmetry.
  eapply eval_eq. apply H.
  eapply eval_value; eauto.
  replace q1 with n₂; auto.
  symmetry.
  eapply eval_eq. apply H.
  eapply eval_value; eauto.
  inv H4. inv H7.
  inv H12.
  inv H14.
  inv H12.
  inv H10.
  inv H7.
  inv H11.
  inv H13.
  inv H11.
  clear H11.
  elim H6.
  econstructor. eapply redex_S.

  cut (eval _ (tapp (tapp (tapp x1 x3) (tapp x2 x3)) x4) q).
  apply eval_app_congruence; auto. intros.
  eapply eapp1.
  apply eapp2.
  apply eapp2.
  apply eS.
  eauto.
  intros [? Hr]; inversion Hr.
  eauto.
  intros [? Hr]; inversion Hr.
  eauto.
  apply redex_S.
  auto.
  clear H9.

  apply eval_app_inv in H10.
  destruct H10 as [v1 [v2 [?[??]]]].
  destruct (H0 x3 y3) as [z1 [??]]; auto; clear H0.
  generalize (push_under2_plus1 _ _ _ _ x1 x4 x3 z1 H H5 H3 H12).
  intros.
  assert (v1 = push_under1 x4 z1).
  eapply eval_eq; eauto. subst v1.
  clear H0 H9.

  unfold push_under1 in H11.
  eapply eval_redex_walk in H11.
  2: apply redex_S.
  eapply eval_app_congruence in H11.
  apply H11.
  intros. eapply eval_redex_walk in H0.
  2: apply redex_S.
  eapply eval_app_congruence in H0. apply H0.
  intros. eapply eval_redex_walk in H9.
  2: apply redex_K.
  apply eval_trans with z1; auto.
  apply eapp2. apply eK.
  eapply eval_value; eauto.
  intros [r Hr]; inversion Hr.
  eapply eval_value; eauto.
  intros. eapply eval_redex_walk in H9.
  2: apply redex_I.
  apply eval_trans with v2; auto.
  apply eI.
  eapply eval_value; eauto.
  apply eapp2. apply eapp2.
  apply eS. apply eapp2. apply eK.
  eapply eval_value; eauto.
  intros [r Hr]; inversion Hr.
  intros [r Hr]; inversion Hr.
  apply eI.
  intros [r Hr]; inversion Hr.
  eapply eval_value; eauto.
  intros. eapply eval_redex_walk in H0.
  2: apply redex_K. auto.
  apply eapp2. apply eK.
  eapply eval_value; eauto.
  intros [r Hr]; inversion Hr.
  eapply eval_value; eauto.
  apply eapp2. apply eapp2.
  apply eS.
  apply eapp2. apply eapp2.
  apply eS. apply eapp2. apply eK.
  eapply eval_value; eauto.
  intros [r Hr]; inversion Hr.
  intros [r Hr]; inversion Hr.
  apply eI.
  intros [r Hr]; inversion Hr.
  intros [r Hr]; inversion Hr.
  apply eapp2.
  apply eK.
  eapply eval_value; eauto.
  intros [r Hr]; inversion Hr.
  intros [r Hr]; inversion Hr.
  eapply eval_value; eauto.

  revert H9.
  apply LR_equiv.
  apply lrsemapp_equiv.
  unfold push_under2_denote.

  clear.
  repeat rewrite PLT.curry_apply2.
  repeat rewrite PLT.curry_apply3.
  rewrite <- (cat_assoc (PLT.PLT false)).
  rewrite (PLT.pair_compose_commute false).
  repeat rewrite PLT.curry_apply2.
  repeat rewrite PLT.curry_apply3.
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite (PLT.pair_compose_commute false).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  rewrite (PLT.curry_apply2 false).
  rewrite (PLT.curry_apply3 false).
  rewrite <- (cat_assoc (PLT.PLT false)).
  rewrite (PLT.pair_compose_commute false).
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  apply cat_respects. auto.
  apply PLT.pair_eq.
  rewrite (PLT.pair_compose_commute false).
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  apply cat_respects. auto.
  apply PLT.pair_eq.
  apply cat_respects; auto.
  do 2 rewrite (PLT.pair_compose_commute false).
  apply (PLT.pair_eq false).
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  apply cat_ident1.
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  auto.
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  apply cat_respects; auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq.
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  auto.
  rewrite pair_commute2.
  auto.
  apply cat_ident1.
Qed.


Lemma LR_I ls τ : forall
  (xs : lrsyn (lrtys ls τ :: ls))
  (ys : lrsem (lrtys ls τ :: ls))
  (H : lrhyps (lrtys ls τ :: ls) xs ys),
   exists z : term τ,
     eval τ (lrapp (lrtys ls τ :: ls) τ xs (tI (lrtys ls τ))) z /\
     LR τ z
       (lrsemapp (lrtys ls τ :: ls) τ ys
          (denote (lrtys (lrtys ls τ :: ls) τ) (tI (lrtys ls τ)))).
Proof.
  induction ls; simpl in *; intuition; fold lrtys in *; simpl in *.
  exists b. split.
  eapply eapp1. apply eI.
  eauto. apply redex_I. auto.
  revert H. apply LR_equiv.
  rewrite PLT.curry_apply2.
  rewrite pair_commute2. auto.

  destruct ys as [[ys y1] y2]; simpl in *.
  destruct (H b0 y1) as [z1 [??]]; auto; clear H.
  destruct (IHls (a1, z1) (ys, PLT.app ∘ PLT.pair y2 y1))
    as [z2 [??]]; intuition; clear IHls.
  simpl.
  eapply eval_value; eauto.

  exists z2. split.
  revert H. simpl.
  eapply eval_lrapp_congruence; eauto.
  intros.
  inv H. inv H12. inv H14.
  clear H12 H14.
  eapply eval_trans with r; auto.
  eapply eval_trans with z1; auto.
  revert H3.
  apply eval_app_congruence; auto.
  intros.
  eapply eapp1. apply eI.
  eauto.
  apply redex_I.
  apply eval_value with b; auto.
  inv H12. elim H14.
  exists n₂. apply redex_I.

  revert H6. apply LR_equiv.
  simpl. apply lrsemapp_equiv.
  rewrite PLT.curry_apply2.
  rewrite pair_commute2.
  rewrite PLT.curry_apply2.
  rewrite pair_commute2.
  auto.
Qed.

Lemma LR_K ls τ σ : forall
  (xs : lrsyn (lrtys ls τ :: σ :: ls))
  (ys : lrsem (lrtys ls τ :: σ :: ls))
  (H : lrhyps (lrtys ls τ :: σ :: ls) xs ys),

   exists z : term τ,
     eval τ (lrapp (lrtys ls τ :: σ :: ls) τ xs (tK (lrtys ls τ) σ)) z /\
     LR τ z
       (lrsemapp (lrtys ls τ :: σ :: ls) τ ys
          (denote (lrtys (lrtys ls τ :: σ :: ls) τ) (tK (lrtys ls τ) σ))).
Proof.
  induction ls; simpl; intuition trivial; simpl in *.
  destruct ys as [[ys y1] y2]. simpl in *.
  exists b. split.
  eapply eapp1.
  apply eapp2. apply eK. eauto.
  intros [r Hr]; inversion Hr.
  eauto.
  apply redex_K. eauto.
  revert H. apply LR_equiv.
  rewrite PLT.curry_apply2.
  rewrite PLT.curry_apply3.
  rewrite <- (cat_assoc (PLT.PLT false)).
  rewrite pair_commute1.
  rewrite pair_commute2.
  auto.

  fold lrtys in *.
  destruct ys as [[ys y1] y2]. simpl in *.
  destruct ys as [ys y']. simpl in *.
  destruct (H b1 y') as [z [??]]; auto.
  destruct (IHls (a0,b0,z) (ys,y1,PLT.app ∘ PLT.pair y2 y'));
    intuition.
  simpl.
  eapply eval_value; eauto.
  exists x. simpl; split.
  revert H9. simpl.
  apply eval_lrapp_congruence. intros.
  inv H8.
  inv H15. inv H19. inv H21.
  inv H19. clear H19. inv H17. clear H17.
  apply eval_trans with r; auto.
  apply eval_trans with z; auto.
  revert H5.
  apply eval_app_congruence; auto.
  intros.
  eapply eapp1.
  apply eapp2. apply eK. eauto.
  intros [? Hr]; inversion Hr.
  eauto.
  apply redex_K.
  eapply eval_value; eauto.
  inv H15. inv H18. inv H20.
  inv H15. inv H21. inv H23.
  inv H21. elim H17.
  econstructor. apply redex_K.
  revert H10. apply LR_equiv.
  apply lrsemapp_equiv. simpl.
  repeat rewrite PLT.curry_apply2.
  repeat rewrite PLT.curry_apply3.
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  auto.
Qed.

Lemma LR_IF ls : forall τ
  (xs : lrsyn (ty_bool :: lrtys ls τ :: lrtys ls τ :: ls))
  (ys : lrsem (ty_bool :: lrtys ls τ :: lrtys ls τ :: ls))
  (H : lrhyps (ty_bool :: lrtys ls τ :: lrtys ls τ :: ls) xs ys),
   exists z : term τ,
     eval τ
       (lrapp (ty_bool :: lrtys ls τ :: lrtys ls τ :: ls) τ xs
          (tIF (lrtys ls τ))) z /\
     LR τ z
       (lrsemapp (ty_bool :: lrtys ls τ :: lrtys ls τ :: ls) τ ys
          (denote (lrtys (ty_bool :: lrtys ls τ :: lrtys ls τ :: ls) τ)
             (tIF (lrtys ls τ)))).
Proof.
  induction ls; simpl; intros.
  destruct xs as [[[xs x1] x2] x3]. simpl in *.
  destruct ys as [[[ys y1] y2] y3]. simpl in *. intuition. clear H6.
  destruct H as [b [??]]. subst x3. destruct b; simpl.
  exists x2. split.
  eapply eapp1. 
  apply eapp2. apply eapp2. apply eIF. apply ebool.
  intros [r Hr]; inversion Hr. eauto.
  intros [r Hr]; inversion Hr. eauto.
  econstructor. auto.
  revert H2. apply LR_equiv.
  rewrite PLT.curry_apply2. rewrite H5.
  rewrite disc_cases_elem.
  rewrite PLT.curry_apply3.
  rewrite PLT.curry_apply3.
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  auto.    

  exists x1. split.
  eapply eapp1.
  apply eapp2. apply eapp2. apply eIF. apply ebool.
  intros [r Hr]; inversion Hr. eauto.
  intros [r Hr]; inversion Hr. eauto.
  econstructor. auto.
  revert H4. apply LR_equiv.
  rewrite PLT.curry_apply2. rewrite H5.
  rewrite disc_cases_elem.
  rewrite PLT.curry_apply3.
  rewrite PLT.curry_apply3.
  repeat rewrite pair_commute2.
  auto.    
  
  destruct xs as [[[[xs x0] x1] x2] x3]. simpl in *.
  destruct ys as [[[[ys y0] y1] y2] y3]. simpl in *. intuition.
  destruct (H4 x0 y0) as [z1 [??]]; auto; clear H4.
  destruct (H2 x0 y0) as [z2 [??]]; auto; clear H2.

  destruct (IHls τ 
    (xs,z1,z2,x3)
    (ys,PLT.app ∘ PLT.pair y1 y0, PLT.app ∘ PLT.pair y2 y0, y3))
    as [z [??]]; clear IHls; simpl; intuition.
  eapply eval_value; eauto.    
  eapply eval_value; eauto.    
  simpl in *.
  exists z. split.
  clear H11.
  destruct H as [b [??]]. subst x3.
  revert H2. apply eval_lrapp_congruence.
  intro q. intro.
  destruct b.

  eapply eval_redex_walk in H. 
  2: econstructor. fold lrtys in *.
  apply eval_trans with z2; auto.
  revert H4. apply eval_app_congruence; auto. intros.
  eapply eapp1. apply eapp2. apply eapp2. apply eIF. apply ebool.
  intros [? Hr]; inv Hr. eauto.
  intros [? Hr]; inv Hr. eauto.
  econstructor.
  eapply eval_value; eauto.
  fold lrtys.
  apply eapp2. apply eapp2. apply eIF. apply ebool.
  intros [? Hr]; inv Hr.
  eapply eval_value; eauto.
  intros [? Hr]; inv Hr.
  eapply eval_value; eauto.
  
  eapply eval_redex_walk in H. 
  2: econstructor. fold lrtys in *.
  apply eval_trans with z1; auto.
  revert H7. apply eval_app_congruence; auto. intros.
  eapply eapp1. apply eapp2. apply eapp2. apply eIF. apply ebool.
  intros [? Hr]; inv Hr. eauto.
  intros [? Hr]; inv Hr. eauto.
  econstructor.
  eapply eval_value; eauto.
  fold lrtys.
  apply eapp2. apply eapp2. apply eIF. apply ebool.
  intros [? Hr]; inv Hr.
  eapply eval_value; eauto.
  intros [? Hr]; inv Hr.
  eapply eval_value; eauto.

  revert H11.  
  apply LR_equiv. apply lrsemapp_equiv.
  destruct H as [b [??]]. rewrite H11.
  rewrite PLT.curry_apply2.
  rewrite PLT.curry_apply2.
  rewrite disc_cases_elem.
  rewrite disc_cases_elem.
  destruct b.
  repeat rewrite PLT.curry_apply3.
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  auto.

  repeat rewrite PLT.curry_apply3.
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  auto.
Qed.


Lemma LRok : forall σ (n:term σ) ls τ m xs ys
  (Hσ : σ = lrtys ls τ),
  eq_rect σ term n (lrtys ls τ) Hσ = m ->
  lrhyps ls xs ys ->
  exists z, eval _ (lrapp ls τ xs m) z /\
    LR τ z (lrsemapp ls τ ys (denote _ m)).
Proof.
  induction n; intros.

  (* bool case *)
  destruct ls; simpl in *. subst τ.
  simpl in H. subst m.
  exists (tbool b). split.
  apply ebool.
  simpl. eauto.
  inversion Hσ.

  (* application case *)
  subst σ₂. simpl in H.
  destruct (IHn2 nil σ₁ n2 tt tt (Logic.refl_equal _) (Logic.refl_equal _) I)
    as [q2 [??]].
  destruct (IHn1 (σ₁::ls) _ n1 (xs, q2) (ys, denote σ₁ n2)
    (Logic.refl_equal _) (Logic.refl_equal _)) as [q1 [??]].
  split; intuition.
  simpl. simpl in H1.
  eapply eval_value; eauto.
  simpl in H3. fold lrtys in H3.
  exists q1. split.
  subst m.
  simpl in *.
  revert H3.
  apply eval_lrapp_congruence.
  intro.
  apply eval_app_congruence; auto.
  intros.
  replace q0 with q2; auto.
  apply eval_eq with q2; auto.
  apply eval_value with n2; auto.
  revert H4. apply LR_equiv.
  subst m. auto.

  (* I case *)
  destruct ls.
  simpl in Hσ. subst τ.
  simpl in H. subst m.
  exists (tI σ).
  split. simpl. apply eI.
  simpl. intros.
  apply (LR_I nil σ (tt,n) (tt,h')). simpl.
  intuition.
  simpl in Hσ.
  inversion Hσ. subst σ. subst t.
  replace Hσ with (Logic.eq_refl (lrtys ls τ ⇒ lrtys ls τ)) in H.
  simpl in m.
  simpl in H. subst m.
  apply (LR_I ls τ xs ys). auto.
  apply Eqdep_dec.UIP_dec. decide equality.

  (* K case *)
  destruct ls; inversion Hσ.
  simpl in Hσ. subst τ.
  simpl in H. subst m.
  exists (tK _ _) .
  split. apply eK.
  simpl. intros.
  exists (tapp (tK _ _) n).
  split.
  apply eapp2. apply eK. auto.
  intros [r Hr]; inversion Hr.
  intros.
  apply (LR_K nil σ₁ σ₂ (tt,n0,n) (tt,h'0,h')).
  simpl; intuition.
  simpl in Hσ.
  destruct ls.
  simpl in Hσ.
  inversion Hσ. subst t τ. clear H3.
  replace Hσ with
    (Logic.refl_equal (σ₁ ⇒ σ₂ ⇒ σ₁)) in H. simpl in H.
  subst m.
  destruct xs. destruct ys.
  simpl in H0. intuition.
  simpl lrapp.
  exists (tapp (tK _ _) t).
  split. apply eapp2. apply eK. auto.
  intros [r Hr]; inversion Hr.
  simpl. intros.
  apply (LR_K nil σ₁ σ₂ (tt,n,t) (tt,h',h)).
  simpl; intuition.
  apply Eqdep_dec.UIP_dec. decide equality.

  simpl in Hσ. subst t.
  simpl in H3. inversion H3. subst t0 σ₁.
  replace Hσ with
    (Logic.refl_equal (lrtys ls τ ⇒ σ₂ ⇒ lrtys ls τ)) in H.
  simpl in H. subst m.
  apply LR_K; auto.
  apply Eqdep_dec.UIP_dec. decide equality.

  (* S case *)
  destruct ls; simpl in Hσ; inversion Hσ; subst.
  exists (tS _ _ _).
  split. simpl. apply eS.
  simpl; intros.
  exists (tapp (tS _ _ _) n). split.
  apply eapp2. apply eS. auto.
  intros [? Hr]; inversion Hr.
  intros.
  exists (tapp (tapp (tS _ _ _) n) n0). split.
  apply eapp2. apply eapp2. apply eS. auto.
  intros [? Hr]; inversion Hr. auto.
  intros [? Hr]; inversion Hr. intros.
  apply (LR_S nil _ _ _ (tt,n1,n0,n) (tt,h'1,h'0,h')).
  simpl; intuition.

  destruct ls; simpl in Hσ; inversion Hσ; subst.
  replace Hσ with
    (Logic.refl_equal ((σ₁ ⇒ σ₂ ⇒ σ₃) ⇒ (σ₁ ⇒ σ₂) ⇒ σ₁ ⇒ σ₃)).
  simpl in *.
  destruct xs as [xs x1].
  destruct ys as [ys y1].
  intuition.
  exists (tapp (tS _ _ _) x1). split.
  apply eapp2. apply eS. simpl. auto.
  intros [? Hr]; inversion Hr.
  intros.
  exists (tapp (tapp (tS _ _ _) x1) n). split.
  apply eapp2. apply eapp2. apply eS. auto.
  intros [? Hr]; inversion Hr. auto.
  intros [? Hr]; inversion Hr. intros.
  apply (LR_S nil _ _ _ (tt,n0,n,x1) (tt,h'0,h',y1)).
  simpl; intuition.
  apply Eqdep_dec.UIP_dec. decide equality.

  destruct ls; simpl in Hσ; inversion Hσ; subst.
  replace Hσ with
    (Logic.refl_equal ((σ₁ ⇒ σ₂ ⇒ σ₃) ⇒ (σ₁ ⇒ σ₂) ⇒ σ₁ ⇒ σ₃)).
  destruct xs as [[xs x2] x1].
  destruct ys as [[ys y2] y1].
  simpl in *. intuition.
  exists (tapp (tapp (tS _ _ _) x1) x2). split.
  apply eapp2. apply eapp2. apply eS. auto.
  intros [? Hr]; inversion Hr. auto.
  intros [? Hr]; inversion Hr. intros.
  apply (LR_S nil _ _ _ (tt,n,x2,x1) (tt,h',y2,y1)).
  simpl; intuition.
  apply Eqdep_dec.UIP_dec. decide equality.

  replace Hσ with
    (Logic.refl_equal ((t ⇒ σ₂ ⇒ lrtys ls τ) ⇒ (t ⇒ σ₂) ⇒ t ⇒ lrtys ls τ)).
  simpl.
  apply LR_S; auto.
  apply Eqdep_dec.UIP_dec. decide equality.

  (* IF case *)
  destruct ls. simpl in Hσ.
  subst τ. simpl in H. subst m.
  exists (tIF σ). split. apply eIF.
  simpl; intros.
  exists (tapp (tIF σ) n). split.
  apply eapp2. apply eIF. inv H1. apply ebool.
  destruct H as [b [??]]. discriminate.
  destruct H as [b [??]]. discriminate.
  intros [? Hr]; inv Hr.
  simpl; intros.
  exists (tapp (tapp (tIF σ) n) n0). split.
  apply eapp2. apply eapp2. apply eIF. auto.
  intros [? Hr]; inv Hr. auto.
  intros [? Hr]; inv Hr. intros.
  apply (LR_IF nil σ (tt,n1,n0,n) (tt,h'1,h'0,h')).
  simpl; intuition.

  destruct ls. simpl in Hσ.
  inversion Hσ. subst t τ.
  replace Hσ with
    (Logic.eq_refl (ty_bool ⇒ σ ⇒ σ ⇒ σ)) in H.
  simpl in H. subst m.
  destruct xs as [xs x1].
  destruct ys as [ys y1]. simpl in *. intuition.
  exists (tapp (tIF σ) x1). split.
  apply eapp2. apply eIF. auto.
  intros [? Hr]; inv Hr.
  intros.
  exists (tapp (tapp (tIF σ) x1) n). split.
  apply eapp2. apply eapp2. apply eIF. auto.
  intros [? Hr]; inv Hr. auto.
  intros [? Hr]; inv Hr.
  intros.
  apply (LR_IF nil σ (tt,n0,n,x1) (tt,h'0,h',y1)).
  simpl; intuition.
  apply Eqdep_dec.UIP_dec. decide equality.

  destruct ls. simpl in Hσ.
  inversion Hσ. subst t t0 τ.
  replace Hσ with
    (Logic.eq_refl (ty_bool ⇒ σ ⇒ σ ⇒ σ)) in H.
  simpl in H. subst m.
  destruct xs as [[xs x1] x2].
  destruct ys as [[ys y1] y2]. simpl in *. intuition.
  exists (tapp (tapp (tIF σ) x2) x1). split.
  apply eapp2. apply eapp2. apply eIF. auto.
  intros [? Hr]; inv Hr. auto.
  intros [? Hr]; inv Hr.
  intros.
  apply (LR_IF nil σ (tt,n,x1,x2) (tt,h',y1,y2)).
  simpl; intuition.
  apply Eqdep_dec.UIP_dec. decide equality.

  simpl in Hσ. inversion Hσ. subst t1 t0 t σ.
  replace Hσ with
    (Logic.eq_refl (ty_bool ⇒ lrtys ls τ ⇒ lrtys ls τ ⇒ lrtys ls τ)) in H.
  simpl in H. subst m.
  apply LR_IF. auto.
  apply Eqdep_dec.UIP_dec. decide equality.
Qed.


Inductive context τ : ty -> Type :=
  | cxt_top : context τ τ
  | cxt_appl : forall σ₁ σ₂,
                    term σ₁ ->
                    context τ σ₂ ->
                    context τ (σ₁ ⇒ σ₂)
  | cxt_appr : forall σ₁ σ₂,
                    term (σ₁ ⇒ σ₂) ->
                    context τ σ₂ ->
                    context τ σ₁.

Fixpoint plug τ σ (C:context τ σ) : term σ -> term τ :=
  match C in context _ σ return term σ -> term τ with
  | cxt_top => fun x => x
  | cxt_appl σ₁ σ₂ t C' => fun x => plug τ _ C' (tapp x t)
  | cxt_appr σ₁ σ₂ t C' => fun x => plug τ _ C' (tapp t x)
  end.

Definition cxt_eq τ σ (m n:term σ):=
  forall (C:context τ σ) (z:term τ),
    eval τ (plug τ σ C m) z <-> eval τ (plug τ σ C n) z.

Lemma adequacy : forall τ (m n:term τ),
  denote τ m ≈ denote τ n -> cxt_eq ty_bool τ m n.
Proof.
  intros. intro.
  revert n m H.
  induction C.

  simpl; intros.
  destruct (LRok _ m nil _ m tt tt (Logic.refl_equal _) (Logic.refl_equal _) I)
    as [zm [??]]. simpl in *.
  destruct (LRok _ n nil _ n tt tt (Logic.refl_equal _) (Logic.refl_equal _) I)
    as [zn [??]]. simpl in *.
  destruct H1 as [bm [??]].
  destruct H3 as [bn [??]].
  subst zm zn.
  rewrite H in H4.
  rewrite H4 in H5.
  assert (bm = bn).
  apply disc_elem_inj in H5. auto.
  subst bn.
  split; intro.
  assert (z = (tbool bm)).
  eapply eval_eq; eauto.
  subst z. auto.
  assert (z = (tbool bm)).
  eapply eval_eq; eauto.
  subst z. auto.

  simpl. intros.
  apply IHC. simpl.
  apply cat_respects; auto.
  apply PLT.pair_eq; auto.

  simpl; intros.
  apply IHC. simpl.
  apply cat_respects; auto.
  apply PLT.pair_eq; auto.
Qed.

Lemma normalizing : forall τ (m:term τ), exists z, eval τ m z.
Proof.
  intros.
  generalize (LRok τ m nil τ m tt tt (Logic.refl_equal _) (Logic.refl_equal _) I).
  simpl. intros [z [??]]. exists z; auto.
Qed.

Print Assumptions adequacy.
Print Assumptions normalizing.
