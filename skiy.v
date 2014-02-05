(* Copyright (c) 2014, Robert Dockins *)

Require Import String.
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
Require Import profinite_adj.
Require Import strict_utils.

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
                term (ty_bool ⇒ σ ⇒ σ ⇒ σ)

  | tY : forall σ₁ σ₂,
                term ( ((σ₁ ⇒ σ₂) ⇒ (σ₁ ⇒ σ₂)) ⇒ (σ₁ ⇒ σ₂)).

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
                  redex _ _ (tapp _ _ (tapp _ _ (tIF σ) (tbool false)) th) el el
  | redex_Y : forall σ₁ σ₂ (f:term ((σ₁ ⇒ σ₂) ⇒ (σ₁ ⇒ σ₂))) x,
                  redex _ _ (tapp _ _ (tY σ₁ σ₂) f) x
                            (tapp _ _ (tapp _ _ f (tapp _ _ (tY _ _) f)) x).


Inductive eval : forall τ, term τ -> term τ -> Prop :=
  | ebool : forall b, eval ty_bool (tbool b) (tbool b)
  | eI   : forall σ, eval _ (tI σ) (tI _)
  | eK   : forall σ₁ σ₂, eval _ (tK σ₁ σ₂) (tK _ _)
  | eS   : forall σ₁ σ₂ σ₃, eval _ (tS σ₁ σ₂ σ₃) (tS _ _ _)
  | eIF  : forall σ, eval _ (tIF σ) (tIF σ)
  | eY   : forall σ₁ σ₂, eval _ (tY σ₁ σ₂) (tY _ _)
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

Definition value σ (t:term σ) := eval _ t t.
Arguments value [σ] t.

Lemma eval_value τ x y :
  eval τ x y -> eval τ y y.
Proof.
  intro H. induction H.
  apply ebool.
  apply eI.
  apply eK.
  apply eS.
  apply eIF.
  apply eY.
  auto.
  apply eapp2; auto.
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

Lemma redex_eq τ₁ τ₂ x y z1 z2 :
  redex τ₁ τ₂ x y z1 ->
  redex τ₁ τ₂ x y z2 ->
  z1 = z2.
Proof.
  intros; inv H; inv H; inv H0; auto.
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

Lemma eval_no_redex : forall σ₁ σ₂ x x',
  eval σ₂ x x' ->
  forall m₁ m₂ n₁ n₂ r,
    x' = tapp σ₁ σ₂ m₁ m₂ ->
    eval _ m₁ n₁ -> eval _ m₂ n₂ -> redex _ _ n₁ n₂ r -> False.
Proof.
  do 5 intro. induction H; intros; try discriminate; subst.
  eapply IHeval3; eauto.
  inv H2.
  assert (m₂0 = n₂0).
  eapply eval_eq; eauto.
  apply eval_trans with m₂0; auto.
  assert (m₁0 = n₁0).
  eapply eval_eq; eauto.
  apply eval_trans with m₁0; auto.
  subst.
  apply H1. eauto.
Qed.

Inductive inert : forall σ₁ σ₂, term (σ₁ ⇒ σ₂) -> Prop :=
  | inert_K : forall σ₁ σ₂,
                  inert _ _ (tK σ₁ σ₂)
  | inert_S1 : forall σ₁ σ₂ σ₃,
                  inert _ _ (tS σ₁ σ₂ σ₃)
  | inert_S2 : forall σ₁ σ₂ σ₃ x,
                  inert _ _ (tapp _ _ (tS σ₁ σ₂ σ₃) x)
  | inert_IF1 : forall σ,
                  inert _ _ (tIF σ)
  | inert_IF2 : forall σ x,
                  inert _ _ (tapp _ _ (tIF σ) x)
  | inert_Y : forall σ₁ σ₂,
                  inert _ _ (tY σ₁ σ₂).

Lemma value_app_inv σ₁ σ₂ x y :
  value (tapp σ₁ σ₂ x y) ->
  value x /\ value y.
Proof.
  intros. inv H.
  elimtype False.
  eapply eval_no_redex.
  apply H8. reflexivity. eauto. eauto. eauto.
  split; auto.
Qed.  

Fixpoint tmsize τ (x:term τ) : nat :=
  match x with
  | tapp σ₁ σ₂ a b => 1 + tmsize _ a + tmsize _ b
  | _ => 1
  end.

Require Import Arith.
Require Import Omega.

Lemma redex_inert_false : forall σ₁ σ₂ f g r,
  redex σ₁ σ₂ f g r ->
  inert σ₁ σ₂ f ->
  False.
Proof.
  intros. inv H; inv H0.
Qed.

Lemma redex_or_inert' n : 
  forall τ (x:term τ) σ₁ σ₂ (f:term (σ₁ ⇒ σ₂))
    (Hτ : τ = σ₁ ⇒ σ₂)
    (Hx : eq_rect τ term x _ Hτ = f)
    (Hsz : tmsize τ x = n),
    value f ->
    (forall g, exists r, redex σ₁ σ₂ f g r) \/ inert σ₁ σ₂ f.
Proof.
  induction n using (well_founded_induction lt_wf).
  intros τ x. rename H into Hind.
  destruct x; intros; try discriminate.

  subst σ₂. simpl in *. subst n f.
  destruct (value_app_inv _ _ _ _ H).
  assert (Hx1:tmsize _ x1 < S (tmsize _ x1 + tmsize _ x2)).
  omega.
  generalize (Hind (tmsize _ x1) Hx1 _ _ _ _ x1
    (refl_equal _) (refl_equal _) (refl_equal _) H0).
  intros. destruct H2. 
  destruct (H2 x2).
  elimtype False. eapply eval_no_redex.
  apply H. reflexivity. apply H0. apply H1. eauto.
  inv H2. 
  left; intros. econstructor. econstructor.
  right. constructor.
  left; intros. econstructor. econstructor.
  right. constructor.
  inj_ty. subst x1.
  destruct (value_app_inv _ _ _ _ H0).
  inv H4.
  left; intros. destruct b.
  econstructor. econstructor.
  econstructor. econstructor.
  simpl in *.
  inv H13.
  elimtype False. eapply eval_no_redex.
  apply H13. reflexivity. eauto. eauto. eauto.
  assert (Hm₁ : tmsize _ m₁ <
         S (S (S (S (tmsize (σ₁ ⇒ ty_bool) m₁ + tmsize σ₁ m₂ + tmsize σ₂0 x2))))).
  omega.
  destruct (value_app_inv _ _ _ _ H4).
  generalize (Hind _ Hm₁ _ _ _ _ m₁ 
    (refl_equal _) (refl_equal _) (refl_equal _) H5).
  intros. destruct H11. destruct (H11 m₂).
  elimtype False. eapply eval_no_redex.
  apply H4. reflexivity. eauto. eauto. eauto.
  inv H11.
  inv H6.
  assert (Hm₁ : tmsize _ m₁ <
         S (S (S (S (tmsize (σ₁ ⇒ ty_bool) m₁ + tmsize σ₁ m₂ + tmsize σ₂0 x2))))).
  omega.
  destruct (value_app_inv _ _ _ _ H4).
  generalize (Hind _ Hm₁ _ _ _ _ m₁
    (refl_equal _) (refl_equal _) (refl_equal _) H5).
  intros. destruct H13. destruct (H13 m₂).
  elimtype False. eapply eval_no_redex.
  apply H4. reflexivity. eauto. eauto. eauto.
  inv H13.

  left; intros. econstructor. econstructor.

  inv Hτ.
  replace Hτ with (refl_equal (σ₂ ⇒ σ₂)). simpl.
  left; intros. econstructor. econstructor.
  apply Eqdep_dec.UIP_dec. decide equality.

  inv Hτ. 
  replace Hτ with (refl_equal (σ₁0 ⇒ σ₂ ⇒ σ₁0)). simpl.
  right. constructor.
  apply Eqdep_dec.UIP_dec. decide equality.
  
  inv Hτ.
  replace Hτ with (refl_equal ((σ₁ ⇒ σ₂ ⇒ σ₃) ⇒ (σ₁ ⇒ σ₂) ⇒ σ₁ ⇒ σ₃)).
  simpl.
  right. constructor.
  apply Eqdep_dec.UIP_dec. decide equality.

  inv Hτ.
  replace Hτ with (refl_equal (ty_bool ⇒ σ ⇒ σ ⇒ σ)).
  simpl.
  right. constructor.
  apply Eqdep_dec.UIP_dec. decide equality.

  inv Hτ.
  replace Hτ with (refl_equal (((σ₁ ⇒ σ₂) ⇒ σ₁ ⇒ σ₂) ⇒ σ₁ ⇒ σ₂)).
  simpl.
  right. constructor.
  apply Eqdep_dec.UIP_dec. decide equality.
Qed.

Lemma redex_or_inert : 
  forall σ₁ σ₂ (f:term (σ₁ ⇒ σ₂)),
    value f ->
    (forall g, exists r, redex σ₁ σ₂ f g r) \/ inert σ₁ σ₂ f.
Proof.
  intros. 
  apply (redex_or_inert' (tmsize _ f) _ f _ _ f (refl_equal _));
    simpl; auto.
Qed.

Require Import flat.

Fixpoint tydom (τ:ty) : ob ∂PLT :=
  match τ with
  | ty_bool => flat enumbool
  | ty_arrow τ₁ τ₂ => colift (PLT.exp (tydom τ₁) (tydom τ₂))
  end.

Section Ydefn.
  Variables σ₁ σ₂:ty.

  Definition Ybody
    : U (colift (tydom (σ₁ ⇒ σ₂) ⊸ tydom (σ₁ ⇒ σ₂)))
       → PLT.exp (U (tydom (σ₁ ⇒ σ₂))) (U (tydom (σ₁ ⇒ σ₂)))

       (*w : U (colift (tydom (σ₁ ⇒ σ₂) ⊸ tydom (σ₁ ⇒ σ₂))) *)
    := PLT.curry (*x:U (tydom (σ₁ ⇒ σ₂)))*) (strict_curry' (*y:U tydom σ₁ *)

                                                          (* w *)    (* x *)    (*y*)
        (strict_app' ∘ PLT.pair (strict_app' ∘ PLT.pair (pi1 ∘ pi1) (pi2 ∘ pi1)) pi2)
       ).

  Lemma Ybody_unroll : forall Γ 
    (f:Γ → U (tydom ((σ₁ ⇒ σ₂) ⇒ (σ₁ ⇒ σ₂))))
    (x:Γ → U (tydom σ₁)),

    semvalue x ->

    let Yf := (fixes _ _ Ybody) ∘ f in

    strict_app' ∘ PLT.pair Yf x ≈
    strict_app' ∘ PLT.pair (strict_app' ∘ PLT.pair f Yf) x.
  Proof.
    intros. unfold Yf at 1.
    rewrite fixes_unroll. unfold Ybody at 1.
    rewrite PLT.curry_apply2.
    rewrite <- (cat_assoc PLT).
    rewrite strict_curry_app2'.
    rewrite <- (cat_assoc PLT).
    rewrite (PLT.pair_compose_commute false).
    rewrite <- (cat_assoc PLT).
    rewrite (PLT.pair_compose_commute false).
    rewrite <- (cat_assoc PLT).
    rewrite pair_commute1.        
    rewrite pair_commute2.
    rewrite <- (cat_assoc PLT).
    rewrite pair_commute1.        
    rewrite (cat_assoc PLT _ _ _ _ pi1).
    rewrite pair_commute1.        
    rewrite (cat_assoc PLT _ _ _ _ pi2).
    rewrite pair_commute2.
    apply cat_respects. auto.
    apply PLT.pair_eq. 2: auto.
    rewrite (cat_ident2 PLT).    
    apply cat_respects. auto.
    apply PLT.pair_eq. auto.
    unfold Yf. auto.   
    auto.
  Qed.

  Definition Ysem Γ 
    : Γ → U (tydom (((σ₁ ⇒ σ₂) ⇒ (σ₁ ⇒ σ₂)) ⇒ (σ₁ ⇒ σ₂)))
    := strict_curry' (fixes _ _ Ybody ∘ pi2).
End Ydefn.



Fixpoint denote (τ:ty) (m:term τ) : PLT.unit false → U (tydom τ) :=
  match m with
  | tbool b => flat_elem' b
  | tapp σ₁ σ₂ m₁ m₂ => strict_app' ∘ PLT.pair (denote (σ₁ ⇒ σ₂) m₁) (denote σ₁ m₂)
  | tI σ => strict_curry' pi2
  | tK σ₁ σ₂ => strict_curry' (strict_curry' (pi2 ∘ pi1))
  | tS σ₁ σ₂ σ₃ => strict_curry' (strict_curry' (strict_curry' (
                     strict_app' ∘ PLT.pair
                       (strict_app' ∘ PLT.pair (pi2 ∘ pi1 ∘ pi1) pi2)
                       (strict_app' ∘ PLT.pair (pi2 ∘ pi1) pi2)
                      )))
  | tIF σ => strict_curry' (flat_cases' (fun b:bool =>
                if b then strict_curry' (strict_curry' (pi2 ∘ pi1))
                     else strict_curry' (strict_curry' pi2)
                ))
  | tY σ₁ σ₂ => Ysem σ₁ σ₂ (PLT.unit false)
  end.


Lemma canonical_bool : forall x,
  eval ty_bool x x -> 
  x = tbool true \/ x = tbool false.
Proof.
  intros. inv H.
  destruct b; auto.

  elimtype False.
  eapply eval_no_redex.
  apply H6. reflexivity. eauto. eauto. eauto.
  inv H1. clear H1.
  destruct (redex_or_inert _ _ m₁); auto.
  elim H5; apply H0.
  inv H0.
Qed.

Lemma flat_elem'_semvalue : forall (X:enumtype) Γ (x:X),
  @semvalue Γ (flat X) (flat_elem' x).
Proof.
  intros. intro a. exists x.
  unfold flat_elem'.
  apply (compose_hom_rel _ _ _ _ η (U@(flat_elem x ∘ PLT.terminate true (L Γ)))
    a (Some x)).
  exists (Some a).   split.
  simpl. apply adj_unit_rel_elem. auto.
  apply hom_rel_U.
  right. exists a. exists x. split; auto.
  apply (compose_hom_rel _ _ _ _ ).
  exists tt. split.
  simpl. apply eprod_elem. split.
  apply eff_complete. apply single_axiom; auto.
  simpl. apply single_axiom. auto.
Qed.

Lemma flat_elem_canon : forall (X:enumtype) (g:PLT.unit _ → U (flat X)),
  semvalue g -> exists x, g ≈ flat_elem' x.
Proof.
  intros. destruct (H tt).
  exists x. split; hnf; intros.
  unfold flat_elem'.
  destruct a.
  apply compose_hom_rel.
  exists (Some c). split.
  simpl. apply adj_unit_rel_elem. auto.
  apply hom_rel_U.
  destruct c0; auto.
  destruct c.
  right.
  exists tt. exists c0.
  split; auto.
  apply compose_hom_rel.
  exists tt. split.
  simpl. apply eprod_elem.
  split. apply eff_complete. apply single_axiom; auto.
  simpl. apply single_axiom.
  assert (c0 = x).
  destruct (PLT.hom_directed _ _ _ g tt (Some x::Some c0::nil)).
  hnf. auto.
  hnf; intros.
  apply cons_elem in H2. destruct H2. rewrite H2.
  apply erel_image_elem; auto.
  apply cons_elem in H2. destruct H2. rewrite H2.
  apply erel_image_elem; auto.
  apply nil_elem in H2. elim H2.
  destruct H2.  
  apply erel_image_elem in H3.
  assert (Some x ≤ x0). apply H2.
  apply cons_elem; auto.
  assert (Some c0 ≤ x0). apply H2.
  apply cons_elem; auto. right.
  apply cons_elem; auto.
  destruct x0. hnf in H4. hnf in H5. subst c; auto.
  elim H4.
  subst c0. auto.
  destruct a.

  unfold flat_elem' in H1.
  apply compose_hom_rel in H1.
  destruct H1 as [y [??]].
  simpl in H1. apply adj_unit_rel_elem in H1.
  apply hom_rel_U in H2.
  destruct c.
  destruct H2.
  subst c0.
  revert H0. apply (PLT.hom_order _ _ _ g). auto.
Transparent U. hnf. auto. Opaque U. 
  destruct H2 as [p [q [?[??]]]].
  subst y c0.
  destruct p.
  apply compose_hom_rel in H2.
  destruct H2 as [?[??]].
  simpl in H3.
  apply single_axiom in H3.
  destruct H3 as [[??][??]]. simpl in *.
  hnf in H6. subst q. auto.
Qed.

Lemma value_inert_semvalue : forall n,
  (forall σ x,
    tmsize _ x = n ->
    eval σ x x -> semvalue (denote _ x)) /\
  (forall σ₁ σ₂ x (y:PLT.unit _ → U (tydom σ₁)),
    tmsize _ x = n ->
    value x ->
    inert σ₁ σ₂ x ->
    semvalue y ->
    semvalue (strict_app' ∘ PLT.pair (denote _ x) y)).
Proof.
  intro n. induction n using (well_founded_induction lt_wf).

  split; intros. 
  inv H1; simpl.
  apply flat_elem'_semvalue.

  apply strict_curry'_semvalue.  
  apply strict_curry'_semvalue.  
  apply strict_curry'_semvalue.  
  apply strict_curry'_semvalue.  
  unfold Ysem. apply strict_curry'_semvalue.

  elimtype False.
  eapply eval_no_redex.
  apply H8. reflexivity. eauto. eauto. eauto.

  inv H3. clear H3.
  destruct (redex_or_inert _ _ m₁); auto.
  elim H7; auto.
  simpl in H.
  assert (Hm1 : (tmsize _ m₁) < S (tmsize _ m₁ + tmsize _ m₂)).
  omega.
  destruct (H _ Hm1).
  apply H3; auto.
  clear H2 H3.
  assert (Hm2 : (tmsize _ m₂) < S (tmsize _ m₁ + tmsize _ m₂)).
  omega.
  destruct (H _ Hm2).
  apply H2; auto.


  inv H2; simpl.

  rewrite strict_curry_app'; auto.
  apply strict_curry'_semvalue2.

  rewrite strict_curry_app'; auto.
  apply strict_curry'_semvalue2.

  rewrite strict_curry_app'; auto.
  rewrite strict_curry_app2'; auto.
  apply strict_curry'_semvalue2.
  destruct (value_app_inv _ _ _ _ H1); auto.
  simpl in H.
  assert (tmsize _ x0 < S (S (tmsize _ x0))). omega.
  destruct (H _ H5). apply (H6 _ x0); auto.

  rewrite strict_curry_app'; auto.
  destruct (flat_elem_canon enumbool y H3) as [b ?].
  rewrite H0.
  rewrite flat_cases_elem'. destruct b.
  apply strict_curry'_semvalue2.
  apply strict_curry'_semvalue2.

  rewrite strict_curry_app'; auto.
  destruct (value_app_inv _ _ _ _ H1); auto.
  destruct (canonical_bool x0); auto; subst x0; simpl.
  rewrite flat_cases_elem'.
  rewrite strict_curry_app2'; auto.
  apply strict_curry'_semvalue2.
  rewrite flat_cases_elem'.
  rewrite strict_curry_app2'; auto.
  apply strict_curry'_semvalue2.

  destruct (value_app_inv _ _ _ _ H1); auto.
  simpl in H.
  assert (tmsize _ x0 < S (S (tmsize _ x0))). omega.
  destruct (H _ H5). apply (H6 _ x0); auto.
  
  unfold Ysem.
  rewrite strict_curry_app'; auto.
  rewrite (fixes_unroll _ _ (Ybody σ₁0 σ₂0)).
  unfold Ybody at 1.
  rewrite PLT.curry_apply2.
  rewrite <- (cat_assoc PLT).
  rewrite <- (cat_assoc PLT).
  apply strict_curry'_semvalue2.
Qed.

Lemma value_semvalue : forall σ x,
  value x -> semvalue (denote σ x).
Proof.
  intros. destruct (value_inert_semvalue (tmsize _ x)); auto.
Qed.

Lemma inert_semvalue σ₁ σ₂ x y :    
  value x -> inert σ₁ σ₂ x -> semvalue y ->
  semvalue (strict_app' ∘ PLT.pair (denote _ x) y).
Proof.
  intros.
  destruct (value_inert_semvalue (tmsize _ x)).
  apply H3; auto.
Qed.

Hint Resolve value_semvalue.

Lemma redex_soundness : forall σ₁ σ₂ x y z,
  value x ->
  value y ->
  redex σ₁ σ₂ x y z ->
  strict_app' ∘ PLT.pair (denote _ x) (denote _ y) ≈ denote _ z.
Proof.
  intros. inv H1.

  inv H1. simpl.
  rewrite strict_curry_app'; auto.
  rewrite pair_commute2. auto.
  
  simpl.
  rewrite strict_curry_app'; auto.
  rewrite strict_curry_app2'; auto.
  rewrite <- (cat_assoc PLT).
  rewrite pair_commute1.
  rewrite pair_commute2. auto.
  destruct (value_app_inv _ _ _ _ H); auto.
  
  destruct (value_app_inv _ _ _ _ H).
  destruct (value_app_inv _ _ _ _ H2). clear H4.
  simpl.
  rewrite strict_curry_app'; auto.
  rewrite strict_curry_app2'; auto.
  rewrite strict_curry_app2'; auto.
  repeat rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  repeat rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  repeat rewrite <- (cat_assoc PLT).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  rewrite (PLT.pair_compose_commute false).
  repeat rewrite <- (cat_assoc PLT).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2.
  auto.
  apply (value_semvalue _ g); auto.
  apply (value_semvalue _ f); auto.
  
  destruct (value_app_inv _ _ _ _ H). clear H2.
  simpl.
  rewrite strict_curry_app'; auto.
  rewrite flat_cases_elem'.
  rewrite strict_curry_app2'; auto.
  rewrite strict_curry_app2'; auto.
  repeat rewrite <- (cat_assoc PLT).
  repeat rewrite pair_commute1.
  repeat rewrite pair_commute2. auto.
  apply flat_elem'_semvalue.
  
  destruct (value_app_inv _ _ _ _ H). clear H2.
  inv H1.
  simpl.
  rewrite strict_curry_app'; auto.
  rewrite flat_cases_elem'.
  rewrite strict_curry_app2'; auto.
  rewrite strict_curry_app2'; auto.
  repeat rewrite pair_commute2. auto.
  apply flat_elem'_semvalue.

  destruct (value_app_inv _ _ _ _ H). clear H1 H2.
  simpl.    
  unfold Ysem.
  rewrite strict_curry_app'; auto.
  rewrite fixes_unroll at 1. unfold Ybody at 1.
  rewrite PLT.curry_apply2.
  rewrite <- (cat_assoc PLT).
  rewrite pair_commute2.
  rewrite <- (cat_assoc PLT).
  rewrite strict_curry_app2'; auto.
  rewrite <- (cat_assoc PLT).
  apply cat_respects. auto.
  rewrite (PLT.pair_compose_commute false).
  rewrite pair_commute2.
  apply PLT.pair_eq. 2: auto.
  rewrite <- (cat_assoc PLT).
  apply cat_respects. auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq.
  rewrite <- (cat_assoc PLT).
  rewrite pair_commute1.
  rewrite (cat_assoc PLT).
  rewrite pair_commute1.
  apply cat_ident2.
  rewrite <- (cat_assoc PLT).
  rewrite pair_commute1.
  rewrite (cat_assoc PLT).
  rewrite pair_commute2.
  rewrite <- (cat_assoc PLT).
  rewrite pair_commute2.
  auto.
  apply (value_semvalue _ f). auto.
Qed.

Lemma soundness : forall τ (m z:term τ),
  eval τ m z -> denote τ m ≈ denote τ z.
Proof.
  intros. induction H; simpl; auto.
  rewrite IHeval1.
  rewrite IHeval2.
  rewrite <- IHeval3.
  apply redex_soundness.
  eapply eval_value; eauto.
  eapply eval_value; eauto.
  auto.
  rewrite IHeval1.
  rewrite IHeval2.
  auto.
Qed.

(****************************************** OK to here *********)

(*
Lemma exp_le_extensional (Γ:PLT) τ₁ τ₂ (f f': Γ → (PLT.exp τ₁ τ₂)) :
  (forall (x:Γ → τ₁), PLT.app ∘ PLT.pair f x ≤ PLT.app ∘ PLT.pair f' x) ->
  f ≤ f'.
Proof.
  intros. repeat intro.
  destruct a as [G r].
  assert (forall x y, (x,y) ∈ (proj1_sig r) -> 
    exists r', (G, r') ∈ PLT.hom_rel f' /\ ((r',x),y) ∈ PLT.hom_rel PLT.app).
  intros.
  assert ((G,y) ∈ PLT.hom_rel (PLT.app ∘ PLT.pair f (plt_const false Γ τ₁ x))).
  apply compose_hom_rel.
  exists (r,x).
  split.
  apply pair_rel_elem.
  split; auto.
  simpl. apply plt_const_rel_elem. auto.
  simpl. apply apply_rel_elem.
  exists x. exists y. split; auto.
  apply H in H2.
  apply compose_hom_rel in H2.
  destruct H2 as [[r' x'] [??]].
  simpl in H2.
  rewrite (pair_rel_elem _ _ _ _ _ _ G r' x') in H2.
  destruct H2. exists r'. split; auto.
  apply plt_const_rel_elem in H4.
  revert H3. apply PLT.hom_order; auto.
  split; auto.

  assert (forall x y, (x,y) ∈ (proj1_sig r) -> 
    exists r', (G, r') ∈ PLT.hom_rel f' /\ 
      exists x', exists y', (x', y') ∈ proj1_sig r' /\ x' ≤ x /\ y ≤ y').
  intros.
  destruct (H1 x y) as [r' [??]]; auto. exists r'; split; auto.
  simpl in H4. 
  rewrite (apply_rel_elem _ _ _ _ _ _ x y r') in H4.
  auto. clear H1.
Admitted. (* seems OK *)  

Lemma exp_le_extensional' (Γ:∂PLT) τ₁ τ₂ (f f': Γ → (PLT.exp τ₁ τ₂)) :
  (forall (x:Γ → τ₁), PLT.app ∘ PLT.pair f x ≤ PLT.app ∘ PLT.pair f' x) ->
  f ≤ f'.
Admitted.
*)



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

(*
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
*)

Fixpoint LR (τ:ty) : 
  term τ -> (PLT.unit false → U (tydom τ)) -> Prop :=
  match τ as τ' return 
    term τ' -> (PLT.unit false → U (tydom τ')) -> Prop
  with
  | ty_bool => fun m h => exists b:bool,
        m = tbool b /\ h ≈ flat_elem' b
  | ty_arrow σ₁ σ₂ => fun m h =>
        forall n h', LR σ₁ n h' -> value n -> semvalue h' ->
          semvalue (strict_app' ∘ PLT.pair h h') ->
          exists z,
            eval _ (tapp σ₁ σ₂ m n) z /\
            LR σ₂ z (strict_app' ∘ PLT.pair h h')
  end.

Lemma LR_equiv τ : forall m h h',
  h ≈ h' -> LR τ m h -> LR τ m h'.
Proof.
  induction τ; simpl. intros.
  destruct H0 as [b [??]]. exists b; split; auto.
  rewrite <- H; auto.
  simpl; intros.
  destruct (H0 n h'0 H1 H2 H3) as [z [??]]; auto.
  revert H4. apply semvalue_equiv.
  apply cat_respects; auto.
  apply PLT.pair_eq; auto.
  exists z.
  split; auto.
  revert H6. apply IHτ2.
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
  | t::ts' => prod (lrsem ts') (PLT.unit false → U (tydom t))
  end.

Fixpoint lrhyps (ls:list ty) : lrsyn ls -> lrsem ls -> Prop :=
  match ls with
  | nil => fun _ _ => True
  | t::ts => fun xs ys =>
    (eval _ (snd xs) (snd xs) /\ semvalue (snd ys)) /\
    LR t (snd xs) (snd ys) /\ lrhyps ts (fst xs) (fst ys)
  end.

Fixpoint lrapp (ls:list ty) z : lrsyn ls -> term (lrtys ls z) -> term z :=
  match ls as ls' return lrsyn ls' -> term (lrtys ls' z) -> term z with
  | nil => fun _ m => m
  | t::ts => fun xs m => lrapp ts _ (fst xs) (tapp _ _ m (snd xs))
  end.

Fixpoint lrsemapp (ls:list ty) z :
  lrsem ls -> (PLT.unit false → U (tydom (lrtys ls z))) 
  -> (PLT.unit false → U (tydom z)) :=
  match ls as ls' return
    lrsem ls' ->
    (PLT.unit false → U (tydom (lrtys ls' z))) 
    -> (PLT.unit false → U (tydom z))
  with
  | nil => fun _ h => h
  | t::ts => fun ys h => lrsemapp ts _ (fst ys) (strict_app' ∘ PLT.pair h (snd ys))
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

Lemma semvalue_lrsemapp_out ls : forall τ ys h,
   semvalue (lrsemapp ls τ ys h) -> semvalue h.
Proof.
  induction ls; simpl; intros; auto.
  apply IHls in H.
  apply semvalue_app_out1' in H. auto.
Qed.

Lemma LR_under_apply ls :
   forall (τ : ty) (m z0 : term (lrtys ls τ)) (xs : lrsyn ls) 
     (ys : lrsem ls) (h : PLT.unit false → U (tydom (lrtys ls τ))),
   eval (lrtys ls τ) m z0 ->
   lrhyps ls xs ys ->
   semvalue (lrsemapp ls τ ys h) ->
   LR (lrtys ls τ) z0 h ->
   exists z : term τ,
     eval τ (lrapp ls τ xs m) z /\ LR τ z (lrsemapp ls τ ys h).
Proof.
  induction ls; simpl; intros.
  exists z0. split; auto.
  destruct xs as [xs x].
  destruct ys as [ys y]. simpl in *.
  destruct H0 as [[??][??]].
  destruct (H2 x y) as [z1 [??]]; auto.
  apply semvalue_lrsemapp_out in H1. auto.

  generalize (IHls τ (tapp z0 x) z1 xs ys (strict_app' ∘ PLT.pair h y)
     H6 H5 H1 H7).
  intros [q [??]].
  exists q; split; auto.
  revert H8.
  apply eval_lrapp_congruence. intro.
  apply eval_app_congruence; auto.
  fold lrtys. intros.
  apply eval_trans with z0; auto.
Qed.

Lemma LR_I σ : LR _ (tI σ) (denote _ (tI σ)).
Proof.
  simpl. intros.
  exists n. split.
  eapply eapp1.
  apply eI. apply H0.
  apply redex_I. auto.
  revert H. apply LR_equiv. rewrite strict_curry_app'.
  rewrite pair_commute2; auto. auto.
Qed.

Lemma LR_K σ₁ σ₂ : LR _ (tK σ₁ σ₂) (denote _ (tK σ₁ σ₂)).
Proof.
  simpl. intros.

  exists (tapp (tK _ _) n). split.
  apply eapp2. apply eK. auto.
  intros [? Hr]. inv Hr.
  intros.
  exists n. split.
  eapply eapp1. 
  apply eapp2. apply eK. eauto.
  intros [? Hr]. inv Hr. eauto.
  apply redex_K. auto.
  revert H.
  apply LR_equiv.
  rewrite strict_curry_app'.
  rewrite strict_curry_app2'.
  rewrite <- (cat_assoc PLT).
  rewrite pair_commute1.
  rewrite pair_commute2.
  auto. auto. auto.
Qed.

Lemma LR_S σ₁ σ₂ σ₃ : LR _ (tS σ₁ σ₂ σ₃) (denote _ (tS σ₁ σ₂ σ₃)).
Proof.
  simpl; intros.
  exists (tapp (tS _ _ _) n). split.
  apply eapp2. apply eS. auto.
  intros [? Hr]; inversion Hr.
  intros.
  exists (tapp (tapp (tS _ _ _) n) n0). split.
  apply eapp2. apply eapp2. apply eS. auto.
  intros [? Hr]; inversion Hr. auto.
  intros [? Hr]; inversion Hr. intros.

  assert ( (strict_app'
           ∘ PLT.pair
               (strict_app'
                ∘ PLT.pair
                    (strict_app'
                     ∘ PLT.pair
                         (strict_curry'
                            (strict_curry'
                               (strict_curry'
                                  (strict_app'
                                   ∘ PLT.pair
                                       (strict_app'
                                        ∘ PLT.pair (pi2 ∘ pi1 ∘ pi1) pi2)
                                       (strict_app'
                                        ∘ PLT.pair (pi2 ∘ pi1) pi2))))) h')
                    h'0) h'1)
     ≈
     strict_app' ∘ PLT.pair
       (strict_app' ∘ PLT.pair h' h'1)
       (strict_app' ∘ PLT.pair h'0 h'1)).
  clear -H9 H5 H1.

  rewrite strict_curry_app'; auto.
  rewrite strict_curry_app2'; auto.
  rewrite strict_curry_app2'; auto.
  rewrite <- (cat_assoc PLT).
  apply cat_respects. auto.
  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq.
  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  apply cat_respects. auto.
  apply PLT.pair_eq.
  rewrite <- (cat_assoc PLT).
  rewrite <- (cat_assoc PLT).
  rewrite pair_commute1.
  rewrite pair_commute1.
  rewrite pair_commute2.
  auto.
  rewrite pair_commute2.
  auto.
  rewrite <- (cat_assoc PLT).
  apply cat_respects; auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq; auto.
  rewrite <- (cat_assoc PLT).
  rewrite pair_commute1.
  rewrite pair_commute2.
  auto.
  rewrite pair_commute2.
  auto.

  rewrite H11 in H10.

  destruct (H3 n1 h'1) as [z0 [??]]; auto; clear H3.
  apply semvalue_app_out2' in H10. auto.
  
  destruct (H n1 h'1) as [z1 [??]]; auto; clear H.
  apply semvalue_app_out1' in H10. auto.
  
  destruct (H14 z0 (strict_app' ∘ PLT.pair h'0 h'1)) as [z2 [??]]; auto; clear H14.
  eapply eval_value; eauto.
  apply semvalue_app_out2' in H10. auto.
  exists z2. split.
  eapply eapp1. 
  apply eapp2. apply eapp2. apply eS. eauto.
  intros [? Hr]; inv Hr. eauto.
  intros [? Hr]; inv Hr. eauto.
  apply redex_S.
  revert H.
  apply eval_app_congruence.
  intros. apply eval_trans with z1; auto.
  intros. apply eval_trans with z0; auto.
  revert H15. apply LR_equiv. auto.
Qed.

Lemma LR_IF σ : LR _ (tIF σ) (denote _ (tIF σ)).
Proof.
  simpl. intros.
  exists (tapp (tIF σ) n). split. apply eapp2.
  apply eIF. auto.
  intros [? Hr]. inv Hr.
  intros.
  exists (tapp (tapp (tIF σ) n) n0). split. apply eapp2. apply eapp2.
  apply eIF. auto.
  intros [? Hr]. inv Hr. auto.
  intros [? Hr]. inv Hr.
  intros.
  destruct H as [b [??]]. subst n.
  destruct b.
  exists n0. split.
  eapply eapp1. apply eapp2. apply eapp2.
  apply eIF. apply ebool.
  intros [? Hr]. inv Hr. eauto.
  intros [? Hr]. inv Hr. eauto.
  econstructor. auto.
  revert H3. apply LR_equiv.
  rewrite H11.
  rewrite strict_curry_app'; auto.
  rewrite flat_cases_elem'.
  rewrite strict_curry_app2'; auto.
  rewrite strict_curry_app2'; auto.
  rewrite <- (cat_assoc PLT).
  rewrite pair_commute1.
  rewrite pair_commute2. auto.
  apply flat_elem'_semvalue.  
  exists n1.
  split.
  eapply eapp1. apply eapp2. apply eapp2.
  apply eIF. apply ebool.
  intros [? Hr]. inv Hr. eauto.
  intros [? Hr]. inv Hr. eauto.
  econstructor. auto.
  revert H7. apply LR_equiv.
  rewrite H11.
  rewrite strict_curry_app'; auto.
  rewrite flat_cases_elem'.
  rewrite strict_curry_app2'; auto.
  rewrite strict_curry_app2'; auto.
  rewrite pair_commute2. auto.
  apply flat_elem'_semvalue.  
Qed.

Lemma LR_Y σ₁ σ₂ : LR _ (tY σ₁ σ₂) (denote _ (tY σ₁ σ₂)).
Admitted.

Lemma fundamental_lemma : forall σ (n:term σ) ls τ m xs ys
  (Hσ : σ = lrtys ls τ),
  eq_rect σ term n (lrtys ls τ) Hσ = m ->
  lrhyps ls xs ys ->
  semvalue (lrsemapp ls τ ys (denote _ m)) ->
  exists z,
    eval _ (lrapp ls τ xs m) z /\
    LR τ z (lrsemapp ls τ ys (denote _ m)).
Proof.
  induction n; intros.

  (* bool case *)
  destruct ls; simpl in *. subst τ.
  simpl in H. subst m.
  exists (tbool b).
  split. apply ebool.
  simpl.
  exists b. split; auto.
  inv Hσ.

  (* application case *)
  subst σ₂. simpl in H. subst m.

  destruct (IHn2 nil σ₁ n2 tt tt (Logic.refl_equal _) (Logic.refl_equal _) I)
    as [q2[??]]; auto.
  simpl.
  apply semvalue_lrsemapp_out in H1. simpl in H1.
  apply semvalue_app_out2' in H1. auto.

  destruct (IHn1 (σ₁::ls) _ n1 (xs, q2) (ys, denote σ₁ q2)
    (Logic.refl_equal _) (Logic.refl_equal _)) as [q1 [??]].
  simpl; intuition. eapply eval_value; eauto.
  apply value_semvalue; auto.  eapply eval_value; eauto.
  revert H2. apply LR_equiv.
  simpl. simpl in H. apply soundness; auto.
  simpl. revert H1.
  apply semvalue_equiv.
  apply lrsemapp_equiv.
  simpl. apply cat_respects; auto.
  apply PLT.pair_eq; auto.
  apply soundness; auto.
  exists q1. split.
  revert H3.
  simpl. apply eval_lrapp_congruence.
  intro q. apply eval_app_congruence; intros; auto.
  apply eval_trans with q2; auto.
  revert H4.
  apply LR_equiv. simpl.
  apply lrsemapp_equiv.
  simpl. apply cat_respects; auto.
  apply PLT.pair_eq; auto.
  symmetry.
  apply soundness; auto.
  
  (* I case *)
  
  cut (exists z : term (σ ⇒ σ),
     eval (σ ⇒ σ) (tI σ) z /\ LR (σ ⇒ σ) z (denote _ (tI _))).
  revert H.
  generalize (tI σ).
  generalize Hσ.
  rewrite Hσ. intro H.
  replace H with (refl_equal (lrtys ls τ)). simpl. intros.
  subst t. clear H Hσ. 
  destruct H3 as [z0 [??]].
  eapply LR_under_apply; eauto.
  apply Eqdep_dec.UIP_dec. decide equality.

  exists (tI σ). split. apply eI.
  apply LR_I.

  (* K case *)
  cut (exists z,
     eval _ (tK σ₁ σ₂) z /\ LR _ z (denote _ (tK _ _))).
  revert H.
  generalize (tK σ₁ σ₂).
  generalize Hσ.
  rewrite Hσ. intro H.
  replace H with (refl_equal (lrtys ls τ)). simpl. intros.
  subst t. clear H Hσ. 
  destruct H3 as [z0 [??]].
  eapply LR_under_apply; eauto.
  apply Eqdep_dec.UIP_dec. decide equality.

  exists (tK _ _). split. apply eK.
  apply LR_K.

  (* S case *)
  cut (exists z,
     eval _ (tS σ₁ σ₂ σ₃) z /\ LR _ z (denote _ (tS _ _ _))).
  revert H.
  generalize (tS σ₁ σ₂ σ₃).
  generalize Hσ.
  rewrite Hσ. intro H.
  replace H with (refl_equal (lrtys ls τ)). simpl. intros.
  subst t. clear H Hσ. 
  destruct H3 as [z0 [??]].
  eapply LR_under_apply; eauto.
  apply Eqdep_dec.UIP_dec. decide equality.

  exists (tS _ _ _).
  split. simpl. apply eS.
  apply LR_S.

  (* IF case *)
  cut (exists z,
     eval _ (tIF σ) z /\ LR _ z (denote _ (tIF _))).
  revert H.
  generalize (tIF σ).
  generalize Hσ.
  rewrite Hσ. intro H.
  replace H with (refl_equal (lrtys ls τ)). simpl. intros.
  subst t. clear H Hσ. 
  destruct H3 as [z0 [??]].
  eapply LR_under_apply; eauto.
  apply Eqdep_dec.UIP_dec. decide equality.

  exists (tIF σ). split. apply eIF.
  apply LR_IF.

  (* Y case *)
  cut (exists z,
     eval _ (tY σ₁ σ₂) z /\ LR _ z (denote _ (tY σ₁ σ₂))).
  revert H.
  generalize (tY σ₁ σ₂).
  generalize Hσ.
  rewrite Hσ. intro H.
  replace H with (refl_equal (lrtys ls τ)). simpl. intros.
  subst t. clear H Hσ. 
  destruct H3 as [z0 [??]].
  eapply LR_under_apply; eauto.
  apply Eqdep_dec.UIP_dec. decide equality.

  exists (tY σ₁ σ₂). split. apply eY.
  apply LR_Y.
Qed.

Lemma fundamental_lemma' : forall τ m,
  semvalue (denote τ m) ->
  exists z, eval τ m z /\ LR τ z (denote τ m).
Proof.
  intros.
  apply (fundamental_lemma τ m nil τ m tt tt (refl_equal _) (refl_equal _) I).
  simpl. auto.
Qed.

Lemma flat_elem'_inj (X:enumtype) (x x':X) :
  @flat_elem' X (PLT.unit _) x ≈ flat_elem' x' -> x = x'.
Proof.
  intros.
  unfold flat_elem' in H.
  assert ((tt, Some x) ∈ PLT.hom_rel (U@(flat_elem x ∘ PLT.terminate true (L (PLT.unit false))) ∘ η)).
  rewrite (compose_hom_rel _ _ _ _ η 
    (U@(flat_elem x ∘ PLT.terminate true (L (PLT.unit false))))).
  exists (Some tt). split.
  simpl. apply adj_unit_rel_elem. auto.
  apply hom_rel_U.
  right. exists tt. exists x. split; auto.
  rewrite (compose_hom_rel _ _ _ _ (PLT.terminate true (L (PLT.unit false)))
    (flat_elem x)).
  exists tt. split.
  simpl. apply eprod_elem. split. apply eff_complete.
  apply single_axiom. auto.
  simpl. apply single_axiom. auto.
  destruct H.
  apply H in H0.
  rewrite (compose_hom_rel _ _ _ _ η 
    (U@(flat_elem x' ∘ PLT.terminate true (L (PLT.unit false))))) in H0.
  destruct H0 as [y[??]].
  simpl in H0. apply adj_unit_rel_elem in H0.
  apply (hom_rel_U _ _ 
    (flat_elem x' ∘ PLT.terminate true (L (PLT.unit false)))) in H2.
  destruct H2. discriminate.
  destruct H2 as [p [q [?[??]]]]. subst y. inv H4.
  rewrite (compose_hom_rel _ _ _ _ (PLT.terminate true (L (PLT.unit false)))
    (flat_elem x')) in H2.
  destruct H2 as [?[??]].
  simpl in H3.
  apply single_axiom in H3.
  destruct H3 as [[??][??]]. simpl in *.
  hnf in H5. auto.
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
  split; intros.
  destruct (fundamental_lemma' _ m) as [zm [??]].
  simpl.
  apply semvalue_equiv with (denote _ z).
  symmetry. apply soundness. auto.
  apply value_semvalue. eapply eval_value; eauto.
  destruct (fundamental_lemma' _ n) as [zn [??]].
  simpl.
  apply semvalue_equiv with (denote _ z).
  symmetry. rewrite <- H.
  apply soundness. auto.
  apply value_semvalue. eapply eval_value; eauto.
  destruct H2 as [b [??]].
  destruct H4 as [b' [??]].
  simpl in *.
  rewrite H in H5. rewrite H5 in H6.
  assert (b = b').
  apply flat_elem'_inj in H6. auto.
  subst b'.
  subst zm zn.
  assert (z = (tbool b)).
  eapply eval_eq; eauto.
  subst z. auto.

  destruct (fundamental_lemma' _ m) as [zm [??]].
  simpl.
  apply semvalue_equiv with (denote _ z).
  symmetry. rewrite H. apply soundness. auto.
  apply value_semvalue. eapply eval_value; eauto.
  destruct (fundamental_lemma' _ n) as [zn [??]].
  simpl.
  apply semvalue_equiv with (denote _ z).
  symmetry. apply soundness. auto.
  apply value_semvalue. eapply eval_value; eauto.
  destruct H2 as [b [??]].
  destruct H4 as [b' [??]].
  simpl in *.
  rewrite H in H5. rewrite H5 in H6.
  assert (b = b').
  apply flat_elem'_inj in H6. auto.
  subst b'.
  subst zm zn.
  assert (z = (tbool b)).
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

Lemma denote_bottom_nonvalue : forall τ (m:term τ),
  (~exists z, eval τ m z) <-> denote τ m ≈ ⊥.
Proof.
  intros. split; intro.

  split. 2: apply bottom_least.
  hnf. intros [u x] Hx. destruct x.
  elimtype False.
  destruct (fundamental_lemma' τ m) as [z [??]].
  red; intros. destruct g. simpl.
  exists c. auto.
  elim H. eauto.
  apply compose_hom_rel.    
  simpl. exists None.
  split.
  apply adj_unit_rel_elem. hnf; auto.
  apply hom_rel_U. auto.

  intros [z ?].
  assert (denote τ z ≈ ⊥).
  rewrite <- soundness; eauto.
  assert (value z).
  eapply eval_value; eauto.
  apply value_semvalue in H2.
  hnf in H2.
  destruct (H2 tt) as [x ?].
  destruct H1. apply H1 in H3.
  simpl bottom in H3.
  apply (compose_hom_rel) in H3.
  destruct H3 as [q [??]].
  apply hom_rel_U in H5.
  destruct H5.
  inversion H5.
  destruct H5 as [q' [?[??]]].
  simpl in H5.
  apply union_axiom in H5.
  destruct H5 as [?[??]].
  apply image_axiom2 in H5. destruct H5 as [? [??]].
  apply empty_elem in H5. elim H5.
Qed.   

Print Assumptions adequacy.
Print Assumptions denote_bottom_nonvalue.
