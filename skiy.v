(* Copyright (c) 2014, Robert Dockins *)

Require Import String.
Require Import List.
Require Import Arith.
Require Import Omega.


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
Require Import fixes.
Require Import flat.


Inductive ty :=
  | ty_bool
  | ty_arrow : ty -> ty -> ty.

Delimit Scope ty_scope with ty.
Notation "2" := ty_bool : ty_scope.
Notation "x ⇒ y" := (ty_arrow (x)%ty (y)%ty) : ty_scope.
Bind Scope ty_scope with ty.

Delimit Scope ski_scope with ski.
Open Scope ski_scope.

Inductive term : ty -> Type :=
  | tbool : forall b:bool,
                term 2

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
                term ( ((σ₁ ⇒ σ₂) ⇒ (σ₁ ⇒ σ₂)) ⇒ (σ₁ ⇒ σ₂) ).

Arguments tapp [_ _] _ _.
Notation "x • y" := (tapp x y) 
  (at level 52, left associativity, format "x • y") : ski_scope.

Inductive redex : forall σ₁ σ₂, term (σ₁ ⇒ σ₂) -> term σ₁ -> term σ₂ -> Prop :=
  | redex_I : forall σ x,
                  redex _ _ (tI σ) x x
  | redex_K : forall σ₁ σ₂ x y,
                  redex σ₂ σ₁ (tK σ₁ σ₂ • y) x y
  | redex_S : forall σ₁ σ₂ σ₃ f g x,
                  redex _ _ (tS σ₁ σ₂ σ₃ • f • g)
                            x
                            ((f•x)•(g•x))
  | redex_IFtrue : forall σ th el,
                  redex _ _ (tIF σ • tbool true • th) el th
  | redex_IFfalse : forall σ th el,
                  redex _ _ (tIF σ • tbool false • th) el el

  | redex_Y : forall σ₁ σ₂ (f:term ((σ₁ ⇒ σ₂) ⇒ (σ₁ ⇒ σ₂))) x,
                  redex _ _ (tY σ₁ σ₂ • f) x
                            (f•(tY σ₁ σ₂ • f)•x).

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
             eval σ₂ (m₁ • m₂) z
  | eapp2 : forall σ₁ σ₂ m₁ m₂ n₁ n₂,
             eval (σ₁ ⇒ σ₂) m₁ n₁ ->
             eval σ₁ m₂ n₂ ->
             ~(exists r, redex σ₁ σ₂ n₁ n₂ r) ->
             eval σ₂ (m₁ • m₂) (n₁ • n₂).

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
  eval _ (@tapp σ₁ σ₂ x y) z ->
  exists x', exists y',
    eval _ x x' /\ eval _ y y' /\
    eval _ (x' • y') z.
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
    x' = @tapp σ₁ σ₂ m₁ m₂ ->
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
                  inert _ _ (tS σ₁ σ₂ σ₃ • x)
  | inert_IF1 : forall σ,
                  inert _ _ (tIF σ)
  | inert_IF2 : forall σ x,
                  inert _ _ (tIF σ • x)
  | inert_Y : forall σ₁ σ₂,
                  inert _ _ (tY σ₁ σ₂).

Lemma value_app_inv σ₁ σ₂ x y :
  value (@tapp σ₁ σ₂ x y) ->
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
  | tapp σ₁ σ₂ a b => (1 + tmsize _ a + tmsize _ b)%nat
  | _ => 1%nat
  end.


Lemma redex_inert_false : forall σ₁ σ₂ f g r,
  redex σ₁ σ₂ f g r ->
  inert σ₁ σ₂ f ->
  False.
Proof.
  intros. inv H; inv H0.
Qed.

Lemma redex_or_inert' n : 
  forall τ (x:term τ) σ₁ σ₂ (f:term (σ₁ ⇒ σ₂))
    (Hτ : τ = (σ₁ ⇒ σ₂)%ty)
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
  replace Hτ with (refl_equal (σ₂ ⇒ σ₂)%ty). simpl.
  left; intros. econstructor. econstructor.
  apply Eqdep_dec.UIP_dec. decide equality.

  inv Hτ. 
  replace Hτ with (refl_equal (σ₁0 ⇒ σ₂ ⇒ σ₁0)%ty). simpl.
  right. constructor.
  apply Eqdep_dec.UIP_dec. decide equality.
  
  inv Hτ.
  replace Hτ with (refl_equal ((σ₁ ⇒ σ₂ ⇒ σ₃) ⇒ (σ₁ ⇒ σ₂) ⇒ σ₁ ⇒ σ₃)%ty).
  simpl.
  right. constructor.
  apply Eqdep_dec.UIP_dec. decide equality.

  inv Hτ.
  replace Hτ with (refl_equal (ty_bool ⇒ σ ⇒ σ ⇒ σ)%ty).
  simpl.
  right. constructor.
  apply Eqdep_dec.UIP_dec. decide equality.

  inv Hτ.
  replace Hτ with (refl_equal (((σ₁ ⇒ σ₂) ⇒ σ₁ ⇒ σ₂) ⇒ σ₁ ⇒ σ₂)%ty).
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


Fixpoint tydom (τ:ty) : ∂PLT :=
  match τ with
  | ty_bool => flat enumbool
  | ty_arrow τ₁ τ₂ => colift (tydom τ₁ ⊸ tydom τ₂)
  end.

Section Ydefn.
  Variables σ₁ σ₂:ty.

  Definition Ybody
    : U (colift (tydom (σ₁ ⇒ σ₂) ⊸ tydom (σ₁ ⇒ σ₂)))
       → PLT.exp (U (tydom (σ₁ ⇒ σ₂))) (U (tydom (σ₁ ⇒ σ₂)))

       (*w : U (colift (tydom (σ₁ ⇒ σ₂) ⊸ tydom (σ₁ ⇒ σ₂))) *)
    := PLT.curry (*x:U (tydom (σ₁ ⇒ σ₂)))*) (strict_curry' (*y:U tydom σ₁ *)

                                                          (* w *)    (* x *)    (*y*)
        (strict_app' ∘ 〈strict_app' ∘ 〈π₁ ∘ π₁, π₂ ∘ π₁〉, π₂〉)
       ).

  Lemma Ybody_unroll : forall Γ 
    (f:Γ → U (tydom ((σ₁ ⇒ σ₂) ⇒ (σ₁ ⇒ σ₂))))
    (x:Γ → U (tydom σ₁)),

    semvalue x ->

    let Yf := (fixes _ _ Ybody) ∘ f in

    strict_app' ∘ 〈Yf, x〉 ≈
    strict_app' ∘ 〈strict_app' ∘ 〈f,Yf〉 , x〉.
  Proof.
    intros. unfold Yf at 1.
    rewrite fixes_unroll. unfold Ybody at 1.
    rewrite PLT.curry_apply2.
    rewrite <- (cat_assoc PLT).
    rewrite strict_curry_app2'.
    rewrite (PLT.pair_compose_commute false).
    rewrite <- (cat_assoc PLT).
    apply cat_respects. auto.
    rewrite (PLT.pair_compose_commute false).
    rewrite <- (cat_assoc PLT).
    rewrite (PLT.pair_compose_commute false).
    rewrite <- (cat_assoc PLT).
    rewrite PLT.pair_commute1.        
    rewrite PLT.pair_commute2.
    rewrite PLT.pair_commute1.        
    rewrite <- (cat_assoc PLT).
    rewrite PLT.pair_commute1.        
    rewrite PLT.pair_commute2.
    rewrite (cat_ident2 PLT).    
    apply PLT.pair_eq. auto. auto.
    auto.
  Qed.

  Definition Ysem Γ 
    : Γ → U (tydom (((σ₁ ⇒ σ₂) ⇒ (σ₁ ⇒ σ₂)) ⇒ (σ₁ ⇒ σ₂)))
    := strict_curry' (fixes _ _ Ybody ∘ π₂).
End Ydefn.

Notation "'Λ' f" := (strict_curry' f) : ski_scope.

Fixpoint denote (τ:ty) (m:term τ) : 1 → U (tydom τ) :=
  match m in term τ return 1 → U (tydom τ) with
  | tbool b => flat_elem' b
  | tapp σ₁ σ₂ m₁ m₂ => strict_app' ∘ 〈〚m₁〛,〚m₂〛〉
  | tI σ => Λ(π₂)
  | tK σ₁ σ₂ => Λ(Λ(π₂ ∘ π₁))
  | tS σ₁ σ₂ σ₃ => Λ(Λ(Λ(
                     strict_app' ∘
                       〈 strict_app' ∘ 〈π₂ ∘ π₁ ∘ π₁, π₂〉
                       , strict_app' ∘ 〈π₂ ∘ π₁, π₂〉
                       〉
                      )))
  | tIF σ => Λ(flat_cases' (fun b:bool =>
                if b then Λ(Λ(π₂ ∘ π₁))
                     else Λ(Λ(π₂))
                ))
  | tY σ₁ σ₂ => Ysem σ₁ σ₂ 1
  end
 where "〚 m 〛" := (denote _ m) : ski_scope.


Lemma value_inert_semvalue : forall n,
  (forall σ x,
    tmsize _ x = n ->
    eval σ x x -> semvalue 〚x〛) /\
  (forall σ₁ σ₂ x (y:1 → U (tydom σ₁)),
    tmsize _ x = n ->
    value x ->
    inert σ₁ σ₂ x ->
    semvalue y ->
    semvalue (strict_app' ∘ 〈〚x〛, y〉)).
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
  simpl.
  rewrite flat_cases_elem'.
  destruct b.
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

Lemma value_semvalue : forall σ (x:term σ),
  value x -> semvalue 〚x〛.
Proof.
  intros. destruct (value_inert_semvalue (tmsize _ x)); auto.
Qed.

Lemma inert_semvalue σ₁ σ₂ x y :    
  value x -> inert σ₁ σ₂ x -> semvalue y ->
  semvalue (strict_app' ∘ 〈〚x〛, y 〉).
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
  strict_app' ∘ 〈〚x〛,〚y〛〉 ≈ 〚z〛.
Proof.
  intros. inv H1.

  inv H1. simpl.
  rewrite strict_curry_app'; auto.
  rewrite PLT.pair_commute2. auto.
  
  simpl.
  rewrite strict_curry_app'; auto.
  rewrite strict_curry_app2'; auto.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute2. auto.
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
  repeat rewrite PLT.pair_commute1.
  repeat rewrite PLT.pair_commute2.
  rewrite (PLT.pair_compose_commute false).
  repeat rewrite <- (cat_assoc PLT).
  repeat rewrite PLT.pair_commute1.
  repeat rewrite PLT.pair_commute2.
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
  repeat rewrite PLT.pair_commute1.
  repeat rewrite PLT.pair_commute2. auto.
  apply flat_elem'_semvalue.
  
  destruct (value_app_inv _ _ _ _ H). clear H2.
  inv H1.
  simpl.
  rewrite strict_curry_app'; auto.
  rewrite flat_cases_elem'.
  rewrite strict_curry_app2'; auto.
  rewrite strict_curry_app2'; auto.
  repeat rewrite PLT.pair_commute2. auto.
  apply flat_elem'_semvalue.

  destruct (value_app_inv _ _ _ _ H). clear H1 H2.
  simpl.    
  unfold Ysem.
  rewrite strict_curry_app'; auto.
  rewrite fixes_unroll at 1. unfold Ybody at 1.
  rewrite PLT.curry_apply2.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute2.
  rewrite <- (cat_assoc PLT).
  rewrite strict_curry_app2'; auto.
  rewrite <- (cat_assoc PLT).
  apply cat_respects. auto.
  rewrite (PLT.pair_compose_commute false).
  rewrite PLT.pair_commute2.
  apply PLT.pair_eq. 2: auto.
  rewrite <- (cat_assoc PLT).
  apply cat_respects. auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  rewrite (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  apply cat_ident2.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  rewrite (cat_assoc PLT).
  rewrite PLT.pair_commute2.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute2.
  auto.
  apply (value_semvalue _ f). auto.
Qed.

Lemma soundness : forall τ (m z:term τ),
  eval τ m z -> 〚m〛≈〚z〛.
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


Lemma eval_app_congruence σ₁ σ₂ : forall x x' y y' z,
  (forall q, eval _ x q -> eval _ x' q) ->
  (forall q, eval _ y q -> eval _ y' q) ->
  eval _ (@tapp σ₁ σ₂ x y) z ->
  eval _ (@tapp σ₁ σ₂ x' y') z.
Proof.
  intros.
  inv H1.
  apply H in H7.
  apply H0 in H8.
  eapply eapp1; eauto.
  apply eapp2; auto.
Qed.


Fixpoint LR (τ:ty) : 
  term τ -> (1 → U (tydom τ)) -> Prop :=
  match τ as τ' return 
    term τ' -> (1 → U (tydom τ')) -> Prop
  with
  | ty_bool => fun m h => exists b:bool,
        m = tbool b /\ h ≈ flat_elem' b
  | ty_arrow σ₁ σ₂ => fun m h =>
        forall n h',
          LR σ₁ n h' -> value n -> semvalue h' ->
          semvalue (strict_app' ∘ 〈h, h'〉) ->
          exists z,
            eval _ (m • n) z /\
            LR σ₂ z (strict_app' ∘ 〈h, h'〉)
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
  | t::ts' => (t ⇒ (lrtys ts' z))%ty
  end.

Fixpoint lrsyn (ts:list ty) : Type :=
  match ts with
  | nil => unit
  | t::ts' => prod (lrsyn ts') (term t)
  end.

Fixpoint lrsem (ts:list ty) : Type :=
  match ts with
  | nil => unit
  | t::ts' => prod (lrsem ts') (1 → U (tydom t))
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
  | t::ts => fun xs m => lrapp ts _ (fst xs) (m • (snd xs))
  end.

Fixpoint lrsemapp (ls:list ty) z :
  lrsem ls -> (1 → U (tydom (lrtys ls z))) -> (1 → U (tydom z)) :=
  match ls as ls' return
    lrsem ls' -> (1 → U (tydom (lrtys ls' z)))  -> (1 → U (tydom z))
  with
  | nil => fun _ h => h
  | t::ts => fun ys h => lrsemapp ts _ (fst ys) (strict_app' ∘ 〈h, snd ys〉)
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

Lemma semvalue_lrsemapp_out ls : forall τ ys h,
   semvalue (lrsemapp ls τ ys h) -> semvalue h.
Proof.
  induction ls; simpl; intros; auto.
  apply IHls in H.
  apply semvalue_app_out1' in H. auto.
Qed.

Lemma LR_under_apply ls :
   forall (τ : ty) (m z0 : term (lrtys ls τ)) (xs : lrsyn ls) 
     (ys : lrsem ls) (h : 1 → U (tydom (lrtys ls τ))),
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


Lemma semvalue_sup (B:∂PLT) (XS:dirset (PLT.homset_cpo _ 1 (U B))) : 
  semvalue (∐XS) -> exists x, x ∈ XS /\ semvalue x.
Proof.
  intros.
  destruct (H tt) as [q ?].
  simpl in H0.
  apply union_axiom in H0.
  destruct H0 as [q' [??]].
  apply image_axiom2 in H0.
  destruct H0 as [q'' [??]].
  simpl in *.
  exists q''. split; auto.
  red; intro. destruct g.
  exists q. rewrite <- H2; auto.
Qed.

Lemma LR_admissible τ : 
  forall m (XS:dirset (PLT.homset_cpo _ 1 (U (tydom τ)))),
  semvalue (∐XS) ->
  (forall x, x ∈ XS -> semvalue x -> LR τ m x) -> LR τ m (∐XS).
Proof.
  induction τ; simpl. intros.

  apply semvalue_sup in H. destruct H as [x [??]].
  destruct (H0 x) as [b [??]]; auto.
  subst m. exists b. split; auto.
  split.
  apply CPO.sup_is_least.
  hnf; simpl; intros.
  destruct (proj2_sig XS (x::x0::nil)). hnf; auto.
  hnf; intros. apply cons_elem in H4.
  destruct H4. rewrite H4. auto.
  apply cons_elem in H4.
  destruct H4. rewrite H4. auto.
  apply nil_elem in H4. elim H4.
  destruct H4.
  assert (x1 ≈ x).  
  assert (x ≤ x1). apply H4. apply cons_elem; auto.
  split; auto.
  hnf; intros.
  rewrite H3 in H6.
  assert ((tt,Some b : U (flat enumbool)) ∈ PLT.hom_rel x1).
  apply H6.
  unfold flat_elem'.
  apply PLT.compose_hom_rel. exists (Some tt).
  split. simpl. apply adj_unit_rel_elem. auto.
  apply U_hom_rel. right.
  exists tt. exists b. split; auto.
  apply PLT.compose_hom_rel; auto.
  exists tt. split.
  simpl. apply eprod_elem. split; simpl.
  apply eff_complete. apply single_axiom; auto.
  simpl. apply single_axiom; auto.
  destruct H3. apply H9.
  destruct a. unfold flat_elem'.
  apply PLT.compose_hom_rel.
  exists (Some tt). split.
  simpl. apply adj_unit_rel_elem; simpl; auto.
  destruct c; auto.
  apply U_hom_rel.
  destruct c0; auto. right.
  exists tt. exists c0. split; auto.
  apply PLT.compose_hom_rel.
  exists tt.
  split. simpl.
  apply eprod_elem. split.
  apply eff_complete. apply single_axiom; auto.
  simpl. apply single_axiom; auto.
  cut (c0 = b). intros. subst c0; auto.
  destruct c.
  destruct (PLT.hom_directed _ _ _ x1 tt ((Some c0::Some b::nil))).
  hnf; auto.
  red; intros.
  apply cons_elem in H10. destruct H10. rewrite H10.
  apply erel_image_elem. auto.
  apply cons_elem in H10. destruct H10. rewrite H10.
  apply erel_image_elem. auto.
  apply nil_elem in H10. elim H10.
  destruct H10.
  assert (Some c0 ≤ x2).
  apply H10. apply cons_elem; auto.
  assert (Some (b:enumbool) ≤ x2).
  apply H10. apply cons_elem. right. apply cons_elem; auto.
  destruct x2. hnf in H12. hnf in H13.
  subst c0. subst b. auto.
  elim H12.

  rewrite <- H3. rewrite <- H6.
  apply H4.
  apply cons_elem. right.
  apply cons_elem. auto.
  apply CPO.sup_is_ub. rewrite <- H3. auto.

  simpl; intros.
  set (g := (postcompose _ strict_app' ∘ pair_left (U (tydom (τ1 ⇒ τ2))) h')).
  assert (strict_app' ∘ PLT.pair (∐XS) h' ≈ g (∐XS)).
  simpl; auto.
  assert (strict_app' ∘ PLT.pair (∐XS) h' ≈ ∐(image g XS)).
  rewrite H5.
  apply CPO.continuous_sup'.
  apply continuous_sequence.
  apply postcompose_continuous.
  apply pair_left_continuous.

  assert (exists q, q ∈ XS /\
    semvalue (strict_app' ∘ PLT.pair q h')).
  rewrite H6 in H4.
  destruct (H4 tt) as [q ?].
  simpl.
  simpl in H7.
  apply union_axiom in H7.
  destruct H7 as [q' [??]].
  apply image_axiom2 in H7.
  destruct H7 as [q'' [??]].
  apply image_axiom2 in H7.
  destruct H7 as [q''' [??]].
  exists q'''. split; auto.
  rewrite H9 in H8.
  rewrite H10 in H8.
  red; intros.
  exists q. auto.
  destruct H7 as [q [??]].
  assert (semvalue q).
  apply semvalue_app_out1' in H8. auto.
  destruct (H0 q H7 H9 n h' H1 H2 H3 H8) as [z [??]].
  exists z. split; auto.
  cut (LR τ2 z (∐(image g XS))).
  apply LR_equiv; auto.
  apply IHτ2; auto.
  rewrite <- H6. auto.

  intros.
  apply image_axiom2 in H12. destruct H12 as [y [??]].
  rewrite H14 in H13.
  simpl in H13.
  assert (semvalue y).
  apply semvalue_app_out1' in H13. auto.
  destruct (H0 y H12 H15 n h' H1 H2 H3) as [z' [??]]; auto.
  assert (z = z').
  eapply eval_eq; eauto. subst z'.
  revert H17.
  apply LR_equiv; auto.
Qed.

Lemma LR_Ybody σ₁ σ₂
  (f:term ((σ₁ ⇒ σ₂) ⇒ σ₁ ⇒ σ₂)) hf :
  LR _ f hf -> value f -> semvalue hf ->

  forall (x:term σ₁) hx,
    LR σ₁ x hx -> value x -> semvalue hx ->
    semvalue (strict_app' ∘ 〈fixes _ _ (Ybody σ₁ σ₂) ∘ hf, hx〉) ->
    exists z:term σ₂,
      eval _ (tY σ₁ σ₂ • f • x) z /\
      LR _ z (strict_app' ∘ 〈fixes _ _ (Ybody σ₁ σ₂) ∘ hf, hx〉).
Proof.      
  intros Hf1 Hf2 Hf3. unfold fixes.
  apply scott_induction.
  split.

  intros.
  apply semvalue_app_out1' in H2.
  destruct (H2 tt) as [q ?].
  rewrite (PLT.compose_hom_rel _ _ _ _ hf ⊥ tt (Some q)) in H3.
  destruct H3 as [?[??]].  
  elimtype False. revert H4.
  clear. simpl bottom.
  intros.
  unfold plt_hom_adj' in H4; simpl in H4.
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [?[??]].
  simpl in H. apply adj_unit_rel_elem in H.
  apply U_hom_rel in H0.
  destruct H0. discriminate.
  destruct H0 as [? [? [?[??]]]].
  subst x. inv H2.
  simpl in H0.
  apply union_axiom in H0.
  destruct H0 as [?[??]].
  apply image_axiom2 in H0.
  destruct H0 as [?[??]].
  apply empty_elem in H0. elim H0.

  intros.
  set (g := (postcompose _ strict_app' 
            ∘ pair_left (U (tydom (σ₁ ⇒ σ₂))) hx
            ∘ precompose _ hf)).
  assert (strict_app' ∘ PLT.pair (∐XS ∘ hf) hx ≈ g (∐XS)). auto.
  assert (strict_app' ∘ PLT.pair (∐XS ∘ hf) hx ≈ ∐(image g XS)).
  rewrite H5.

  apply CPO.continuous_sup'.
  apply continuous_sequence.
  apply continuous_sequence.
  apply postcompose_continuous.
  apply pair_left_continuous.
  apply precompose_continuous.

  assert (exists q, q ∈ XS /\
    semvalue (strict_app' ∘ PLT.pair (q ∘ hf) hx)).
  rewrite H6 in H4.
  apply semvalue_sup in H4.
  destruct H4 as [q [??]].
  apply image_axiom2 in H4 as [q' [??]].
  exists q'. split; auto.
  simpl in H8. rewrite <- H8. auto.

  destruct H7 as [q [??]].
  destruct (H0 q H7 x hx H1 H2 H3) as [z [??]]; auto.
  exists z.
  split; auto.
  cut (LR σ₂ z (∐(image g XS))).  
  apply LR_equiv; auto.
  apply LR_admissible.
  rewrite <- H6; auto.
  intros.
  apply image_axiom2 in H11. destruct H11 as [y [??]].
  simpl in H13. rewrite H13 in H12.
  destruct (H0 y H11 x hx) as [z' [??]]; auto.
  assert (z = z'). eapply eval_eq; eauto. subst z'.
  revert H15; apply LR_equiv; auto.  

  intros.
  destruct (H0 x0 hx H1 H2 H3) as [z [??]]. rewrite H; auto.
  exists z; split; auto.
  revert H6. apply LR_equiv. rewrite <- H; auto.

  intros.
  simpl in H3. unfold fixes_step in H3.
  unfold Ybody in H3.
  rewrite PLT.curry_apply2 in H3.
  rewrite <- (cat_assoc PLT) in H3.
  rewrite (PLT.pair_compose_commute false) in H3.
  rewrite strict_curry_app2' in H3.
  rewrite <- (cat_assoc PLT) in H3.
  rewrite (PLT.pair_compose_commute false) in H3.
  rewrite PLT.pair_commute2 in H3.  
  rewrite <- (cat_assoc PLT) in H3.
  rewrite (PLT.pair_compose_commute false) in H3.
  rewrite <- (cat_assoc PLT) in H3.
  rewrite PLT.pair_commute1 in H3.
  rewrite PLT.pair_commute1 in H3.
  rewrite <- (cat_assoc PLT) in H3.
  rewrite PLT.pair_commute1 in H3.
  rewrite PLT.pair_commute2 in H3.
  rewrite (cat_ident2 PLT) in H3.    

  simpl in Hf1.
  destruct (Hf1 (tapp (tY _ _) f) (x ∘ hf)) as [q [??]]; auto.
  apply eapp2. apply eY. auto.
  intros [? Hr]; inv Hr.
  apply semvalue_app_out1' in H3.
  apply semvalue_app_out2' in H3. auto.
  apply semvalue_app_out1' in H3. auto.
  destruct (H5 x0 hx) as [q' [?]]; auto.
  exists q'. split.
  eapply eapp1.
  apply eapp2. apply eY. eauto.
  intros [? Hr]; inv Hr. eauto.
  apply redex_Y.
  revert H6. apply eval_app_congruence; intros; auto.
  apply eval_trans with q; auto.
  revert H7. apply LR_equiv.
  simpl. unfold fixes_step. unfold Ybody.
  symmetry.

  rewrite PLT.curry_apply2.
  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  rewrite strict_curry_app2'.
  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  rewrite PLT.pair_commute2.
  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute1.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute2.
  rewrite (cat_ident2 PLT).
  auto.
  apply semvalue_app_out2' in H3. auto.
  auto.
Qed.

Lemma LR_Y σ₁ σ₂ : LR _ (tY σ₁ σ₂) 〚tY σ₁ σ₂〛.
Proof.
  simpl; intros.
  exists (tapp (tY _ _) n).
  split. apply eapp2. apply eY. auto.
  intros [? Hr]; inv Hr.
  intros.  
  unfold Ysem in H6.
  rewrite strict_curry_app' in H6.
  rewrite <- (cat_assoc PLT) in H6.
  rewrite PLT.pair_commute2 in H6.
  destruct (LR_Ybody σ₁ σ₂ n h' H H0 H1 n0 h'0 H3 H4 H5 H6) as [z [??]].
  exists z. split; auto.
  revert H8. apply LR_equiv.
  unfold Ysem.
  rewrite strict_curry_app'.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute2.
  auto.
  auto.
  auto.
Qed.


Lemma LR_I σ : LR _ (tI σ) 〚tI σ〛.
Proof.
  simpl. intros.
  exists n. split.
  eapply eapp1.
  apply eI. apply H0.
  apply redex_I. auto.
  revert H. apply LR_equiv. rewrite strict_curry_app'.
  rewrite PLT.pair_commute2; auto. auto.
Qed.

Lemma LR_K σ₁ σ₂ : LR _ (tK σ₁ σ₂) 〚tK σ₁ σ₂〛.
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
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute2.
  auto. auto. auto.
Qed.

Lemma LR_S σ₁ σ₂ σ₃ : LR _ (tS σ₁ σ₂ σ₃) 〚tS σ₁ σ₂ σ₃〛.
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
                                        ∘ PLT.pair (π₂ ∘ π₁ ∘ π₁) π₂)
                                       (strict_app'
                                        ∘ PLT.pair (π₂ ∘ π₁) π₂))))) h')
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
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute2.
  auto.
  rewrite PLT.pair_commute2.
  auto.
  rewrite <- (cat_assoc PLT).
  apply cat_respects; auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq; auto.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute2.
  auto.
  rewrite PLT.pair_commute2.
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

Lemma LR_IF σ : LR _ (tIF σ) 〚tIF σ〛.
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
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute2. auto.
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
  rewrite PLT.pair_commute2. auto.
  apply flat_elem'_semvalue.  
Qed.


Lemma fundamental_lemma : forall σ (n:term σ) ls τ m xs ys
  (Hσ : σ = lrtys ls τ),
  eq_rect σ term n (lrtys ls τ) Hσ = m ->
  lrhyps ls xs ys ->
  semvalue (lrsemapp ls τ ys 〚m〛) ->
  exists z,
    eval _ (lrapp ls τ xs m) z /\
    LR τ z (lrsemapp ls τ ys 〚m〛).
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

  exists (tI σ). split. apply eI. apply LR_I.

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

  exists (tK _ _). split. apply eK. apply LR_K.

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
  split. simpl. apply eS. apply LR_S.

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

  exists (tY σ₁ σ₂). split. apply eY. apply LR_Y.
Qed.

Lemma fundamental_lemma' : forall τ (m:term τ),
  semvalue 〚m〛 ->
  exists z, eval τ m z /\ LR τ z 〚m〛.
Proof.
  intros.
  apply (fundamental_lemma τ m nil τ m tt tt (refl_equal _) (refl_equal _) I).
  simpl. auto.
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

Theorem adequacy : forall τ (m n:term τ),
  〚m〛≈〚n〛 -> cxt_eq ty_bool τ m n.
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
  exact tt.
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
  exact tt.
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

Corollary denote_bottom_nonvalue : forall τ (m:term τ),
  (~exists z, eval τ m z) <-> 〚m〛 ≈ ⊥.
Proof.
  intros. split; intro.

  split. 2: apply bottom_least.
  hnf. intros [u x] Hx. destruct x.
  elimtype False.
  destruct (fundamental_lemma' τ m) as [z [??]].
  red; intros. destruct g. simpl.
  exists c. auto.
  elim H. eauto.
  apply PLT.compose_hom_rel.    
  simpl. exists None.
  split.
  apply adj_unit_rel_elem. hnf; auto.
  apply U_hom_rel. auto.

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
  apply (PLT.compose_hom_rel) in H3.
  destruct H3 as [q [??]].
  apply U_hom_rel in H5.
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
