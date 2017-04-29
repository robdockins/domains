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
Require Import discrete.

(** * Soundness, adequacy and strong normalization for simply-typed SKI with booleans.

    As a demonstration of the system in action, here is a proof
    of soundness and adequacy for a simply-typed SKI calculus.
    The adequacy proof goes via a standard logical-relations argument.
    As a corollary of the main logical-relations lemma, we achieve
    strong normalization for the calculus.
  *)

(**  We have arrow types and a single base type of booleans. *)
Inductive ty :=
  | ty_bool
  | ty_arrow : ty -> ty -> ty.

Delimit Scope ty_scope with ty.
Notation "2" := ty_bool : ty_scope.
Notation "x ⇒ y" := (ty_arrow (x)%ty (y)%ty) : ty_scope.
Bind Scope ty_scope with ty.

Delimit Scope ski_scope with ski.
Open Scope ski_scope.

(**  Terms are boolean constants, the standard combinators S, K and I,
     and an IF/THEN/ELSE combinator; and applications.
  *)
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
                term (2 ⇒ σ ⇒ σ ⇒ σ).

Arguments tapp [_ _] _ _.
Notation "x • y" := (tapp x y) 
  (at level 52, left associativity, format "x • y") : ski_scope.

(**  The operational semantics is given in a big-step style, with the specification
     of redexes split out into a separate relation.
  *)

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
                  redex _ _ (tIF σ • tbool false • th) el el.

Inductive eval : forall τ, term τ -> term τ -> Prop :=
  | ebool : forall b, eval 2 (tbool b) (tbool b)
  | eI   : forall σ, eval _ (tI σ) (tI _)
  | eK   : forall σ₁ σ₂, eval _ (tK σ₁ σ₂) (tK _ _)
  | eS   : forall σ₁ σ₂ σ₃, eval _ (tS σ₁ σ₂ σ₃) (tS _ _ _)
  | eIF  : forall σ , eval _ (tIF σ) (tIF σ)
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

(**  Syntactic types have decicable equality, which
     implies injectivity for dependent pairs with
     (syntactic) types as the type being depended upon.
  *)
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

(** Values are terms that evaluate to themselves.
  *)
Definition value σ (t:term σ) := eval _ t t.
Arguments value [σ] t.

(**  Here are some basic techincal results  
     about the operational semantics.
  *)
Lemma eval_value τ x y :
  eval τ x y -> value y.
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


(**  Types are interpreted as unpointed domains, using the discrete domain
     of booleans and the exponential in PLT.
  *)
Fixpoint tydom (τ:ty) : PLT :=
  match τ with
  | 2%ty => disc finbool
  | (τ₁ ⇒ τ₂)%ty => tydom τ₁ ⇒ tydom τ₂
  end.

(**  The denotation of terms is given by a simple fixpoint on term structure.
     The denotation of each combinator is a straightforward interpretation of the
     usual lambda term into the operations of a cartesian closed category.
  *)

Fixpoint denote (τ:ty) (m:term τ) : 1 → tydom τ :=
  match m in term τ return 1 → tydom τ with
  | tbool b => disc_elem b

  | tapp m₁ m₂ => apply ∘ 〈〚m₁〛, 〚m₂〛〉

  | tI σ => Λ(π₂)

  | tK σ₁ σ₂ => Λ(Λ(π₂ ∘ π₁))

  | tS σ₁ σ₂ σ₃ => Λ(Λ(Λ(
                    apply ∘ 〈 apply ∘ 〈 π₂ ∘ π₁ ∘ π₁, π₂ 〉    
                            , apply ∘ 〈 π₂ ∘ π₁, π₂ 〉
                            〉
                   )))

  | tIF σ => Λ (disc_cases (fun b:bool =>
                 if b then Λ(Λ(π₂ ∘ π₁))
                      else Λ(Λ(π₂))
             ))
  end

 where "〚 m 〛" := (denote _ m) : ski_scope.


(**  Every redex preserves the meaning of terms. *)
Lemma redex_soundness : forall σ₁ σ₂ x y z,
  redex σ₁ σ₂ x y z ->
  apply ∘ 〈〚x〛,〚y〛〉 ≈ 〚z〛.
Proof.
  intros. case H; simpl.
  intros.

  rewrite PLT.curry_apply2.
  rewrite PLT.pair_commute2. auto.
  intros.
  rewrite PLT.curry_apply2.
  rewrite PLT.curry_apply3.
  rewrite <- (cat_assoc (PLT.PLT false) _ _ _ _ PLT.pi2).
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute2.
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
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute2. auto.
  rewrite PLT.pair_commute2. auto.
  rewrite <- (cat_assoc (PLT.PLT false)).
  apply cat_respects. auto.
  rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq.
  repeat rewrite <- (cat_assoc (PLT.PLT false)).
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute2. auto.
  rewrite PLT.pair_commute2. auto.

  intros.
  rewrite PLT.curry_apply2.
  rewrite disc_cases_elem.
  rewrite PLT.curry_apply3.
  rewrite PLT.curry_apply3.
  rewrite <- (cat_assoc (PLT.PLT false)).
  rewrite PLT.pair_commute1.  
  rewrite PLT.pair_commute2.
  auto.

  intros.
  rewrite PLT.curry_apply2.
  rewrite disc_cases_elem.
  rewrite PLT.curry_apply3.
  rewrite PLT.curry_apply3.
  rewrite PLT.pair_commute2.
  auto.
Qed.

(**  Evaluation preserves the denotation of terms. *)
Theorem soundness : forall τ (m z:term τ),
  eval τ m z -> 〚m〛 ≈ 〚z〛.
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


(** * The logical relations lemma

    Now we define the logical relation.  It is defined by induction
    on the structure of types, in a standard way.
  *)
Fixpoint LR (τ:ty) : term τ -> (1 → tydom τ) -> Prop :=
  match τ as τ' return term τ' -> (1 → tydom τ') -> Prop
  with
  | ty_bool => fun m h =>
        exists b:bool, m = tbool b /\ h ≈ disc_elem b
  | ty_arrow σ₁ σ₂ => fun m h =>
        forall n h', 
          LR σ₁ n h' -> eval σ₁ n n ->
          exists z, 
            eval _ (m•n) z /\
            LR σ₂ z (apply ∘ 〈h, h'〉)
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

(**  Now we need a host of auxilary definitions to state
     the main lemmas regarding the logical relation.  These
     definitions allow us to apply an arbitrary number of
     arguments to a syntactic term and to the denotation of terms.
  *)
Fixpoint lrtys (ts:list ty) (z:ty) : ty :=
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
  | t::ts' => prod (lrsem ts') (1 → tydom t)
  end.

Fixpoint lrhyps (ls:list ty) : lrsyn ls -> lrsem ls -> Prop :=
  match ls with
  | nil => fun _ _ => True
  | t::ts => fun xs ys =>
      eval _ (snd xs) (snd xs) /\
      LR t (snd xs) (snd ys) /\
      lrhyps ts (fst xs) (fst ys)
  end.

Fixpoint lrapp (ls:list ty) z : lrsyn ls -> term (lrtys ls z) -> term z :=
  match ls as ls' return lrsyn ls' -> term (lrtys ls' z) -> term z with
  | nil => fun _ m => m
  | t::ts => fun xs m => lrapp ts _ (fst xs) (m • (snd xs))
  end.

Fixpoint lrsemapp (ls:list ty) z :
  lrsem ls -> (1 → tydom (lrtys ls z)) -> (1 → tydom z) :=
  match ls as ls' return
    lrsem ls' -> (1 → tydom (lrtys ls' z)) -> (1 → tydom z)
  with
  | nil => fun _ h => h
  | t::ts => fun ys h => lrsemapp ts _ (fst ys) (apply ∘ 〈h, snd ys〉)
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


(**  This fact is important in the base cases of the fundamental lemma; it allows
     unwind a stack of applications.
  *)
Lemma LR_under_apply ls :
   forall (τ : ty) (m z0 : term (lrtys ls τ)) (xs : lrsyn ls) 
     (ys : lrsem ls) (h : 1 → (tydom (lrtys ls τ))),
   eval (lrtys ls τ) m z0 ->
   lrhyps ls xs ys ->
   LR (lrtys ls τ) z0 h ->
   exists z : term τ,
     eval τ (lrapp ls τ xs m) z /\ LR τ z (lrsemapp ls τ ys h).
Proof.
  induction ls; simpl; intros.
  exists z0. split; auto.
  destruct xs as [xs x].
  destruct ys as [ys y]. simpl in *.
  destruct H0 as [?[??]].
  destruct (H1 x y) as [z1 [??]]; auto.

  generalize (IHls τ (tapp z0 x) z1 xs ys (apply ∘ 〈h,y〉)
     H4 H3 H5).
  intros [q [??]].
  exists q; split; auto.
  revert H6.
  apply eval_lrapp_congruence. intro.
  apply eval_app_congruence; auto.
  fold lrtys. intros.
  apply eval_trans with z0; auto.
Qed.

(**  Now we prove that each of the base combinators stands
     in the logical relation with their denotations.
  *)
Lemma LR_I σ : LR _ (tI σ) 〚tI σ〛.
Proof.
  simpl. intros.
  exists n. split.
  eapply eapp1.
  apply eI. apply H0.
  apply redex_I. auto.
  revert H. apply LR_equiv. rewrite PLT.curry_apply2.
  rewrite PLT.pair_commute2; auto.
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
  rewrite PLT.curry_apply2.
  rewrite PLT.curry_apply3.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute2.
  auto.
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

  assert (
    (PLT.app
        ∘ PLT.pair
            (PLT.app
             ∘ PLT.pair
                 (PLT.app
                  ∘ PLT.pair
                      (PLT.curry
                         (PLT.curry
                            (PLT.curry
                               (PLT.app
                                ∘ PLT.pair
                                    (PLT.app
                                     ∘ PLT.pair (PLT.pi2 ∘ PLT.pi1 ∘ PLT.pi1)
                                         PLT.pi2)
                                    (PLT.app
                                     ∘ PLT.pair (PLT.pi2 ∘ PLT.pi1) PLT.pi2)))))
                      h') h'0) h'1)
     ≈
     PLT.app ∘ PLT.pair
       (PLT.app ∘ PLT.pair h' h'1)
       (PLT.app ∘ PLT.pair h'0 h'1)).
  clear.
  rewrite PLT.curry_apply2.
  rewrite PLT.curry_apply3.
  rewrite PLT.curry_apply3.
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

  destruct (H1 n1 h'1) as [z0 [??]]; auto; clear H1.
  destruct (H n1 h'1) as [z1 [??]]; auto; clear H.
  destruct (H8 z0 (PLT.app ∘ PLT.pair h'0 h'1)) as [z2 [??]]; auto; clear H8.
  eapply eval_value; eauto.
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
  revert H9. apply LR_equiv. auto.
Qed.

Lemma LR_IF σ : LR _ (tIF σ) 〚tIF σ〛.
Proof.
  simpl; intros.  
  destruct H as [b [??]]. subst n.
  exists (tapp (tIF σ) (tbool b)).
  split. apply eapp2. apply eIF. apply ebool.
  intros [r Hr]; inversion Hr.
  intros.
  exists (tapp (tapp (tIF σ) (tbool b)) n).
  split.
  apply eapp2. apply eapp2. 
  apply eIF. apply ebool.
  intros [r Hr]; inversion Hr. eauto.
  intros [r Hr]; inversion Hr. eauto.
  intros.
  destruct b.
  exists n. split.
  eapply eapp1. 
  apply eapp2. apply eapp2. apply eIF. apply ebool.
  intros [r Hr]; inversion Hr. eauto.
  intros [r Hr]; inversion Hr. eauto.
  econstructor. auto.
  revert H. apply LR_equiv.
  rewrite PLT.curry_apply2. rewrite H1.
  rewrite disc_cases_elem.
  rewrite PLT.curry_apply3.
  rewrite PLT.curry_apply3.
  repeat rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  rewrite PLT.pair_commute2.
  auto.    

  exists n0. split.
  eapply eapp1.
  apply eapp2. apply eapp2. apply eIF. apply ebool.
  intros [r Hr]; inversion Hr. eauto.
  intros [r Hr]; inversion Hr. eauto.
  econstructor. auto.
  revert H3. apply LR_equiv.
  rewrite PLT.curry_apply2. rewrite H1.
  rewrite disc_cases_elem.
  rewrite PLT.curry_apply3.
  rewrite PLT.curry_apply3.
  rewrite PLT.pair_commute2.
  auto.    
Qed.

(**  The fundamental lemma states that every term stands in the logical relation
     with its denotation when applied related term/denotation pairs.
  *)
Lemma fundamental_lemma : forall σ (n:term σ) ls τ m xs ys
  (Hσ : σ = lrtys ls τ),
  eq_rect σ term n (lrtys ls τ) Hσ = m ->
  lrhyps ls xs ys ->
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
  destruct (IHn1 (σ₁::ls) _ n1 (xs, q2) (ys, denote σ₁ q2)
    (Logic.refl_equal _) (Logic.refl_equal _)) as [q1 [??]].
  simpl; intuition. eapply eval_value; eauto.
  revert H1. apply LR_equiv.
  simpl. simpl in H. apply soundness; auto.
  exists q1. split.
  revert H2.
  simpl. apply eval_lrapp_congruence.
  intro q. apply eval_app_congruence; intros; auto.
  apply eval_trans with q2; auto.
  revert H3.
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
  destruct H2 as [z0 [??]].
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
  destruct H2 as [z0 [??]].
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
  destruct H2 as [z0 [??]].
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
  destruct H2 as [z0 [??]].
  eapply LR_under_apply; eauto.
  apply Eqdep_dec.UIP_dec. decide equality.

  exists (tIF σ). split. apply eIF. apply LR_IF.
Qed.

(**  A simpified form of the fundamental lemma that follows
     from the inductively-strong one above.
  *)
Lemma fundamental_lemma' : forall τ (m:term τ),
  exists z, eval τ m z /\ LR τ z 〚 m 〛.
Proof.
  intros.
  apply (fundamental_lemma _ m nil _ m tt tt 
    (Logic.refl_equal _) (Logic.refl_equal _) I).
Qed.

(** * Contextual equivalance and the adequacy theorem.

    Now we define contextual equivalance.  Contexts here are
    given in "inside-out" form, which makes the induction in the
    adequacy proof significantly easier.
  *)
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
  | cxt_top _ => fun x => x
  | cxt_appl _ σ₁ σ₂ t C' => fun x => plug τ _ C' (tapp x t)
  | cxt_appr _ σ₁ σ₂ t C' => fun x => plug τ _ C' (tapp t x)
  end.

Definition cxt_eq τ σ (m n:term σ):=
  forall (C:context τ σ) (z:term τ),
    eval τ (plug τ σ C m) z <-> eval τ (plug τ σ C n) z.

(**  Adequacy means that terms with equivalant denotations
     are contextually equivalant in any boolean context.
  *)
Theorem adequacy : forall τ (m n:term τ),
  〚m〛 ≈ 〚n〛 -> cxt_eq 2 τ m n.
Proof.
  intros. intro.
  revert n m H.
  induction C.

  simpl; intros.
  destruct (fundamental_lemma' _ m) as [zm [??]]. simpl in *.
  destruct (fundamental_lemma' _ n) as [zn [??]]. simpl in *.
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

(**  As a corollary of the fundamental lemma, we learn that
     the calculus is strongly normalizing.
  *)
Corollary normalizing : forall τ (m:term τ), exists z, eval τ m z.
Proof.
  intros.
  generalize (fundamental_lemma' τ m).
  simpl. intros [z [??]]. exists z; auto.
Qed.

(** These should print "Closed under the global context", meaning these
    theorems hold without the use of any axioms.
  *)
Print Assumptions adequacy.
Print Assumptions normalizing.
