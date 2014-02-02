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


(**  We have arrow types and a single base type of booleans. *)
Inductive ty :=
  | ty_bool
  | ty_unit : ty
  | ty_prod : ty -> ty -> ty
  | ty_arrow : ty -> ty -> ty.

Delimit Scope ty_scope with ty.

Notation "x ⇒ y" := (ty_arrow x y) : ty_scope.
Notation "x × y" := (ty_prod x y) : ty_scope.
Local Open Scope ty.


Inductive term : ty -> ty -> Type :=

  | tbool : forall σ (b:bool),
                term σ ty_bool

  | tif : forall σ₁ σ₂,
                term σ₁ σ₂ ->
                term σ₁ σ₂ ->
                term σ₁ (ty_bool ⇒ σ₂)

  | tterminate : forall σ,
                term σ ty_unit

  | tident : forall σ,
                term σ σ

  | tcompose : forall σ₁ σ₂ σ₃,
                term σ₂ σ₃ ->
                term σ₁ σ₂ ->
                term σ₁ σ₃

  | tpair : forall σ₁ σ₂ σ₃,
                term σ₁ σ₂ ->
                term σ₁ σ₃ ->
                term σ₁ (σ₂ × σ₃)

  | tpi1 : forall σ₁ σ₂,
                term (σ₁ × σ₂) σ₁

  | tpi2 : forall σ₁ σ₂,
                term (σ₁ × σ₂) σ₂

  | tapp : forall σ₁ σ₂,
                term ((σ₁ ⇒ σ₂) × σ₁) σ₂

  | tcurry : forall σ₁ σ₂ σ₃,
                term (σ₁ × σ₂) σ₃ ->
                term σ₁ (σ₂ ⇒ σ₃).


(**  Types are interpreted as unpointed domains, using the discrete domain
     of booleans and the exponential in PLT.
  *)
Fixpoint tydom (τ:ty) : PLT :=
  match τ with
  | ty_bool => disc finbool
  | ty_unit => PLT.unit _
  | ty_prod τ₁ τ₂ => PLT.prod (tydom τ₁) (tydom τ₂)
  | ty_arrow τ₁ τ₂ => PLT.exp (tydom τ₁) (tydom τ₂)
  end.

(**  The denotation of terms is given by a simple fixpoint on term structure.
     The denotation of each combinator is a straightforward interpretation of the
     usual lambda term into the operations of a cartesian closed category.
  *)
Fixpoint denote (τ₁ τ₂:ty) (m:term τ₁ τ₂) : tydom τ₁ → tydom τ₂ :=
  match m in term τ₁ τ₂ return tydom τ₁ → tydom τ₂ with

  | tbool σ b => disc_elem b ∘ PLT.terminate false (tydom σ)

  | tterminate σ => PLT.terminate false (tydom σ)

  | tident σ => id(tydom σ)

  | tcompose σ₁ σ₂ σ₃ m₁ m₂ => denote σ₂ σ₃ m₁ ∘ denote σ₁ σ₂ m₂

  | tpair σ₁ σ₂ σ₃ m₁ m₂ => PLT.pair (denote σ₁ σ₂ m₁) (denote σ₁ σ₃ m₂)

  | tpi1 σ₁ σ₂ => PLT.pi1

  | tpi2 σ₁ σ₂ => PLT.pi2

  | tapp σ₁ σ₂ => PLT.app

  | tcurry σ₁ σ₂ σ₃ m => PLT.curry (denote (σ₁ × σ₂) σ₃ m)

  | tif σ₁ σ₂ th el => PLT.curry 
        (disc_cases (fun b:bool => if b then denote σ₁ σ₂ th else denote σ₁ σ₂ el))
  end.


(**  The operational semantics is given in a big-step style, with the specification
     of redexes split out into a separate relation.
  *)

Inductive redex : forall σ₁ σ₂ σ₃, term σ₂ σ₃ -> term σ₁ σ₂ -> term σ₁ σ₃ -> Prop :=
  | redex_pi1 : forall σ₁ σ₂ σ₃ x y,
                  redex _ _ _ (tpi1 σ₁ σ₂) (tpair σ₃ σ₁ σ₂ x y) x

  | redex_pi2 : forall σ₁ σ₂ σ₃ x y,
                  redex _ _ _ (tpi2 σ₁ σ₂) (tpair σ₃ σ₁ σ₂ x y) y

  | redex_bool : forall σ₁ σ₂ x b,
                  redex σ₁ σ₂ ty_bool (tbool _ b) x (tbool _ b)

  | redex_terminate : forall σ₁ σ₂ (x:term σ₁ σ₂),
                  redex _ _ _ (tterminate _) x (tterminate _)

  | redex_ident : forall σ₁ σ₂ (x:term σ₁ σ₂),
                  redex _ _ _ (tident _) x x

  | redex_compose : forall σ₁ σ₂ σ₃ σ₄ x y (z:term σ₄ σ₁),
                  redex _ _ _ (tcompose σ₁ σ₂ σ₃ x y) z 
                              (tcompose _ _ _ x (tcompose _ _ _ y z))

  | redex_beta : forall σ₁ σ₂ σ₃ (f:term (σ₁ × σ₂) σ₃) (g:term σ₁ σ₂),
                  redex _ _ _ (tapp _ _)
                              (tpair _ _ _ (tcurry _ _ _ f) g)
                              (tcompose _ _ _ f (tpair _ _ _ (tident _) g))

  | redex_iftrue : forall σ₁ σ₂ th el,
                  redex _ _ _ (tapp _ _)
                              (tpair _ _ _ (tif σ₁ σ₂ th el) (tbool _ true))
                              th
  
  | redex_iffalse : forall σ₁ σ₂ th el,
                  redex _ _ _ (tapp _ _)
                              (tpair _ _ _ (tif σ₁ σ₂ th el) (tbool _ false))
                              el

  | redex_curry : forall σ₁ σ₂ σ₃ σ₄ (f:term (σ₁×σ₂) σ₃) (g:term σ₄ σ₁),
                  redex _ _ _ (tcurry _ _ _ f) g
                              (tcurry _ _ _ (tcompose _ _ _ f 
                                (tpair _ _ _ (tcompose _ _ _ g (tpi1 _ _)) (tpi2 _ _))))
  .

(*
  | redex_if_true : forall σ₁ σ₂ σ₃ th el (g:term σ₃ σ₁),
                  redex _ _ _ (tif σ₁ σ₂ th el)
                              (tpair _ _ _ g (tbool _ true))
                              (tcompose _ _ _ th g)

  | redex_if_false : forall σ₁ σ₂ σ₃ th el (g:term σ₃ σ₁),
                  redex _ _ _ (tif σ₁ σ₂ th el)
                              (tpair _ _ _ g (tbool _ false))
                              (tcompose _ _ _ el g).
*)
Inductive eval : forall τ₁ τ₂, term τ₁ τ₂ -> term τ₁ τ₂ -> Prop :=
  | ebool : forall σ b, eval σ ty_bool (tbool σ b) (tbool _ b)
  | epi1 : forall σ₁ σ₂, eval _ _ (tpi1 σ₁ σ₂) (tpi1 _ _)
  | epi2 : forall σ₁ σ₂, eval _ _ (tpi2 σ₁ σ₂) (tpi2 _ _)
  | eterminate : forall σ, eval _ _ (tterminate σ) (tterminate σ)
  | eident : forall σ, eval _ _ (tident σ) (tident _)
  | eif : forall σ₁ σ₂ th el, eval _ _ (tif σ₁ σ₂ th el) (tif _ _ th el)
  | ecurry : forall σ₁ σ₂ σ₃ m, eval _ _ (tcurry σ₁ σ₂ σ₃ m) (tcurry _ _ _ m)
  | eapp : forall σ₁ σ₂, eval _ _ (tapp σ₁ σ₂) (tapp σ₁ σ₂)
  | epair : forall σ₁ σ₂ σ₃ x y x' y',
         eval _ _ x x' ->
         eval _ _ y y' ->
         eval _ _ (tpair σ₁ σ₂ σ₃ x y) (tpair _ _ _ x' y')
  | ecompose1 : forall σ₁ σ₂ σ₃ x y x' y' r z,
         eval σ₂ σ₃ x x' ->
         eval σ₁ σ₂ y y' ->
         redex σ₁ σ₂ σ₃ x' y' r ->
         eval σ₁ σ₃ r z ->
         eval σ₁ σ₃ (tcompose σ₁ σ₂ σ₃ x y) z
  | ecompose2 : forall σ₁ σ₂ σ₃ x y x' y',
         eval σ₂ σ₃ x x' ->
         eval σ₁ σ₂ y y' ->
         (~exists r, redex σ₁ σ₂ σ₃ x' y' r) ->
         eval σ₁ σ₃ (tcompose σ₁ σ₂ σ₃ x y) (tcompose σ₁ σ₂ σ₃ x' y')
  .


(* FIXME: move to profinite.v *)
Lemma plt_terminate_univ : forall (A:PLT) (f:A → PLT.unit false),
  f ≈ PLT.terminate false A.
Proof.
  intros. split.
  apply PLT.terminate_le_univ.
  hnf; simpl; intros.
  destruct a.
  destruct u.
  destruct (PLT.hom_directed false _ _ f c nil); auto.
  hnf; auto. hnf; intros. apply nil_elem in H0. elim H0.
  destruct H0. apply erel_image_elem in H1. destruct x. auto.
Qed.

(*FIXME: move to discrete.v *)
Lemma disc_cases_elem'
     : forall (X : fintype) (A B C : PLT) 
       (f : X -> A → B) (g: C → PLT.unit false) (x : X) (h : C → A),
       disc_cases f ∘ PLT.pair h (disc_elem x ∘ g) ≈ f x ∘ h.
Proof.
  split; intros a H. destruct a.
  apply compose_hom_rel in H.
  apply compose_hom_rel.
  destruct H as [q [??]].
  destruct q.
  apply (mk_disc_cases_elem X _ _ f (fintype.fintype_list X)) in H0.
  simpl in H.
  rewrite (pair_rel_elem _ _ _ _ _ _ c c1 c2) in H. destruct H.
  apply compose_elem in H1.  2: apply (PLT.hom_order _ _ _ g).
  simpl in *.
  destruct H1 as [q [??]].
  apply single_axiom in H2.
  exists c1. split; auto.
  destruct H2 as [[??][??]]. simpl in *.
  hnf in H3. subst c2. auto.
  apply fintype.fintype_complete.
  destruct a.
  apply compose_hom_rel in H.
  apply compose_hom_rel.
  destruct H as [q [??]].
  exists (q,x). split.
  apply pair_rel_elem. split; auto.
  apply compose_hom_rel.
  exists tt.
  split.
  destruct (PLT.hom_directed false _ _ g c nil); auto.
  hnf; auto. hnf; intros. apply nil_elem in H1. elim H1.
  destruct H1. apply erel_image_elem in H2. destruct x0. auto.
  simpl. apply single_axiom. auto.
  apply (mk_disc_cases_elem X _ _ f (fintype.fintype_list X)).
  apply fintype.fintype_complete.
  auto.   
Qed.

(**  Every redex preserves the meaning of terms. *)
Lemma redex_soundness : forall σ₁ σ₂ σ₃ x y z,
  redex σ₁ σ₂ σ₃ x y z ->
  denote _ _ x ∘ denote _ _ y ≈ denote _ _ z.
Proof.
  intros. case H; simpl.

  intros. rewrite pair_commute1. auto.
  intros. rewrite pair_commute2. auto.
  intros. rewrite <- (cat_assoc _ _ _ _ _ (disc_elem b)).
  apply cat_respects; auto. apply plt_terminate_univ.
  intros. apply plt_terminate_univ.
  intros. apply cat_ident2.
  intros. symmetry. apply cat_assoc.
  intros. rewrite PLT.curry_apply2; auto.
  intros. rewrite PLT.curry_apply2; auto.
  rewrite disc_cases_elem'.
  apply cat_ident1.
  intros. rewrite PLT.curry_apply2; auto.
  rewrite disc_cases_elem'.
  apply cat_ident1.
  intros. rewrite PLT.curry_compose_commute.
  apply PLT.curry_eq.
  apply cat_respects; auto.
  unfold PLT.pair_map.
  apply PLT.pair_eq; auto.
  apply cat_ident2.
Qed.

(**  Evaluation preserves the denotation of terms. *)
Theorem soundness : forall τ₁ τ₂ (m z:term τ₁ τ₂),
  eval τ₁ τ₂ m z -> denote τ₁ τ₂ m ≈ denote τ₁ τ₂ z.
Proof.
  intros. induction H; simpl; auto.
  rewrite IHeval1.
  rewrite IHeval2.
  auto.
  rewrite IHeval1.
  rewrite IHeval2.
  rewrite <- IHeval3.
  apply redex_soundness. auto.
  rewrite IHeval1.
  rewrite IHeval2.
  auto.
Qed.


Notation synapp a b := (tcompose _ _ _ (tapp _ _) (tpair _ _ _ a b)).
Notation semapp a b := (PLT.app ∘ (PLT.pair a b)).

(**  Now we define the logical relation.  It is defined by induction
     on the structure of types, in a standard way.
  *)
Fixpoint LR Γ (τ₂:ty) : term Γ τ₂ -> (tydom Γ → tydom τ₂) -> Prop :=
  match τ₂ as τ' return term Γ τ' -> (tydom Γ → tydom τ') -> Prop
  with

  | ty_unit => fun m h => True

  | ty_bool => fun m h => denote _ _ m ≈ h

  | ty_prod σ₁ σ₂ => fun m h =>
            LR Γ σ₁ (tcompose _ _ _ (tpi1 _ _) m) (PLT.pi1 ∘ h) /\
            LR Γ σ₂ (tcompose _ _ _ (tpi2 _ _) m) (PLT.pi2 ∘ h)

  | ty_arrow σ₁ σ₂ => fun m h =>
        forall n h',
          LR Γ σ₁ n h' -> eval _ σ₁ n n ->
          exists z, 
            eval Γ σ₂ (synapp m n) z /\
            LR Γ σ₂ z (semapp h h')
  end.

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

  

(**  Now we move on to the more difficult adequacy proof.
     For this we will first need a variety of technical results
     about the operational semantics.
  *)

Lemma eval_value τ₁ τ₂ x y :
  eval τ₁ τ₂ x y -> eval τ₁ τ₂ y y.
Proof.
  intro H. induction H; try (constructor; fail); auto.
  apply epair; auto.
  apply ecompose2; auto.
Qed.


Lemma redex_eq τ₁ τ₂ τ₃ x y z1 z2 :
  redex τ₁ τ₂ τ₃ x y z1 ->
  redex τ₁ τ₂ τ₃ x y z2 ->
  z1 = z2.
Proof.
  intros; inv H; inv H0; auto.
  inv H; auto.
Qed.

Lemma eval_eq τ₁ τ₂ x y1 y2 :
  eval τ₁ τ₂ x y1 -> eval τ₁ τ₂ x y2 -> y1 = y2.
Proof.
  intro H. revert y2.
  induction H.

  intros. inv H. auto.
  intros. inv H. auto.
  intros. inv H. auto.
  intros. inv H. auto.
  intros. inv H. auto.
  intros. inv H. auto.
  intros. inv H. auto.

  intros. inversion H.
  subst. inj_ty. auto.

  intros. inv H1.
  apply IHeval1 in H6.
  apply IHeval2 in H9.
  subst y'0 x'0.
  auto.

  intros. inv H3.
  apply IHeval1 in H10.
  apply IHeval2 in H11.
  subst y'0 x'0.
  assert (r = r0).
  eapply redex_eq; eauto.
  subst r0.
  apply IHeval3; auto.

  apply IHeval1 in H10.
  apply IHeval2 in H11.
  subst y'0 x'0.
  elim H12; eauto.

  intros. inv H2.
  apply IHeval1 in H9.
  apply IHeval2 in H10.
  subst y'0 x'0.
  elim H1. eauto.
  f_equal; auto.
Qed.

Lemma eval_trans τ₁ τ₂ x y z :
  eval τ₁ τ₂ x y -> eval τ₁ τ₂ y z -> eval τ₁ τ₂ x z.
Proof.
  intros.
  replace z with y; auto.
  eapply eval_eq with y; auto.
  eapply eval_value; eauto.
Qed.


Lemma eval_app_congruence σ₁ σ₂ σ₃ : forall x x' y y' z,
  (forall q, eval _ _ x q -> eval _ _ x' q) ->
  (forall q, eval _ _ y q -> eval _ _ y' q) ->
  eval _ _ (tcompose σ₁ σ₂ σ₃ x y) z ->
  eval _ _ (tcompose σ₁ σ₂ σ₃ x' y') z.
Proof.
  intros.
  inv H1.
  apply H in H8.
  apply H0 in H9.
  eapply ecompose1; eauto.
  apply ecompose2; eauto.
Qed.

Lemma eval_redex_walk : forall t1 t2 t3 x y z q,
  redex t1 t2 t3 x y z ->
  eval _ _ x x ->
  eval _ _ y y ->
  eval _ _ (tcompose _ _ _ x y) q ->
  eval _ _ z q.
Proof.
  intros.
  inv H2.
  assert (x = x'). eapply eval_eq; eauto.
  assert (y = y'). eapply eval_eq; eauto.
  subst x' y'.
  assert (r = z). eapply redex_eq; eauto.
  subst r. auto.
  assert (x = x'). eapply eval_eq; eauto.
  assert (y = y'). eapply eval_eq; eauto.
  subst x' y'.
  elim H11. eauto.
Qed.


Lemma LR_equiv τ : forall Γ m h h',
  h ≈ h' -> LR Γ τ m h -> LR Γ τ m h'.
Proof.
  induction τ; simpl. intros.
  intuition. rewrite <- H; auto.
  simpl; intuition.
  simpl; intuition.
  revert H1. apply IHτ1.
  apply cat_respects; auto.
  revert H2. apply IHτ2.
  apply cat_respects; auto.
  
  simpl; intros; auto.
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

Fixpoint lrtys (z:ty) (ts:list ty) :=
  match ts with
  | nil => z
  | t::ts' => t ⇒ (lrtys z ts')
  end.

Fixpoint lrsyn Γ (ts:list ty) : Type :=
  match ts with
  | nil => unit
  | t::ts' => prod (lrsyn Γ ts') (term Γ t)
  end.

Fixpoint lrsem Γ (ts:list ty) : Type :=
  match ts with
  | nil => unit
  | t::ts' => prod (lrsem Γ ts') (tydom Γ → tydom t)
  end.

Fixpoint lrhyps Γ (ls:list ty) : lrsyn Γ ls -> lrsem Γ ls -> Prop :=
  match ls as ls' return lrsyn Γ ls' -> lrsem Γ ls' -> Prop with
  | nil => fun _ _ => True
  | t::ts => fun xs ys =>
      eval _ _ (snd xs) (snd xs) /\
      LR Γ _ (snd xs) (snd ys) /\
      lrhyps Γ ts (fst xs) (fst ys)
  end.

Fixpoint lrapp Γ σ (ls:list ty) : term Γ (lrtys σ ls) -> lrsyn Γ ls -> term Γ σ :=
  match ls as ls' return 
    term Γ (lrtys σ ls') -> lrsyn Γ ls' -> term Γ σ
  with
  | nil => fun m _ => m
  | t::ts => fun m xs => lrapp Γ σ ts (synapp m (snd xs)) (fst xs)
  end.

Fixpoint lrsemapp Γ σ (ls:list ty) :
  (tydom Γ → tydom (lrtys σ ls)) -> lrsem Γ ls -> (tydom Γ → tydom σ) :=
  match ls as ls' return
    (tydom Γ → tydom (lrtys σ ls')) -> lrsem Γ ls' -> (tydom Γ → tydom σ)
  with
  | nil => fun h _ => h
  | t::ts => fun h ys => lrsemapp Γ σ ts (semapp h (snd ys)) (fst ys)
  end.

Lemma eval_lrapp_congruence ls : forall Γ τ xs m m' z,
  (forall q, eval _ _ m q -> eval _ _ m' q) ->
  eval _ _ (lrapp Γ τ ls m xs) z ->
  eval _ _ (lrapp Γ τ ls m' xs) z.
Proof.
  induction ls; simpl; intros.
  apply H. auto.

  revert H0. apply IHls.
  intros.
  inv H0; fold lrtys in *.
  eapply ecompose1; eauto.
  inv H8. apply epair; auto.
  eapply ecompose2; eauto.
  inv H8. apply epair; auto.
Qed.

Lemma lrsemapp_equiv ls : forall Γ τ ys h h',
  h ≈ h' -> lrsemapp Γ τ ls h ys ≈ lrsemapp Γ τ ls h' ys.
Proof.
  induction ls; simpl; intros; auto.
  apply IHls.
  apply cat_respects; auto.
  apply PLT.pair_eq; auto.  
Qed.

(**  The main logical relations lemma.  In order to make the induction
     function properly, we have to play some games with equality coercions :-(

     We work through the issues that arise via liberal application of the
     Eqdep_dec.UIP_dec lemma, which applies to types with decidable equality.
  *)
Lemma LRok : forall Γ σ (n:term Γ σ) (ls:list ty) τ (m:term Γ (lrtys τ ls)) xs ys
  (Hσ : σ = lrtys τ ls),
  eq_rect σ (fun a => term Γ a) n (lrtys τ ls) Hσ = m ->
  lrhyps Γ ls xs ys ->
  exists z,
    eval Γ τ (lrapp Γ τ ls m xs) z /\
    LR Γ τ z (lrsemapp Γ τ ls (denote _ _ m) ys).
Proof.
  induction n; intros.

admit.
admit.
admit.
admit.

  subst. simpl in *.



(**  Now we define contextual equivalance.  Contexts here are
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
  | cxt_top => fun x => x
  | cxt_appl σ₁ σ₂ t C' => fun x => plug τ _ C' (tapp x t)
  | cxt_appr σ₁ σ₂ t C' => fun x => plug τ _ C' (tapp t x)
  end.

Definition cxt_eq τ σ (m n:term σ):=
  forall (C:context τ σ) (z:term τ),
    eval τ (plug τ σ C m) z <-> eval τ (plug τ σ C n) z.

(**  Adequacy means that terms with equivalant denotations
     are contextually equivalant in any boolean context.
  *)
Theorem adequacy : forall τ (m n:term τ),
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

(**  As a corollary of the logical relations lemma, we learn that
     the calculus is strongly normalizing.
  *)
Corollary normalizing : forall τ (m:term τ), exists z, eval τ m z.
Proof.
  intros.
  generalize (LRok τ m nil τ m tt tt (Logic.refl_equal _) (Logic.refl_equal _) I).
  simpl. intros [z [??]]. exists z; auto.
Qed.

(** These should print "Closed under the global context", meaning these
    theorems hold without the use of any axioms.
  *)
Print Assumptions adequacy.
Print Assumptions normalizing.
