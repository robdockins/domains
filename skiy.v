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
Require Import profinite_adj.

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

Parameter flat : Type -> ∂PLT.
Parameter flat_elem : forall (X:Type), X -> PLT.unit true → flat X.
Parameter flat_cases : forall (X:Type) (A B:∂PLT) (f:X -> A → B), PLT.prod A (flat X) → B.
Arguments flat_elem [X] x.
Arguments flat_cases [X A B] f.

Definition lift (X:PLT) : PLT := U (L X).
Definition colift (X:∂PLT) : ∂PLT := L (U X).

Fixpoint tydom (τ:ty) : ob ∂PLT :=
  match τ with
  | ty_bool => flat bool
  | ty_arrow τ₁ τ₂ => colift (PLT.exp (tydom τ₁) (tydom τ₂))
  end.

Notation up f := (L@(U@f) ∘ adj_counit_inv_hom _) (only parsing).
Notation pi1 := PLT.pi1.
Notation pi2 := PLT.pi2.
Notation ε := (adj_counit _).
Notation η := (adj_unit _).
Notation γ := (adj_counit_inv_hom _).
Arguments PLT.pair_map [hf] [A B C D] f g.
Notation "A × B" := (@PLT.prod false A B).
Notation "A ⊗ B" := (@PLT.prod true A B)
   (at level 54, right associativity).
Notation "A ⊸ B" := (@PLT.exp true A B)
   (at level 50, left associativity).
Notation "A ⇒ B" := (@PLT.exp false A B).

Definition strict_app (Γ:PLT) (A B:∂PLT) 
  : U (A ⊸ B) × U A → U B

  := U@( @PLT.app _ A B ∘ PLT.pair_map ε ε ∘ lift_prod' _ _) ∘ η.

Definition strict_curry (Γ:PLT) (A B:∂PLT)
  (f:Γ×U A → U B) : Γ → U (A ⊸ B) 

  := U@( PLT.curry( ε ∘ L@f ∘ lift_prod _ _ ∘ PLT.pair_map id γ) ) ∘ η.
  
Definition strict_app' (Γ:PLT) (A B:∂PLT) 
  : U (colift (A ⊸ B)) × U A → U B 

  := strict_app Γ A B ∘ PLT.pair_map (U@ε) id.

Definition strict_curry' (Γ:PLT) (A B:∂PLT)
  (f:Γ × U A → U B) : Γ → U (colift (A ⊸ B))

  := η ∘ strict_curry Γ A B f.

Opaque liftPPLT.
Opaque forgetPLT.

Definition semvalue (Γ:PLT) (A:∂PLT) (f:Γ → U A) :=
  forall g, exists a, (g,Some a) ∈ PLT.hom_rel f.
Arguments semvalue [Γ A] f.

Lemma strict_curry_app (Γ:PLT) (A B:∂PLT) 
  (f : Γ×U A → U B) (g : Γ → U A) (Hg: semvalue g) :
  strict_app Γ A B ∘ PLT.pair (strict_curry Γ A B f) g ≈ f ∘ PLT.pair id g.
Proof.
  unfold strict_app, strict_curry.
  simpl.
  rewrite <- (cat_assoc PLT).
  rewrite (NT.axiom adj_unit
    (PLT.pair
          (U @
           PLT.curry
             (adj_counit_hom B ∘ L @ f ∘ lift_prod Γ (U A)
              ∘ PLT.pair_map id γ) ∘ adj_unit_hom Γ) g)).
  simpl.
  rewrite (cat_assoc PLT).
  rewrite <- (Functor.compose U). 2: reflexivity.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- lift_prod_pair'.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (PLT.pair_map_pair true).
  rewrite (Functor.compose L). 2: reflexivity.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (cat_assoc ∂PLT).
  generalize (NT.axiom adj_counit
    (PLT.curry (adj_counit_hom B
                ∘ (L @ f ∘ (lift_prod Γ (U A) ∘ PLT.pair_map id γ))))).
  simpl; intros.
  etransitivity.
  apply cat_respects. 2: reflexivity.
  apply (Functor.respects U).
  apply cat_respects. reflexivity.
  apply PLT.pair_eq. 2: reflexivity.
  rewrite (cat_assoc ∂PLT).
  apply cat_respects. 2: reflexivity.
  apply H. clear H.
  rewrite (cat_assoc ∂PLT).
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (cat_assoc ∂PLT).
  generalize (Adjunction.adjoint_axiom1 PLT_adjoint Γ).
  simpl. intros. rewrite H. clear H.
  rewrite (cat_ident1 ∂PLT).
  rewrite (PLT.curry_apply2 true).
  repeat rewrite <- (cat_assoc ∂PLT).
  rewrite <- (PLT.pair_map_pair true).
  assert (PLT.pair (id ∘ id)
             (adj_counit_inv_hom A ∘ (adj_counit_hom A ∘ forgetPLT @ g)) 
             ≈
          PLT.pair (forgetPLT@id) (forgetPLT @ g)).
  apply PLT.pair_eq.
  rewrite (Functor.ident forgetPLT); auto. apply cat_ident1.
  rewrite (cat_assoc ∂PLT).
  apply adj_inv_eq. auto.
  etransitivity.
  apply cat_respects. 2: reflexivity.
  apply Functor.respects.
  apply cat_respects. reflexivity.
  apply cat_respects. reflexivity.
  apply cat_respects. reflexivity. apply H.
  rewrite lift_prod_pair.
  rewrite <- (Functor.compose L). 2: reflexivity.
  rewrite (Functor.compose U). 2: reflexivity.
  rewrite <- (cat_assoc PLT).
  rewrite <- (NT.axiom adj_unit (f ∘ PLT.pair id g)). simpl.
  rewrite (cat_assoc PLT).
  generalize (Adjunction.adjoint_axiom2 PLT_adjoint B).
  simpl. intros. rewrite H0.
  apply cat_ident2.
Qed.  


Lemma strict_curry_app' (Γ:PLT) (A B:∂PLT) 
  (f : Γ×U A → U B) (g : Γ → U A)
  (Hg : forall a, exists b, (a,Some b) ∈ PLT.hom_rel g) :

  strict_app' Γ A B ∘ PLT.pair (strict_curry' Γ A B f) g ≈ f ∘ PLT.pair id g.
Proof.
  unfold strict_curry'.
  unfold strict_app'.
  rewrite <- (cat_assoc PLT).
  rewrite <- (PLT.pair_map_pair false).
  rewrite (cat_assoc PLT).
  rewrite (cat_ident2 PLT).
  generalize (Adjunction.adjoint_axiom2 PLT_adjoint (A ⊸ B)).
  intros. simpl in H. rewrite H.
  rewrite (cat_ident2 PLT).
  apply strict_curry_app. auto.
Qed.

Lemma plt_strict_compose : forall (A B C:∂PLT) (f:B → C),
  f ∘ (⊥: A → B) ≈ ⊥.
Proof.
  intros. split. 2: apply bottom_least.
  hnf. intros.
  destruct a. apply compose_hom_rel in H.
  destruct H as [y [??]].
  simpl in H.
  apply union_axiom in H. destruct H as [X[??]].
  apply image_axiom2 in H. destruct H as [q [??]].
  apply empty_elem in H. elim H.
Qed.


Lemma strict_app_bot (Γ:PLT) (A B:∂PLT) (f:Γ → U (A ⊸ B)) :
  strict_app Γ A B ∘ PLT.pair f ⊥ ≈ ⊥.
Proof.
  unfold strict_app. simpl.
  rewrite <- (cat_assoc PLT).

  generalize (NT.axiom adj_unit). simpl; intros.
  rewrite H.
  rewrite (cat_assoc PLT).
  rewrite <- (Functor.compose U). 2: reflexivity.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- lift_prod_pair'.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (PLT.pair_map_pair true).
  etransitivity.
  apply cat_respects. 2: reflexivity.
  apply Functor.respects.
  etransitivity.
  apply cat_respects. reflexivity.
  2: apply plt_strict_compose.
  etransitivity.
  apply PLT.pair_eq. reflexivity.
  2: apply PPLT.pair_bot1.
  generalize (NT.axiom adj_counit). simpl; intros.
  rewrite (Functor.compose L). 2: reflexivity.
  rewrite (cat_assoc ∂PLT).
  rewrite H0. 
  rewrite <- (cat_assoc ∂PLT).
  generalize (Adjunction.adjoint_axiom1 PLT_adjoint Γ).
  intros. simpl in H1. rewrite H1.
  apply cat_ident1.
  auto.
Qed.

Lemma strict_app_bot' (Γ:PLT) (A B:∂PLT) (f:Γ → U (colift (A ⊸ B))) :
  strict_app' Γ A B ∘ PLT.pair f ⊥ ≈ ⊥.
Proof.
  unfold strict_app'.
  rewrite <- (cat_assoc PLT).
  rewrite <- (PLT.pair_map_pair false).
  rewrite (cat_ident2 PLT).
  apply strict_app_bot.
Qed.



Lemma curry_app' (Γ:PLT) (A B:∂PLT) (f:PLT.prod Γ (liftPPLT A) → liftPPLT B)
  (g : Γ → liftPPLT A)
  (Hg : forall a, exists b, (a,Some b) ∈ PLT.hom_rel g) :
  app' Γ A B ∘ PLT.pair (curry' Γ A B f) g ≈ f ∘ PLT.pair id(Γ) g.
Proof.
  unfold curry'.
  unfold app'. 
  simpl.
  rewrite <- (cat_assoc PLT).
  rewrite <- (cat_assoc PLT).
  rewrite (NT.axiom adj_unit
  (PLT.pair
          (adj_unit_hom (liftPPLT (PLT.exp A B))
           ∘ (liftPPLT @
              PLT.curry
                (adj_counit_hom B ∘ forgetPLT @ f ∘ lift_prod Γ (liftPPLT A)
                 ∘ PLT.pair_map true (id) (adj_counit_inv_hom A))
              ∘ adj_unit_hom Γ)) g)).
  simpl.
  rewrite (cat_assoc PLT).
  rewrite <- (Functor.compose liftPPLT). 2: reflexivity.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- lift_prod_pair'.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (PLT.pair_map_pair true).
  rewrite (Functor.compose forgetPLT). 2: reflexivity.
  rewrite <- (cat_assoc ∂PLT).
  rewrite (cat_assoc ∂PLT _ _ _ _
    (adj_counit_hom (colift (PLT.exp A B)))).
  generalize (Adjunction.adjoint_axiom1 PLT_adjoint (liftPPLT (PLT.exp A B))).
  intros. simpl in H.
  unfold colift.
  rewrite H. clear H.
  rewrite (cat_ident2 ∂PLT).
  rewrite (Functor.compose forgetPLT). 2: reflexivity.
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (cat_assoc ∂PLT).
  generalize (NT.axiom adj_counit
    (PLT.curry
              (adj_counit_hom B
               ∘ (forgetPLT @ f
                  ∘ (lift_prod Γ (liftPPLT A)
                     ∘ PLT.pair_map true (id) (adj_counit_inv_hom A)))))).
  simpl. intros.
  etransitivity.
  apply cat_respects. 2: reflexivity.
  apply (Functor.respects liftPPLT).
  apply cat_respects. reflexivity.
  apply PLT.pair_eq. 2: reflexivity.
  rewrite (cat_assoc ∂PLT).
  apply cat_respects. 2: reflexivity.
  apply H. clear H.
  rewrite (cat_assoc ∂PLT).
  rewrite <- (cat_assoc ∂PLT).
  rewrite <- (cat_assoc ∂PLT).
  generalize (Adjunction.adjoint_axiom1 PLT_adjoint Γ).
  simpl. intros. rewrite H. clear H.
  rewrite (cat_ident1 ∂PLT).
  rewrite (PLT.curry_apply2 true).
  repeat rewrite <- (cat_assoc ∂PLT).
  rewrite <- (PLT.pair_map_pair true).
  assert (PLT.pair (id ∘ id)
             (adj_counit_inv_hom A ∘ (adj_counit_hom A ∘ forgetPLT @ g)) 
             ≈
          PLT.pair (forgetPLT@id) (forgetPLT @ g)).
  apply PLT.pair_eq.
  rewrite (Functor.ident forgetPLT); auto. apply cat_ident1.
  rewrite (cat_assoc ∂PLT).
  apply adj_inv_eq. auto.
  etransitivity.
  apply cat_respects. 2: reflexivity.
  apply Functor.respects.
  apply cat_respects. reflexivity.
  apply cat_respects. reflexivity.
  apply cat_respects. reflexivity. apply H.
  rewrite lift_prod_pair.
  rewrite <- (Functor.compose forgetPLT). 2: reflexivity.
  rewrite (Functor.compose liftPPLT). 2: reflexivity.
  rewrite <- (cat_assoc PLT).
  rewrite <- (NT.axiom adj_unit (f ∘ PLT.pair id g)). simpl.
  rewrite (cat_assoc PLT).
  generalize (Adjunction.adjoint_axiom2 PLT_adjoint B).
  simpl. intros. rewrite H0.
  apply cat_ident2.
Qed.  


(****)
Definition curry (C A B:∂PLT) (f:PLT.prod C A → B)
  := up (PLT.curry f).

Definition app (C A B:∂PLT) (f:C → colift (PLT.exp A B)) (x:C → A)
  := PLT.app ∘ PLT.pair (adj_counit_hom _ ∘ f) x.

Arguments curry [C A B] f.
Arguments app [C A B] f x.

Require Import Setoid.

Add Parametric Morphism (C A B:∂PLT) :
  (@app C A B)
    with signature (eq_op _) ==> (eq_op _) ==> (eq_op _)
    as app_morphism.
Proof.
  intros. unfold app.
  rewrite H. rewrite H0. auto.
Qed.

Add Parametric Morphism (C A B:∂PLT) :
  (@curry C A B)
    with signature (eq_op _) ==> (eq_op _)
    as curry_morphism.
Proof.
  unfold curry; intros.
  rewrite H. auto.
Qed.

Lemma curry_app_commute (C A B:∂PLT) (f:PLT.prod C A → B) (x:C → A) :
  app (curry f) x ≈ f ∘ PLT.pair id x.
Proof.
  unfold app, curry.
  rewrite (cat_assoc _ _ _ _ _ (adj_counit_hom (PLT.exp A B))).
  rewrite (NT.axiom adj_counit (PLT.curry f)). simpl.
  rewrite <- (cat_assoc _ _ _ _ _ (PLT.curry f)).
  rewrite adj_counit_inv_eq.
  rewrite PLT.curry_apply3. auto.
Qed.

Lemma curry_app_commute2 (D C A B:∂PLT) (f:PLT.prod C A → B) (h:D → C) (x:D → A) :
  app (curry f ∘ h) x ≈ f ∘ PLT.pair h x.
Proof.
  unfold app, curry.
  rewrite (cat_assoc _ _ _ _ _ (adj_counit_hom (PLT.exp A B))).
  rewrite (cat_assoc _ _ _ _ _ (adj_counit_hom (PLT.exp A B))).
  rewrite (NT.axiom adj_counit (PLT.curry f)). simpl.
  rewrite <- (cat_assoc _ _ _ _ _ (PLT.curry f)).
  rewrite adj_counit_inv_eq. rewrite cat_ident1.
  rewrite PLT.curry_apply3. auto.
Qed.

Lemma app_compose_commute (A B C D:∂PLT)
    (f: C → colift (PLT.exp A B)) (g:C → A) (h:D → C) :
    app f g ∘ h ≈ app (f ∘ h) (g ∘ h).
Proof.
  unfold app.
  rewrite <- (cat_assoc ∂PLT).
  rewrite (PLT.pair_compose_commute true).
  rewrite <- (cat_assoc ∂PLT).
  auto.  
Qed.

Lemma lfp_bot : forall (X:cppo) (f:X → X),
  lfp f ≈ cpo.bot _.
Proof.
  intros. apply scott_induction.
  intros.
  split. apply CPO.sup_is_least.
  hnf; simpl; intros.
  rewrite (H x); auto.
  apply cpo.bot_least.
  intros. rewrite <- H; auto.
  intros.
  rewrite H. apply strict_map.
Qed.

Definition fixes_step (Γ:PLT) (A:∂PLT)
  (f:Γ → (PLT.exp (liftPPLT A) (liftPPLT A)))
  (x:Γ → liftPPLT A) : Γ → liftPPLT A :=

  PLT.app ∘ PLT.pair f x.
  
Definition fixes_base (Γ:PLT) (A:∂PLT) :
  Γ → liftPPLT A := 

  liftPPLT@⊥ ∘ adj_unit _.
  
Lemma fixes_base_least Γ A h :
  fixes_base Γ A ≤ h.
Proof.
  unfold fixes_base.
  assert (⊥ ≤ adj_counit _ ∘ forgetPLT@h).
  apply bot_least.
  transitivity
    (liftPPLT@(adj_counit A ∘ forgetPLT@h) ∘ adj_unit Γ).
  apply PLT.compose_mono; auto.
  apply liftPPLT_mono. auto.
  rewrite Functor.compose. 2: reflexivity.
  rewrite <- (cat_assoc PLT).
  rewrite <- (NT.axiom adj_unit h).
  rewrite (cat_assoc PLT).
  rewrite (Adjunction.adjoint_axiom2 PLT_adjoint A).
  simpl. rewrite (cat_ident2 PLT); auto.
Qed.

Lemma fixes_step_mono Γ A f :
  forall x y, x ≤ y -> fixes_step Γ A f x ≤ fixes_step Γ A f y.
Proof.
  intros. unfold fixes_step.
  apply PLT.compose_mono.
  apply PLT.pair_monotone; auto.
  auto.
Qed.

Lemma fixes_step_base Γ A f :
  fixes_base Γ A ≤ fixes_step Γ A f (fixes_base Γ A).
Proof.
  apply fixes_base_least.
Qed.
  
Check (chain_sup).

Definition lfp' (Γ:PLT) (A:∂PLT) (f:Γ → PLT.exp (liftPPLT A) (liftPPLT A)) :=

  chain_sup false (PLT.homset_cpo false Γ (liftPPLT A)) 
    (fixes_base Γ A) (fixes_step Γ A f)
    (fixes_step_mono Γ A f)
    (fixes_step_base Γ A f).

Lemma scott_induction' (Γ:PLT) (A:∂PLT) f 
    (P: Γ → liftPPLT A -> Prop) :
    (forall XS:dirset (PLT.homset_cpo _ Γ (liftPPLT A)),
      (forall x, x ∈ XS -> P x) -> P (∐XS)) ->
    (forall x y, x ≈ y -> P x -> P y) ->
    (P (fixes_base Γ A)) ->
    (forall x, P x -> P (fixes_step Γ A f x)) ->
    P (lfp' Γ A f).
Proof.
  intros. unfold lfp'. apply chain_induction; auto.
Qed.

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

(*
Lemma upapp_ext (Γ:PLT) A B C (f f':C → colift (PLT.exp A B)) :
  (forall x, app f x ≤ app f' x) -> f ≤ f'.
Proof.  
  intros.
  unfold colift in f, f'.
  cut (adj_counit _ ∘ f ≤ adj_counit _ ∘ f').
  repeat intro.
  destruct a. destruct c0.
  assert ((c,c0) ∈ PLT.hom_rel (adj_counit _ ∘ f)).
  apply compose_hom_rel.
  exists (Some c0). split; auto.
  simpl. apply adj_counit_rel_elem. auto.
  apply H0 in H2.
  apply compose_hom_rel in H2.
  destruct H2 as [q [??]].
  simpl in H3.
  apply adj_counit_rel_elem in H3.
  revert H2. apply PLT.hom_order; auto.
  
  destruct (PLT.hom_directed _ _ _ f' c nil).
  

  apply exp_le_extensional'. intros.
  apply H.
Qed.

Check (adj_counit _ ∘ f).

Qed.
*)

Lemma currypi2_id : forall (A:PLT),
  PLT.curry (PLT.app ∘ PLT.pair pi1 pi2) ≈ id(PLT.exp A A).
Proof.
  intros. symmetry.
  apply PLT.curry_universal.
  unfold PLT.pair_map. 
  rewrite (cat_ident2 PLT).
  rewrite (cat_ident2 PLT).
  auto.
Qed.  

Lemma curry_asdf : forall (C A B:PLT) (f:C → PLT.exp A B),
  PLT.curry (PLT.app ∘ PLT.pair (f ∘ pi1) pi2) ≈ f.
Proof.
  intros. symmetry.
  apply PLT.curry_universal.
  unfold PLT.pair_map. 
  rewrite (cat_ident2 PLT).
  auto.
Qed.  

(*
Lemma curry_asdf' : forall (C A B:∂PLT) (f:C → PLT.exp A B),
  PLT.curry (PLT.app ∘ PLT.pair (f ∘ pi1) pi2) ≈ f.
Proof.
  intros. symmetry.
  apply PLT.curry_universal.
  unfold PLT.pair_map. 
  rewrite (cat_ident2 ∂PLT).
  auto.
Qed.  

Lemma adj_counit_inv_push X Y (f:lift X → Y) : 
  forgetPLT@f ∘ adj_counit_inv_hom (forgetPLT X) ≈ forgetPLT@(f ∘ adj_unit_hom X).
Admitted.
  idtac.
  unfold colift.
  rewrite adj_counit_inv_push.
  rewrite (H X).
  apply Functor.ident. auto.
Qed.
*)


Definition fixes''' σ₁ σ₂ :
  liftPPLT (PLT.exp (tydom (σ₁ ⇒ σ₂)) (tydom (σ₁ ⇒ σ₂)))
  →
  PLT.exp (liftPPLT (PLT.exp (tydom σ₁) (tydom σ₂)))
          (liftPPLT (PLT.exp (tydom σ₁) (tydom σ₂)))

  := PLT.curry (liftPPLT@(adj_counit _ ∘ PLT.app ∘ PLT.pair_map true (id) (adj_counit_inv_hom _)) 
                ∘ push_prod _ _).

Definition fixes' σ₁ σ₂ :
  liftPPLT (PLT.exp (tydom (σ₁ ⇒ σ₂)) (tydom (σ₁ ⇒ σ₂)))
  →
  liftPPLT (PLT.exp (tydom σ₁) (tydom σ₂))

  := lfp' (liftPPLT (PLT.exp (tydom (σ₁ ⇒ σ₂)) (tydom (σ₁ ⇒ σ₂))))
          _
          (fixes''' σ₁ σ₂).

Definition fixes σ₁ σ₂
  : tydom ((σ₁ ⇒ σ₂) ⇒ (σ₁ ⇒ σ₂)) → tydom (σ₁ ⇒ σ₂)

  := forgetPLT@(fixes' σ₁ σ₂).
  
Lemma up_antistrict (A B:∂PLT) (f:A → B) :
  PPLT.antistrict (up f).
Proof.
  repeat intro.
  exists None.
  apply compose_hom_rel.
  exists None.
  split. simpl.
  apply adj_unit_rel_elem. hnf. auto.
  simpl.
  apply liftPPLT_rel_elem. auto.
Qed.

Lemma curry_antistrict (C A B:∂PLT) (f:PLT.prod C A → B) :
  PPLT.antistrict (curry f).
Proof.
  unfold curry. apply up_antistrict.
Qed.
  
Fixpoint denote (τ:ty) (m:term τ) : PLT.unit true → tydom τ :=
  match m with
  | tbool b => flat_elem b
  | tapp σ₁ σ₂ m₁ m₂ => app (denote (σ₁ ⇒ σ₂) m₁) (denote σ₁ m₂)
  | tI σ => curry pi2
  | tK σ₁ σ₂ => curry (curry (pi2 ∘ pi1))
  | tS σ₁ σ₂ σ₃ => curry (curry (curry (
                     app 
                       (app (pi2 ∘ pi1 ∘ pi1) pi2)
                       (app (pi2 ∘ pi1) pi2)
                      )))
  | tIF σ => curry (flat_cases (fun b:bool =>
                 if b then curry (curry (pi2 ∘ pi1)) 
                      else curry (curry pi2)
             ))
  | tY σ₁ σ₂ => curry (fixes σ₁ σ₂ ∘ pi2)
  end.

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

Lemma redex_soundness : forall σ₁ σ₂ x y z,
  redex σ₁ σ₂ x y z ->
  app (denote _ x) (denote _ y) ≈ denote _ z.
Proof.
  intros. inv H.

  inv H. simpl.
  rewrite curry_app_commute.
  rewrite antistrict_pair_commute2'.

  rewrite pair_commute2.
  apply antistrict_id.

  simpl.
  rewrite curry_app_commute.
  rewrite curry_app_commute2.
  rewrite <- (cat_assoc (PLT.PLT true) _ _ _ _ PLT.pi2).
  rewrite antistrict_pair_commute1'.
  rewrite antistrict_pair_commute2'.
  auto.
  apply antistrict_id.
admit.
  simpl.
  rewrite curry_app_commute.
  rewrite curry_app_commute2.
  rewrite curry_app_commute2.
  rewrite app_compose_commute.
  apply app_morphism.
  rewrite app_compose_commute.
  apply app_morphism.
  repeat rewrite <- (cat_assoc (PLT.PLT true)).
  rewrite antistrict_pair_commute1'.
  rewrite antistrict_pair_commute1'.
  rewrite antistrict_pair_commute2'. auto.
  apply antistrict_id.

  auto. simpl in *.



Theorem antistrict_pair_commute1' (C A B:∂PLT) (f:C → A) (g:C → B) :
  PPLT.antistrict g -> PLT.pi1 ∘ PLT.pair f g ≈ f.
Proof.
  intros.
  apply PPLT.antistrict_pair_commute1. auto.
Qed.  

Theorem antistrict_pair_commute2' (C A B:∂PLT) (f:C → A) (g:C → B) :
  PPLT.antistrict f -> PLT.pi2 ∘ PLT.pair f g ≈ g.
Proof.
  intros. apply PPLT.antistrict_pair_commute2. auto.
Qed.  

Lemma antistrict_id (A:∂PLT) : PPLT.antistrict id(A).
Proof.
  repeat intro. exists a. simpl. apply ident_elem. auto.
Qed.


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

Lemma redex_soundness : forall σ₁ σ₂ x y z,
  value x ->
  value y ->
  redex σ₁ σ₂ x y z ->
  app (denote _ x) (denote _ y) ≈ denote _ z.
Proof.
  intros. inv H1.

  inv H1. simpl.
  rewrite curry_app_commute.
  apply antistrict_pair_commute2'.
  apply antistrict_id.

  simpl.
  rewrite curry_app_commute.
  rewrite curry_app_commute2.
  rewrite <- (cat_assoc (PLT.PLT true) _ _ _ _ PLT.pi2).
  rewrite antistrict_pair_commute1'.
  rewrite antistrict_pair_commute2'.
  auto.
  apply antistrict_id.
admit.
  simpl.
  rewrite curry_app_commute.
  rewrite curry_app_commute2.
  rewrite curry_app_commute2.
  rewrite app_compose_commute.
  apply app_morphism.
  rewrite app_compose_commute.
  apply app_morphism.
  repeat rewrite <- (cat_assoc (PLT.PLT true)).
  rewrite antistrict_pair_commute1'.
  rewrite antistrict_pair_commute1'.
  rewrite antistrict_pair_commute2'. auto.
  apply antistrict_id.

  auto. simpl in *.

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
