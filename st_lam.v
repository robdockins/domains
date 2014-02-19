(* Copyright (c) 2014, Robert Dockins *)

Require Import String.

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
(*Require Import finprod.*)

Require Import List.

Inductive ty :=
  | ty_nat 
  | ty_arrow : ty -> ty -> ty.

Delimit Scope ty_scope with ty.

Notation "x ⇒ y" := (ty_arrow x y) : ty_scope.

Definition env := list (atom * ty).

Fixpoint env_papp (p:perm) (Γ:env) :=
  match Γ with
  | nil => nil
  | (x,σ)::Γ' => (p x, σ)::env_papp p Γ'
  end.

Lemma env_papp_id Γ :
  env_papp id Γ = Γ.
Proof.
  induction Γ; simpl; auto.
  destruct a.
  f_equal. auto.
Qed.

Definition env_supp (Γ:env) := map (@fst atom ty) Γ.

Canonical Structure env_supported :=
  Supported env env_supp.

Section lookup.
  Variable I:Type.
  Variable Idec : forall (x y:I), {x=y}+{x<>y}.

  Variable A:Type.


  Fixpoint lookup (i:I) (l:list (I*A)) : option A :=
    match l with
    | nil => None
    | (i',a)::l' =>
         match Idec i i' with
         | left Hi => Some a
         | right _ => lookup i l'
         end
    end.

  Lemma lookup_app i l1 l2 :
    lookup i (l1++l2) =
    match lookup i l1 with
    | None => lookup i l2
    | Some a => Some a
    end.
  Proof.
    induction l1; simpl; auto.
    destruct a as [i' a].
    destruct (Idec i i'); auto.
  Qed.
End lookup.

Definition inenv (Γ:env) (x:atom) (σ:ty) :=
  lookup atom string_dec ty x Γ = Some σ.

Inductive rawterm : Type :=
  | rawvar : atom -> rawterm
  | rawnat : nat -> rawterm
  | rawapp : rawterm -> rawterm -> rawterm
  | rawlam : atom -> ty -> rawterm -> rawterm.

Inductive term (Γ:env) : ty -> Type :=
  | tvar : forall x σ,
                inenv Γ x σ ->
                term Γ σ
  | tnat : forall n:nat,
                term Γ ty_nat
  | tapp : forall σ₁ σ₂,
                term Γ (σ₁ ⇒ σ₂)%ty ->
                term Γ σ₁ ->
                term Γ σ₂
  | tlam : forall x σ₁ σ₂,
                term ((x,σ₁)::Γ) σ₂ ->
                term Γ (σ₁ ⇒ σ₂)%ty.
Arguments term Γ ty%ty.

Local Open Scope ty.


Definition concat A := fold_right (@app A) nil.

Notation "'fresh' '[' x , .. , z ']'" :=
  (fresh_atom (concat atom
   (cons (Support.support _ x) .. (cons (Support.support _ z) nil) ..))).
    
Canonical Structure atom_supp :=
  Supported atom (fun x => x::nil).

Lemma inenv_papp Γ x τ p :
  inenv Γ x τ ->
  inenv (env_papp p Γ) (p x) τ.
Proof.
  induction Γ; simpl; intros; auto.
  destruct a as [y a].
  unfold inenv in *.
  simpl in *.
  destruct (string_dec x y).
  subst x.
  destruct (string_dec (p y) (p y)).
  auto.
  elim n; auto.
  destruct (string_dec (p x) (p y)).
  apply Perm.f_inj in e. elim n; auto.
  apply IHΓ; auto.
Defined.

Fixpoint term_papp (p:perm) Γ τ (m:term Γ τ) : term (env_papp p Γ) τ :=
  match m with
  | tvar x σ H => tvar _ (p x) σ (inenv_papp Γ x σ p H)
  | tnat n => tnat _ n
  | tapp σ₁ σ₂ m1 m2 => tapp _ σ₁ σ₂ (term_papp p _ _ m1) (term_papp p _ _ m2)
  | tlam x σ₁ σ₂ m' => tlam _ (p x) σ₁ σ₂ (term_papp p _ _ m')
  end.

Inductive alpha_eq : forall Γ Γ' (ρ₁ ρ₂:perm) (τ:ty),
  term Γ τ -> term Γ' τ -> Prop :=

  | aeq_var : forall Γ Γ' (ρ₁ ρ₂:perm) τ x₁ x₂ H₁ H₂,
                  ρ₁ x₁ = ρ₂ x₂ ->
                  alpha_eq Γ Γ' ρ₁ ρ₂ τ (tvar Γ x₁ τ H₁) (tvar Γ' x₂ τ H₂)

  | aeq_nat : forall Γ Γ' ρ₁ ρ₂ n,
                  alpha_eq Γ Γ' ρ₁ ρ₂ ty_nat (tnat Γ n) (tnat Γ' n)

  | aeq_app : forall Γ Γ' ρ₁ ρ₂ σ₁ σ₂ m₁ m₂ n₁ n₂,
                  alpha_eq Γ Γ' ρ₁ ρ₂ (σ₁ ⇒ σ₂) m₁ n₁ ->
                  alpha_eq Γ Γ' ρ₁ ρ₂ σ₁ m₂ n₂ ->
                  alpha_eq Γ Γ' ρ₁ ρ₂ σ₂ (tapp Γ σ₁ σ₂ m₁ m₂) (tapp Γ' σ₁ σ₂ n₁ n₂)

  | aeq_lam : forall (Γ Γ':env) (ρ₁ ρ₂:perm) (x₁ x₂ x:atom) σ₁ σ₂ m₁ m₂,
                  x♯x₁ -> x♯x₂ -> x♯ρ₁ -> x♯ρ₂ -> x♯Γ -> x♯Γ' ->
                  alpha_eq ((x₁,σ₁)::Γ) ((x₂,σ₁)::Γ') (ρ₁ ∘ x ⇋ x₁) (ρ₂ ∘ x ⇋ x₂) σ₂ m₁ m₂ ->
                  alpha_eq Γ Γ' ρ₁ ρ₂ (σ₁ ⇒ σ₂) (tlam Γ x₁ σ₁ σ₂ m₁) (tlam Γ' x₂ σ₁ σ₂ m₂).

Fixpoint raw (Γ:env) (τ:ty) (m:term Γ τ) : rawterm :=
  match m with
  | tvar x _ _ => rawvar x
  | tnat n => rawnat n
  | tapp σ₁ σ₂ t1 t2 => rawapp (raw Γ (σ₁ ⇒ σ₂) t1) (raw Γ σ₁ t2)
  | tlam x σ₁ σ₂ m' => rawlam x σ₁ (raw ((x,σ₁)::Γ) σ₂ m')
  end.

Definition env_incl (Γ₁ Γ₂:env) :=
  forall x τ, inenv Γ₁ x τ -> inenv Γ₂ x τ.

Lemma env_incl_wk (Γ₁ Γ₂:env) y σ :
  env_incl Γ₁ Γ₂ ->
  env_incl ((y,σ)::Γ₁) ((y,σ)::Γ₂).
Proof.
  unfold env_incl. unfold inenv.
  simpl; repeat intro.
  destruct (string_dec x y); auto.
Qed.

Fixpoint term_wk (Γ₁ Γ₂:env) (σ:ty)
  (m:term Γ₁ σ) 
  (H:forall x τ, inenv Γ₁ x τ -> inenv Γ₂ x τ)
  : term Γ₂ σ :=

  match m with
  | tvar x σ IN => tvar Γ₂ x σ (H x σ IN)
  | tnat n => tnat Γ₂ n
  | tapp σ₁ σ₂ m₁ m₂ =>
        tapp Γ₂ σ₁ σ₂ (term_wk Γ₁ Γ₂ (σ₁ ⇒ σ₂) m₁ H) (term_wk Γ₁ Γ₂ σ₁ m₂ H)
  | tlam x σ₁ σ₂ m' =>
        tlam Γ₂ x σ₁ σ₂ 
            (term_wk ((x,σ₁)::Γ₁) ((x,σ₁)::Γ₂) σ₂ m'
              (env_incl_wk Γ₁ Γ₂ x σ₁ H))
  end.


Lemma weaken_fresh
  (Γ Γ' : env) (σ: ty) x' :
  x' ∉ ‖Γ‖ -> x' ∉ ‖Γ'‖ -> 
  forall (x : atom) (τ : ty),
    inenv Γ' x τ -> inenv ((x', σ) :: Γ') x τ.
Proof.
  intros.
  unfold inenv. simpl. intros.
  destruct (string_dec x x').
  assert (x' ∈ (‖Γ'‖)).
  rewrite <- e.
  revert H1. clear e. 
  induction Γ'; simpl in *; intuition.
  discriminate.
  destruct a. 
  hnf in H1. simpl in H1.
  destruct (string_dec x s).
  apply cons_elem; simpl; auto. left. subst s; auto.
  apply cons_elem; right; auto.
  apply IHΓ'.
  intro.
  apply H0.
  apply cons_elem. right; auto.
  auto.
  elim H0; auto.
  auto.
Qed.

Definition extend_map Γ Γ' 
  (VAR:forall a τ, inenv Γ a τ -> term Γ' τ)
  x σ (m:term Γ' σ) :
  forall a τ, inenv ((x,σ)::Γ) a τ -> term Γ' τ.
Proof.
  unfold inenv. simpl; intros.
  destruct (string_dec a x). subst a.
  injection H. intro. subst σ. exact m.
  exact (VAR a τ H).
Defined.

Definition weaken_map Γ Γ'
  (VAR:forall a τ, inenv Γ a τ -> term Γ' τ)
  x' σ (Hx1:x' ∉ ‖Γ‖) (Hx2:x' ∉ ‖Γ'‖) :
  (forall a τ, inenv Γ a τ -> term ((x',σ)::Γ') τ)

  := fun a τ H => 
       term_wk Γ' ((x', σ) :: Γ') τ (VAR a τ H) (weaken_fresh Γ Γ' σ x' Hx1 Hx2).

Program Definition newestvar Γ x σ : term ((x,σ)::Γ) σ := tvar _ x σ _.
Next Obligation.
  intros. hnf; simpl.
  destruct (string_dec x x); auto. elim n; auto.
Defined.

Definition shift_vars Γ Γ' x x' σ
  (Hx1:x' ∉ ‖Γ‖) (Hx2:x' ∉ ‖Γ'‖)
  (VAR:forall a τ, inenv Γ a τ -> term Γ' τ)
  : forall (a : atom) (τ : ty) (H:inenv ((x, σ) :: Γ) a τ), term ((x', σ) :: Γ') τ

  := extend_map Γ ((x', σ) :: Γ')
       (weaken_map Γ Γ' VAR x' σ Hx1 Hx2) 
       x σ (newestvar Γ' x' σ).

Lemma shift_vars' : forall Γ Γ' x σ,
  let x' := fresh[ Γ, Γ' ] in
  (forall a τ, inenv Γ a τ -> term Γ' τ) ->
  (forall (a : atom) (τ : ty),
    inenv ((x, σ) :: Γ) a τ -> term ((x', σ) :: Γ') τ).
Proof.
  intros. 
  refine (shift_vars Γ Γ' x x' σ _ _  X a τ H).

  apply fresh_atom_is_fresh'.
  simpl. red; intros. apply app_elem. auto.

  apply fresh_atom_is_fresh'.
  simpl. red; intros.
  apply app_elem. right.
  apply app_elem. auto.
Defined.

Fixpoint term_subst
  (Γ Γ':env) (τ₁:ty)
  (VAR:forall a τ, inenv Γ a τ -> term Γ' τ)
  (m:term Γ τ₁) : term Γ' τ₁ :=

  match m with
  | tvar x σ IN => VAR x σ IN
  | tnat n => tnat Γ' n
  | tapp σ₁ σ₂ m₁ m₂ =>
      tapp Γ' σ₁ σ₂
          (term_subst Γ Γ' (σ₁ ⇒ σ₂) VAR m₁)
          (term_subst Γ Γ' σ₁ VAR m₂)
  | tlam x σ₁ σ₂ m' =>
      let x' := fresh[ Γ, Γ' ] in
      tlam Γ' x' σ₁ σ₂
          (term_subst ((x,σ₁)::Γ) ((x',σ₁)::Γ') σ₂
            (shift_vars' Γ Γ' x σ₁ VAR) 
            m')
  end.

Program Definition subst (Γ:env) (τ₁ τ₂:ty) (a:atom)
  (m:term ((a,τ₂)::Γ) τ₁) (z:term Γ τ₂) : term Γ τ₁ :=

  term_subst ((a,τ₂)::Γ) Γ τ₁ (extend_map Γ Γ (tvar Γ) a τ₂ z) m.

Program Definition term1 :=
  tlam (("x",ty_nat)::nil) "y" ty_nat ty_nat 
    (tvar (("y",ty_nat)::("x",ty_nat)::nil) "x" ty_nat (Logic.refl_equal _)).

Program Definition term2 :=
  tnat nil 10.

Definition term3' := subst nil _ _ "x" term1 term2.

Program Definition term3 :=
  subst nil (ty_nat ⇒ ty_nat) ty_nat "x" term1 term2.

Eval vm_compute in (raw _ _ term1).
Eval vm_compute in (raw _ _ term2).
Eval vm_compute in (raw _ _ term3).
Eval vm_compute in (raw _ _ term3').


(*
Definition var_subst 
       (Γ : env) (τ : ty) (a : atom)
       (z:term Γ τ)
       (x : atom) (σ : ty)
       : forall (IN:inenv ((a,τ)::Γ) x σ), term Γ σ.
Proof.
  refine (match string_dec x a with
          | left Hx => fun IN => eq_rect τ (term Γ) z σ _
          | right Hx => fun IN => tvar Γ x σ _
          end).
  hnf in IN. simpl in *.
  destruct (string_dec x a). injection IN; auto.
  elim n; auto.
  hnf in IN; simpl in IN.
  destruct (string_dec x a); auto. elim Hx; auto.
Defined.

Lemma weaken_fresh
  (Γ Γ' : env) (σ: ty) (a:atom) (p:perm) :
  let x' := fresh[ Γ, Γ', a, p ] in
  forall
  (x : atom) (τ : ty), inenv Γ' x τ -> inenv ((x', σ) :: Γ') x τ.
Proof.
  intro x'. unfold inenv. simpl. intros.
  destruct (string_dec x x').
  assert (x' ∈ (‖Γ'‖)).
  rewrite <- e.
  revert H. clear e. 
  induction Γ'; simpl in *; intuition.
  discriminate.
  destruct a0. 
  destruct (string_dec x s).
  apply cons_elem; simpl; auto. left. subst s; auto.
  apply cons_elem; right; auto.
  elimtype False.
  revert H0. apply fresh_atom_is_fresh'.
  simpl. red; intros.
  apply app_elem. right.
  apply app_elem. auto.
  auto.
Defined.

Lemma lam_invariant
  (Γ Γ' : env) (τ₂ : ty) (a : atom) (p : perm) (x : atom) (σ₁: ty) :
    let x' := fresh[ Γ, Γ', a, p ] in
    (forall (x : atom) (τ : ty), inenv Γ x τ -> 
      inenv ((a, τ₂) :: Γ') (p x) τ) ->
    forall (x0 : atom) (τ : ty),
      inenv ((x, σ₁) :: Γ) x0 τ ->
      inenv ((a, τ₂) :: (x', σ₁) :: Γ') ((p ∘ x ⇋ x') x0) τ.
Proof.
  do 4 intro.
  unfold inenv; simpl.
  destruct (string_dec x0 x). subst x0.
  destruct (string_dec x x).
  destruct (string_dec (p x') x').
  destruct (string_dec (p x') a).
  elimtype False.
  apply (fresh_atom_is_fresh _ : x' ∉ _).
  fold x'. rewrite <- e0. rewrite e1.
  simpl.
  apply app_elem. right.
  apply app_elem. right.
  apply cons_elem; auto.
  auto.
  elim n.
  destruct (Perm.support_axiom p x'); auto.
  elim (fresh_atom_is_fresh _ : x' ∉ _).
  fold x'.
  apply app_elem. right.
  apply app_elem. right.
  simpl.
  apply cons_elem. right.
  apply app_elem. auto.
  elim n; auto.

  destruct (string_dec x x0).
  elim n; auto.
  destruct (string_dec x' x0).
  subst x0.

  intro.
  elimtype False. 
  assert (x' ∈ ‖Γ‖).  
  revert H0. generalize x'.
  clear.
  induction Γ; simpl; intuition.
  discriminate.
  destruct (string_dec x' a0).
  subst a0.
  apply cons_elem; simpl; auto.
  apply cons_elem; simpl; auto.
  revert H1.
  apply (fresh_atom_is_fresh').
  red; intros.
  apply app_elem. auto.
  intros.
  generalize (H x0 τ H0). unfold inenv. simpl.
  destruct (string_dec (p x0) a); auto.
  destruct (string_dec (p x0) x'); auto.
  replace x' with (p x') in e.
  apply Perm.f_inj in e. elim n1; auto.
  destruct (Perm.support_axiom p x'); auto.
  elim (fresh_atom_is_fresh _ : x' ∉ _).
  fold x'.
  apply app_elem. right.
  apply app_elem. right.
  apply app_elem. right.
  apply app_elem. auto.
Defined.



Fixpoint term_subst
  (Γ Γ':env) (τ₁ τ₂:ty)
  (a:atom) (p:perm) (m:term Γ τ₁)
  (z:term Γ' τ₂)
  (H:forall x τ, inenv Γ x τ -> inenv ((a,τ₂)::Γ') (p x) τ)
  : term Γ' τ₁ :=

  match m with
  | tvar x σ IN => var_subst Γ' τ₂ a z (p x) σ (H x σ IN)
  | tnat n => tnat Γ' n
  | tapp σ₁ σ₂ m₁ m₂ =>
      tapp Γ' σ₁ σ₂
          (term_subst Γ Γ' (σ₁ ⇒ σ₂) τ₂ a p m₁ z H)
          (term_subst Γ Γ' σ₁ τ₂ a p m₂ z H)
  | tlam x σ₁ σ₂ m' =>
      let x' := fresh[ Γ, Γ', a, p ] in
      tlam Γ' x' σ₁ σ₂
          (term_subst
            ((x,σ₁)::Γ) ((x',σ₁)::Γ')
            σ₂ τ₂ a (p ∘ x ⇋ x')
            m'
            (term_wk Γ' ((x', σ₁) :: Γ') τ₂ z (weaken_fresh Γ Γ' σ₁ a p))
            (lam_invariant Γ Γ' τ₂ a p x σ₁ H))
  end.

Program Definition subst (Γ:env) (τ₁ τ₂:ty) (a:atom)
  (m:term ((a,τ₂)::Γ) τ₁) (z:term Γ τ₂) : term Γ τ₁ :=

  term_subst ((a,τ₂)::Γ) Γ τ₁ τ₂ a (id) m z (fun x τ H => H).


Program Definition term1 :=
  tlam (("x",ty_nat)::nil) "y" ty_nat ty_nat 
    (tvar (("y",ty_nat)::("x",ty_nat)::nil) "x" ty_nat (Logic.refl_equal _)).

Program Definition term2 :=
  tnat nil 10.

Definition term3' := subst nil _ _ "x" term1 term2.

Program Definition term3 :=
  term_subst (("x",ty_nat)::nil) nil (ty_nat ⇒ ty_nat) ty_nat "x" (id) term1 term2 _.
Next Obligation.
  simpl. intuition.
Defined.

Eval vm_compute in (raw _ _ term1).
Eval vm_compute in (raw _ _ term2).
Eval vm_compute in (raw _ _ term3).
Eval vm_compute in (raw _ _ term3').

Lemma subst_app Γ σ₁ σ₂ τ x z m1 m2 :
  subst Γ σ₂ τ x (tapp _ σ₁ σ₂ m1 m2) z =
    tapp Γ σ₁ σ₂ (subst Γ (σ₁ ⇒ σ₂) τ x m1 z) (subst Γ σ₁ τ x m2 z).
Proof.
  reflexivity.
Qed.  

Require Import Eqdep_dec.

Lemma subst_var Γ τ x z H :
  subst Γ τ τ x (tvar _ x τ H) z = z.
Proof.
  unfold subst. simpl.
  hnf in H. simpl in H.
  revert H.
  unfold var_subst. unfold inenv. simpl.
  case (string_dec x x).
  intros.
  match goal with [ |- eq_rect _ _ _ _ ?Heq = _ ] =>
    replace Heq with (Logic.eq_refl τ)
  end.
  simpl. auto.
  unfold f_equal. simpl.
  apply UIP_dec. decide equality.
  intros. elim n. auto.
Qed.

Lemma subst_var_neq Γ τ₁ τ₂ x y z H :
  x <> y ->
  exists H', 
    subst Γ τ₁ τ₂ x (tvar _ y τ₁ H) z = tvar Γ y τ₁ H'.
Proof.
  intros.
  unfold subst. simpl.
  revert H. unfold var_subst, inenv. simpl.
  destruct (string_dec y x).
  elim H0; auto.
  econstructor. reflexivity.
Qed.

Lemma subst_nat Γ τ x n z :
  subst Γ ty_nat τ x (tnat _ n) z = tnat Γ n.
Proof.
  reflexivity.
Qed.
*)

Inductive eval (Γ:env) : forall τ, term Γ τ -> term Γ τ -> Prop :=
  | evar : forall x τ IN,
               eval Γ τ (tvar Γ x τ IN) (tvar Γ x τ IN)
  | enat : forall n,
               eval Γ ty_nat (tnat Γ n) (tnat Γ n)
  | elam : forall x σ₁ σ₂ m,
               eval Γ (σ₁ ⇒ σ₂) (tlam Γ x σ₁ σ₂ m) (tlam Γ x σ₁ σ₂ m)
  | eapp : forall x σ₁ σ₂ m₁ m₂ n₁ n₂ z,
               eval Γ (σ₁ ⇒ σ₂) m₁ (tlam Γ x σ₁ σ₂ n₁) ->
               eval Γ σ₁ m₂ n₂ ->
               eval Γ σ₂ (subst Γ σ₂ σ₁ x n₁ n₂) z ->
               eval Γ σ₂ (tapp Γ σ₁ σ₂ m₁ m₂) z.

Require Import discrete.

Fixpoint tydom (τ:ty) : PLT :=
  match τ with
  | ty_nat => disc finbool
  | ty_arrow τ₁ τ₂ => PLT.exp (tydom τ₁) (tydom τ₂)
  end.

Require Import profinite_adj.

(***)
Definition tydom' (τ:ty) : PLT := liftPPLT (tydom τ).

Notation cxt := (finprod.finprod false string string_dec ty tydom').
Notation cxt' := (finprod.finprod true string string_dec ty tydom).
Notation castty := (cast (finprod.ty false ty tydom')).
Notation bind := (finprod.bind false string string_dec ty tydom').
Notation proj := (finprod.proj false string string_dec ty tydom').
Notation lookup := (finprod.lookup string string_dec ty).

Definition dom (Γ:env) (τ:ty) : Type := cxt Γ → tydom' τ.

Parameter junk : forall T:Type, T.

Parameter lift_prod : forall A B:PLT,
  PLT.prod (forgetPLT A) (forgetPLT B) → forgetPLT (PLT.prod A B).
Parameter push_prod : forall A B:∂PLT, 
  PLT.prod (liftPPLT A) (liftPPLT B) → liftPPLT (PLT.prod A B).

Parameter push_pprod : forall Γ,
  finprod.finprod false string string_dec ty tydom' Γ →
  liftPPLT (finprod.finprod true string string_dec ty tydom Γ).

Fixpoint denote (Γ:env) (τ:ty) (m:term Γ τ) : dom Γ τ :=
  match m in term _ τ' return dom Γ τ' with
  | tvar x σ IN => castty IN ∘ proj Γ x
  | tnat n => liftPPLT@(flat_elem n) ∘ push_pprod Γ
  | tapp σ₁ σ₂ m₁ m₂ =>
         liftPPLT@PLT.app ∘ push_prod _ _ ∘ PLT.pair (denote Γ (σ₁ ⇒ σ₂) m₁) (denote Γ σ₁ m₂)
  | tlam x σ₁ σ₂ m' =>
         liftPPLT@(PLT.curry 
           (adj_counit _
            ∘ forgetPLT@(denote ((x,σ₁)::Γ) σ₂ m' ∘ bind Γ x σ₁)
            ∘ lift_prod _ _
            ∘ PLT.pair_map _ (id) (adj_counit_inv_hom _)))
         ∘ adj_unit _
  end.


Parameter cxt_permute : forall Γ (p:perm), cxt Γ → cxt (env_papp p Γ).

Lemma denote_papp Γ τ (m:term Γ τ) (p:perm) :
  denote Γ τ m ≈ denote (env_papp p Γ) τ (term_papp p Γ τ m) ∘ cxt_permute Γ p.
Admitted.

Lemma bind_papp Γ τ x (p:perm) :
  cxt_permute ((x,τ)::Γ) p ∘ bind Γ x τ ≈
  bind (env_papp p Γ) (p x) τ ∘ PLT.pair_map _ (cxt_permute Γ p) id.
Admitted.

Lemma subst_soundness (Γ Γ':env) x σ₁ σ₂ n₁ n₂ (p:perm) H
   (Hx:lookup x (env_papp p Γ) = Some σ₁) 
   (Hx': forall i (Hn:i <> x), lookup i (env_papp p Γ) = lookup i Γ')
   (f:cxt Γ' → cxt (env_papp p Γ)) :

   castty Hx ∘ proj (env_papp p Γ) x ∘ f ≈ denote Γ' σ₁ n₂ -> 
   (forall i (Hn:i <> x),
     castty (Hx' i Hn) ∘ proj (env_papp p Γ) i ∘ f ≈ proj Γ' i) ->

   denote (env_papp p Γ) σ₂ (term_papp p _ _ n₁) ∘ f ≈ 
   denote Γ' σ₂ (term_subst Γ Γ' σ₂ σ₁ x p n₁ n₂ H).
Proof.
  revert x Γ' σ₁ p n₂ H Hx Hx' f.
  induction n₁; intros.

  (* variable case *)
  simpl.
  unfold var_subst.
  generalize (H x σ i).
  generalize (inenv_papp Γ x σ p i).
  unfold inenv. simpl.
  case (string_dec (p x) x0).
  simpl; intros.
  injection i1. intros. subst σ.
  replace i1 with (Logic.refl_equal (Some σ₁)).
  simpl.
  revert i0. rewrite e. intros.
  replace i0 with Hx. auto.
  apply UIP_dec. decide equality. decide equality.
  apply UIP_dec. decide equality. decide equality.
  intros.
  simpl.
  
  generalize (H1 (p x) n).
  generalize (Hx' (p x) n).
  intros. rewrite <- H2.
  rewrite (cat_assoc _ _ _ _ _ (castty i1)).
  rewrite (cat_assoc _ _ _ _ _ (castty i1)).
  rewrite (cast_compose _ _ (finprod.ty true ty tydom) _ _ _ e i1).
  replace (Logic.eq_trans e i1) with i0; auto.
  apply UIP_dec. decide equality. decide equality.
  
  (* nat case *)
  simpl.
admit. (* property of flat_elem *)

  (* app case *)
  simpl.
  rewrite <- (IHn₁1 x Γ' σ₁0 p n₂ H Hx Hx' f); auto.
  rewrite <- (IHn₁2 x Γ' σ₁0 p n₂ H Hx Hx' f); auto.
  rewrite <- (cat_assoc _ _ _ _ _ _ _ f).
  apply cat_respects. auto.
  apply PLT.pair_compose_commute.

  (* lambda case *)
  simpl.  
  set (x' := (fresh_atom (‖Γ‖ ++ ‖Γ'‖ ++ x0 :: ‖p‖ ++ nil))).
  simpl in *. fold x'.
  evar (f' : 
    (cxt ((x', σ₁) :: Γ')) →
    (cxt (((p ∘ x ⇋ x') x, σ₁) :: env_papp (p ∘ x ⇋ x') Γ))).
  rewrite <- (IHn₁ x0 ((x',σ₁)::Γ') σ₁0 (p ∘ x ⇋ x') 
               (term_wk Γ' ((x', σ₁) :: Γ') σ₁0 n₂ (weaken_fresh Γ Γ' σ₁ x0 p))
               (lam_invariant Γ Γ' σ₁0 x0 p x σ₁ H)) with (f:=f').
  rewrite PLT.curry_compose_commute.
  apply PLT.curry_eq.
  

Qed.



Lemma soundness : forall (Γ:env) (τ:ty) (m z:term Γ τ),
  eval Γ τ m z -> denote Γ τ m ≈ denote Γ τ z.
Proof.
  intros. induction H; auto.
  simpl.
  rewrite IHeval1.
  rewrite IHeval2.
  rewrite <- IHeval3.
  simpl.
  rewrite (PLT.curry_apply2).
  unfold subst.
  assert (Hi : lookup (id  (tt) x) (env_papp id  (tt) ((x, σ₁) :: Γ)) = Some σ₁).
  simpl. destruct (string_dec x x); auto. elim n; auto.
  rewrite <- (subst_soundness ((x,σ₁)::Γ) Γ x σ₁ σ₂ n₁ n₂ (id) (fun _ _ H => H) x Hi
    (bind (env_papp id Γ) x σ₁ ∘ PLT.pair (cxt_permute Γ id) (denote Γ σ₁ n₂))).
  simpl.
  clear Hi.
  rewrite (denote_papp ((x,σ₁)::Γ) σ₂ n₁ id). simpl.
  repeat rewrite <- (cat_assoc _ _ _ _ _ (denote _ _ _)).
  apply cat_respects. auto.
  rewrite bind_papp.  
  rewrite <- (cat_assoc _ _ _ _ _ (bind (env_papp id Γ) x σ₁)).
  apply cat_respects; auto.
  rewrite <- (PLT.pair_map_pair true).
  apply PLT.pair_eq.
  apply cat_ident1. apply cat_ident2.

  rewrite <- (cat_assoc _ _ _ _ _ (castty Hi)).
  rewrite (cat_assoc _ _ _ _ _ (proj _ _)).
  simpl.
  rewrite (finprod.proj_bind true).
  unfold finprod.lookup_eq.
  revert Hi. simpl.
  destruct (string_dec x x). intros.
  rewrite cast_refl. rewrite (cat_ident2 _ _ (finprod.ty true ty tydom (Some σ₁))).
  rewrite cast_dec_id. 
  rewrite (cat_ident2 _ _ (finprod.ty true ty tydom (Some σ₁))).
  apply PPLT.antistrict_pair_commute2.
admit.
  decide equality. decide equality.
  elim n. auto.
Qed.

  
