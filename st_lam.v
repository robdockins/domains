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
Require Import finprod.
Require Import discrete.

Require Import List.

Inductive ty :=
  | ty_bool
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


Definition inenv (Γ:env) (x:atom) (σ:ty) :=
  finprod.lookup atom string_dec ty x Γ = Some σ.

Inductive rawterm : Type :=
  | rawvar : atom -> rawterm
  | rawbool : bool -> rawterm
  | rawapp : rawterm -> rawterm -> rawterm
  | rawlam : atom -> ty -> rawterm -> rawterm.

Inductive term (Γ:env) : ty -> Type :=
  | tvar : forall x σ,
                inenv Γ x σ ->
                term Γ σ
  | tbool : forall n:bool,
                term Γ ty_bool
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
  | tbool b => tbool _ b
  | tapp σ₁ σ₂ m1 m2 => tapp _ σ₁ σ₂ (term_papp p _ _ m1) (term_papp p _ _ m2)
  | tlam x σ₁ σ₂ m' => tlam _ (p x) σ₁ σ₂ (term_papp p _ _ m')
  end.

Inductive alpha_eq : forall Γ Γ' (ρ₁ ρ₂:perm) (τ:ty),
  term Γ τ -> term Γ' τ -> Prop :=

  | aeq_var : forall Γ Γ' (ρ₁ ρ₂:perm) τ x₁ x₂ H₁ H₂,
                  ρ₁ x₁ = ρ₂ x₂ ->
                  alpha_eq Γ Γ' ρ₁ ρ₂ τ (tvar Γ x₁ τ H₁) (tvar Γ' x₂ τ H₂)

  | aeq_bool : forall Γ Γ' ρ₁ ρ₂ b,
                  alpha_eq Γ Γ' ρ₁ ρ₂ ty_bool
                    (tbool Γ b) (tbool Γ' b)

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
  | tbool b => rawbool b
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
  | tbool b => tbool Γ₂ b
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

Definition varmap (Γ Γ':env) :=
  forall a τ, inenv Γ a τ -> term Γ' τ.

Definition extend_map Γ Γ' 
  (VAR:varmap Γ Γ') x σ (m:term Γ' σ) :
  varmap ((x,σ)::Γ) Γ'.
Proof.
  red. unfold inenv. simpl; intros.
  destruct (string_dec a x). subst a.
  injection H. intro. subst σ. exact m.
  exact (VAR a τ H).
Defined.

Definition weaken_map Γ Γ'
  (VAR:varmap Γ Γ')
  x' σ (Hx1:x' ∉ ‖Γ‖) (Hx2:x' ∉ ‖Γ'‖) :
  varmap Γ ((x',σ)::Γ')

  := fun a τ H => 
       term_wk Γ' ((x', σ) :: Γ') τ (VAR a τ H) 
          (weaken_fresh Γ Γ' σ x' Hx1 Hx2).

Program Definition newestvar Γ x σ : term ((x,σ)::Γ) σ := tvar _ x σ _.
Next Obligation.
  intros. hnf; simpl.
  destruct (string_dec x x); auto. elim n; auto.
Defined.

Definition shift_vars Γ Γ' x x' σ
  (Hx1:x' ∉ ‖Γ‖) (Hx2:x' ∉ ‖Γ'‖)
  (VAR:varmap Γ Γ')
  : varmap ((x,σ)::Γ) ((x',σ)::Γ')

  := extend_map Γ ((x', σ) :: Γ')
      (weaken_map Γ Γ' VAR x' σ Hx1 Hx2) 
       x σ (newestvar Γ' x' σ).

Lemma shift_vars' : forall Γ Γ' x σ,
  let x' := fresh[ Γ, Γ' ] in
    varmap Γ Γ' ->
    varmap ((x,σ)::Γ) ((x',σ)::Γ').
Proof.
  intros.
  refine (shift_vars Γ Γ' x x' σ _ _ X).

  apply fresh_atom_is_fresh'.
  simpl. red; intros. apply app_elem. auto.

  apply fresh_atom_is_fresh'.
  simpl. red; intros.
  apply app_elem. right.
  apply app_elem. auto.
Defined.

Fixpoint term_subst
  (Γ Γ':env) (τ₁:ty)
  (VAR:varmap Γ Γ')
  (m:term Γ τ₁) : term Γ' τ₁ :=

  match m with
  | tvar x σ IN => VAR x σ IN
  | tbool b => tbool Γ' b
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
  tlam (("x",ty_bool)::nil) "y" ty_bool ty_bool
    (tvar (("y",ty_bool)::("x",ty_bool)::nil) "x" ty_bool (Logic.refl_equal _)).

Program Definition term2 :=
  tbool nil false.

Definition term3' := subst nil _ _ "x" term1 term2.

Program Definition term3 :=
  subst nil (ty_bool ⇒ ty_bool) ty_bool "x" term1 term2.

Eval vm_compute in (raw _ _ term1).
Eval vm_compute in (raw _ _ term2).
Eval vm_compute in (raw _ _ term3).
Eval vm_compute in (raw _ _ term3').


Inductive eval (Γ:env) : forall τ, term Γ τ -> term Γ τ -> Prop :=
  | evar : forall x τ IN,
               eval Γ τ (tvar Γ x τ IN) (tvar Γ x τ IN)
  | ebool : forall b,
               eval Γ ty_bool (tbool Γ b) (tbool Γ b)
  | elam : forall x σ₁ σ₂ m,
               eval Γ (σ₁ ⇒ σ₂) (tlam Γ x σ₁ σ₂ m) (tlam Γ x σ₁ σ₂ m)
  | eapp : forall x σ₁ σ₂ m₁ m₂ n₁ n₂ z,
               eval Γ (σ₁ ⇒ σ₂) m₁ (tlam Γ x σ₁ σ₂ n₁) ->
               eval Γ σ₁ m₂ n₂ ->
               eval Γ σ₂ (subst Γ σ₂ σ₁ x n₁ n₂) z ->
               eval Γ σ₂ (tapp Γ σ₁ σ₂ m₁ m₂) z.


Fixpoint tydom (τ:ty) : PLT :=
  match τ with
  | ty_bool => disc finbool
  | ty_arrow τ₁ τ₂ => PLT.exp (tydom τ₁) (tydom τ₂)
  end.

Notation cxt := (finprod.finprod false string string_dec ty tydom).
Notation castty := (cast (finprod.ty false ty tydom)).
Notation bind := (finprod.bind false string string_dec ty tydom).
Notation proj := (finprod.proj false string string_dec ty tydom).
Notation lookup := (finprod.lookup string string_dec ty).

Definition dom (Γ:env) (τ:ty) : Type := cxt Γ → tydom τ.

Fixpoint denote (Γ:env) (τ:ty) (m:term Γ τ) : dom Γ τ :=
  match m in term _ τ' return dom Γ τ' with
  | tvar x σ IN => castty IN ∘ proj Γ x
  | tbool b => disc_elem b ∘ PLT.terminate false (cxt Γ)
  | tapp σ₁ σ₂ m₁ m₂ => apply ∘ 〈 denote Γ (σ₁ ⇒ σ₂)%ty m₁, denote Γ σ₁ m₂ 〉
  | tlam x σ₁ σ₂ m' => Λ(denote ((x,σ₁)::Γ) σ₂ m' ∘ bind Γ x σ₁)
  end.
