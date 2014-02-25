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
Bind Scope ty_scope with ty.

Delimit Scope lam_scope with lam.
Open Scope lam_scope.

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
                term Γ (σ₁ ⇒ σ₂) ->
                term Γ σ₁ ->
                term Γ σ₂
  | tlam : forall x σ₁ σ₂,
                term ((x,σ₁)::Γ) σ₂ ->
                term Γ (σ₁ ⇒ σ₂).

Arguments tapp [_ _ _] _ _.
Notation "x • y" := (tapp x y) 
  (at level 52, left associativity, format "x • y") : lam_scope.

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
  | tapp σ₁ σ₂ m1 m2 => tapp (term_papp p _ _ m1) (term_papp p _ _ m2)
  | tlam x σ₁ σ₂ m' => tlam _ (p x) σ₁ σ₂ (term_papp p _ _ m')
  end.

Inductive var_cong : env -> env -> atom -> atom -> Prop :=
 | vcong_here : forall Γ₁ Γ₂ x₁ x₂ y₁ y₂ τ, 
                   x₁ = y₁ -> x₂ = y₂ ->
                   var_cong ((x₁,τ)::Γ₁) ((x₂,τ)::Γ₂) y₁ y₂
 | vcong_there : forall Γ₁ Γ₂ x₁ x₂ y₁ y₂ τ,
                   x₁ <> y₁ -> x₂ <> y₂ ->
                   var_cong Γ₁ Γ₂ y₁ y₂ ->
                   var_cong ((x₁,τ)::Γ₁) ((x₂,τ)::Γ₂) y₁ y₂.

Inductive alpha_cong : forall Γ Γ' (τ:ty), term Γ τ -> term Γ' τ -> Prop :=

  | acong_var : forall Γ Γ' τ x₁ x₂ H₁ H₂,
                  var_cong Γ Γ' x₁ x₂ ->
                  alpha_cong Γ Γ' τ (tvar Γ x₁ τ H₁) (tvar Γ' x₂ τ H₂)

  | acong_bool : forall Γ Γ' b,
                  alpha_cong Γ Γ' ty_bool (tbool Γ b) (tbool Γ' b)

  | acong_app : forall Γ Γ' σ₁ σ₂ m₁ m₂ n₁ n₂,
                  alpha_cong Γ Γ' (σ₁ ⇒ σ₂) m₁ n₁ ->
                  alpha_cong Γ Γ' σ₁ m₂ n₂ ->
                  alpha_cong Γ Γ' σ₂ (m₁ • m₂) (n₁ • n₂)

  | acong_lam : forall (Γ Γ':env) (x₁ x₂:atom) σ₁ σ₂ m₁ m₂,
                  alpha_cong ((x₁,σ₁)::Γ) ((x₂,σ₁)::Γ') σ₂ m₁ m₂ ->
                  alpha_cong Γ Γ' (σ₁ ⇒ σ₂) (tlam Γ x₁ σ₁ σ₂ m₁) (tlam Γ' x₂ σ₁ σ₂ m₂).


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
        @tapp Γ₂ σ₁ σ₂ (term_wk Γ₁ Γ₂ (σ₁ ⇒ σ₂) m₁ H) (term_wk Γ₁ Γ₂ σ₁ m₂ H)
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
  (Γ Γ':env) (τ:ty)
  (VAR:varmap Γ Γ')
  (m:term Γ τ) : term Γ' τ :=

  match m with
  | tvar x σ IN => VAR x σ IN
  | tbool b => tbool Γ' b
  | tapp σ₁ σ₂ m₁ m₂ =>
      @tapp Γ' σ₁ σ₂
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

Program Definition term1' :=
  tlam (("x",ty_bool)::nil) "x" ty_bool ty_bool
    (tvar (("x",ty_bool)::("x",ty_bool)::nil) "x" ty_bool (Logic.refl_equal _)).

Program Definition term2 :=
  tbool nil false.

Definition term3 := subst nil _ _ "x" term1 term2.
Definition term3' := subst nil _ _ "x" term1' term2.

Program Definition term1'' :=
  tlam nil "x" ty_bool ty_bool
    (tvar (("x",ty_bool)::nil) "x" ty_bool (Logic.refl_equal _)).

Definition term4 := subst nil _ _ "x" term1 (term1'' • tbool _ true).
Definition term4' := subst nil _ _ "x" term1' (term1'' • tbool _ true).

Program Definition term5 :=
  tlam (("y",ty_bool ⇒ ty_bool)%ty::("x",ty_bool)%ty::nil) "x" ty_bool _
    (tvar (("x",ty_bool)::("y",ty_bool ⇒ ty_bool)%ty::("x",ty_bool)%ty::nil) 
       "y" (ty_bool ⇒ ty_bool) (Logic.refl_equal _)).

Definition term6 := subst (("x",ty_bool)%ty::nil) _ _ "y" term5 term1.
Definition term6' := subst (("x",ty_bool)%ty::nil) _ _ "y" term5 term1'.

Eval vm_compute in (raw _ _ term1).
Eval vm_compute in (raw _ _ term1').
Eval vm_compute in (raw _ _ term2).
Eval vm_compute in (raw _ _ term3).
Eval vm_compute in (raw _ _ term3').
Eval vm_compute in (raw _ _ term4).
Eval vm_compute in (raw _ _ term4').
Eval vm_compute in (raw _ _ term5).
Eval vm_compute in (raw _ _ term6).
Eval vm_compute in (raw _ _ term6').


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

Lemma env_dec : forall a b:env, {a=b}+{a<>b}.
Proof.
  decide equality.
  decide equality.
  decide equality.
  apply string_dec.
Qed.

Ltac inj_ty :=
  repeat match goal with
           [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
             apply inj_pair2_ty in H ||
             apply (Eqdep_dec.inj_pair2_eq_dec _ string_dec) in H ||
             apply (Eqdep_dec.inj_pair2_eq_dec _ env_dec) in H
           end.

Ltac inv H :=
  inversion H; subst; inj_ty; repeat subst.

Section varmap_compose.
  Variables Γ₁ Γ₂ Γ₃:env.
  Variable g:varmap Γ₂ Γ₃.
  Variable f:varmap Γ₁ Γ₂.  

  Program Definition varmap_compose : varmap Γ₁ Γ₃ :=
    fun a τ (IN:inenv Γ₁ a τ) => term_subst Γ₂ Γ₃ τ g (f a τ IN).
End varmap_compose.

Lemma var_cong_refl Γ x τ:
  inenv Γ x τ ->
  var_cong Γ Γ x x.
Proof.
  induction Γ; intro H.
  inv H.
  hnf in H. simpl in H.
  destruct a.
  destruct (string_dec x c). inv H.
  apply vcong_here; auto.
  apply vcong_there; auto.
Qed.

Lemma var_cong_trans Γ₁ Γ₂ x y z :
  var_cong Γ₁ Γ₂ x y ->
  forall Γ₃,
  var_cong Γ₂ Γ₃ y z ->
  var_cong Γ₁ Γ₃ x z.
Proof.
  intro H; induction H; intros.
  subst. inv H1.
  apply vcong_here; auto.
  elim H3; auto.
  inv H2.
  elim H0. auto.
  apply vcong_there; auto.
Qed.

Lemma alpha_eq_refl Γ σ (m:term Γ σ) :
  alpha_cong Γ Γ σ m m.
Proof.
  induction m.
  apply acong_var.
  eapply var_cong_refl; eauto.
  apply acong_bool.
  apply acong_app; auto.
  apply acong_lam; auto.
Qed.

Lemma alpha_eq_trans Γ₁ τ (m:term Γ₁ τ) : 
  forall Γ₂ Γ₃ (n:term Γ₂ τ) (o:term Γ₃ τ),
  alpha_cong Γ₁ Γ₂ τ m n ->
  alpha_cong Γ₂ Γ₃ τ n o ->
  alpha_cong Γ₁ Γ₃ τ m o.
Proof.
  induction m; intros; inv H; inv H0.
  apply acong_var.
  eapply var_cong_trans; eauto.
  apply acong_bool.
  apply acong_app; eauto.
  apply acong_lam; eauto.
Qed.

Lemma alpha_cong_wk : forall (Γm Γn Γm' Γn':env) τ m n H₁ H₂,
  (forall a b, var_cong Γm Γn a b -> var_cong Γm' Γn' a b) ->
  alpha_cong Γm Γn τ m n ->
  alpha_cong _ _ τ (term_wk Γm Γm' τ m H₁)
                   (term_wk Γn Γn' τ n H₂).
Proof.
  intros. revert Γm' Γn' H₁ H₂ H.
  induction H0; simpl; intros.
  apply acong_var. apply H0. auto.
  apply acong_bool.
  apply acong_app; auto.
  apply acong_lam. apply IHalpha_cong.
  intros. inv H1.
  apply vcong_here; auto.
  apply vcong_there; auto.
Qed.

Lemma term_subst_cong : forall Γ τ (m:term Γ τ) Γ₁ Γ₂ 
  (VAR1 : varmap Γ Γ₁) (VAR2 : varmap Γ Γ₂),
  
  (forall a σ IN, alpha_cong Γ₁ Γ₂ σ (VAR1 a σ IN) (VAR2 a σ IN)) ->

  alpha_cong Γ₁ Γ₂ τ
    (term_subst Γ Γ₁ τ VAR1 m)
    (term_subst Γ Γ₂ τ VAR2 m).
Proof.
  intros until m; induction m; simpl; intros; auto.
  apply acong_bool.
  apply acong_app; auto.
  apply acong_lam; auto.
  apply IHm. intros.
  unfold shift_vars', shift_vars, extend_map, weaken_map.
  hnf in IN. simpl in IN.
  revert IN.
  destruct (string_dec a x); simpl; intros.
  subst a. inv IN.
  replace IN with (Logic.eq_refl (Some σ)). simpl.
  unfold eq_rect_r. simpl.
  unfold newestvar. simpl.
  apply acong_var.
  apply vcong_here; auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply alpha_cong_wk; auto.
  intros.
  apply vcong_there; auto.
admit.
admit.
Qed.

Lemma term_wk_ident : forall Γ σ m H,
  term_wk Γ Γ σ m H = m.
Proof.
  intros until m; induction m; simpl; intros; auto.
  f_equal.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  f_equal; auto.
  f_equal; auto.
Qed.  

Lemma term_wk_compose : forall Γ₁ σ m Γ₂ Γ₃ H1 H2 H3,
  term_wk Γ₂ Γ₃ σ (term_wk Γ₁ Γ₂ σ m H1) H2 = term_wk Γ₁ Γ₃ σ m H3.
Proof.
  intros until m. induction m; simpl; intros; auto.
  f_equal.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  rewrite (IHm1 Γ₂ Γ₃ H1 H2 H3).
  rewrite (IHm2 Γ₂ Γ₃ H1 H2 H3).
  auto.
  f_equal.
  apply IHm.
Qed.

Lemma term_wk_compose' : forall Γ₁ σ m Γ₂ Γ₃ H1 H2,
  term_wk Γ₂ Γ₃ σ (term_wk Γ₁ Γ₂ σ m H1) H2 = 
  term_wk Γ₁ Γ₃ σ m (fun x τ H => H2 x τ (H1 x τ H)).
Proof.
  intros. eapply term_wk_compose; eauto.
Qed.

Lemma term_subst_wk_cong : forall Γ τ (m:term Γ τ) Γ₁ Γ₂ Γ₃ Γ₄ 
  (VAR1 : varmap Γ Γ₁) (VAR2:varmap Γ₃ Γ₄) H₁ H₂,

  (forall a σ Ha1 Ha2 H,
    alpha_cong _ _ σ (term_wk Γ₁ Γ₂ σ (VAR1 a σ Ha1) H) (VAR2 a σ Ha2)) ->

  alpha_cong _ _ τ
    (term_wk Γ₁ Γ₂ τ (term_subst Γ Γ₁ τ VAR1 m) H₁)
    (term_subst Γ₃ Γ₄ τ VAR2 (term_wk Γ Γ₃ τ m H₂)).
Proof.
  intros until m. induction m; simpl; intros; auto.
  apply acong_bool.
  apply acong_app; auto.
  apply acong_lam.

  apply IHm; clear IHm.
  intros. unfold shift_vars'. unfold shift_vars.
  unfold extend_map. simpl. unfold weaken_map. simpl.
  unfold newestvar. simpl. unfold newestvar_obligation_1. simpl.
  generalize Ha1 Ha2. unfold inenv; simpl.
  destruct (string_dec a x); simpl.
  subst a. intros.
  inv Ha0. unfold eq_rect_r.
  replace Ha0 with (Logic.eq_refl (Some σ)).
  replace Ha3 with (Logic.eq_refl (Some σ)). simpl.
  apply acong_var.
  apply vcong_here; auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.

  intros.  
  rewrite term_wk_compose'.
  match goal with [ |- alpha_cong _ _ _
    (term_wk _ _ _ _ ?Q1)
    (term_wk _ _ _ _ ?Q2) ] =>
    generalize Q1 Q2; intros
  end.
  assert (forall x τ, inenv Γ₂ x τ -> inenv ((fresh[Γ,Γ₂],σ₁)::Γ₂) x τ).
    intros.
    hnf. hnf in H1. simpl. simpl in H1.
    rewrite H1.
    set (q := fresh [Γ,Γ₂]).
    simpl in q. fold q.
    destruct (string_dec x0 q).
    subst q.
    elimtype False.
admit.
    auto.

  apply alpha_eq_trans with
    ((fresh [Γ,Γ₂],σ₁)::Γ₂) 
    (term_wk Γ₂ ((fresh [Γ,Γ₂],σ₁)::Γ₂) σ
      (term_wk Γ₁ Γ₂ σ (VAR1 a σ Ha0) H₁) H1).
  rewrite term_wk_compose'.
  apply alpha_cong_wk.
admit.
  apply alpha_eq_refl.
  apply alpha_cong_wk.
  intros.
  apply vcong_there.
admit.
admit.
  auto.
  apply H.
Qed.


Lemma compose_term_subst : forall Γ₁ τ (m:term Γ₁ τ),
  forall (Γ₂ Γ₃:env) (g:varmap Γ₂ Γ₃) (f:varmap Γ₁ Γ₂),
  alpha_cong _ _ _ 
    (term_subst Γ₁ Γ₃ τ (varmap_compose _ _ _ g f) m)
    (term_subst Γ₂ Γ₃ τ g (term_subst Γ₁ Γ₂ τ f m)).
Proof.
  unfold varmap_compose.
  do 3 intro. induction m; simpl; intros.
  apply alpha_eq_refl.
  apply acong_bool.
  simpl. apply acong_app.
  apply IHm1; auto.
  apply IHm2; auto.

  apply acong_lam.
  eapply alpha_eq_trans. 2: apply IHm.

  apply term_subst_cong.
  clear. unfold shift_vars', shift_vars. simpl.
  intros.
  simpl.
  unfold inenv in *. simpl in *.
  unfold extend_map.
  destruct (string_dec a x).
  unfold eq_rect_r. simpl.
  subst a. inv IN.
  replace IN with (Logic.eq_refl (Some σ)).
  simpl.
  set (q := (fresh_atom (‖Γ‖ ++ ‖Γ₂‖ ++ nil))).
  simpl in *. fold q.
  unfold newestvar_obligation_1.
  destruct (string_dec q q).
  simpl. unfold newestvar. simpl.
  apply acong_var.
  apply vcong_here; auto.
  elim n; auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.

  apply term_subst_wk_cong. simpl. intros.
  set (q1 := fresh [ Γ, Γ₂ ]). 
  set (q2 := fresh [ Γ₂, Γ₃ ]).
  unfold inenv in *. simpl in *.
  revert Ha2.
  simpl in *. fold q1. fold q2.  
  destruct (string_dec a0 q1).
  subst a0.
  elimtype False.
  revert Ha1.
admit.
  intros.
  apply alpha_cong_wk.
  intros. apply vcong_there; auto.
admit.
  unfold q2.
admit.
  replace Ha2 with Ha1.
  apply alpha_eq_refl.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
Qed.  


Reserved Notation "m ⇓ z" (at level 82, left associativity).
Reserved Notation "m ↓" (at level 82, left associativity).

Inductive eval (Γ:env) : forall τ, term Γ τ -> term Γ τ -> Prop :=
  | evar : forall x τ IN,
               tvar Γ x τ IN ↓
  | ebool : forall b,
               tbool Γ b ↓
  | elam : forall x σ₁ σ₂ m,
               tlam Γ x σ₁ σ₂ m ↓
  | eapp : forall x σ₁ σ₂ m₁ m₂ n₁ n₂ z,
               m₁ ⇓ (tlam Γ x σ₁ σ₂ n₁) ->
               m₂ ⇓ n₂ ->
               subst Γ σ₂ σ₁ x n₁ n₂ ⇓ z ->
               m₁ • m₂ ⇓ z
 where "m ⇓ z" := (eval _ _ m z)
  and "m ↓" := (eval _ _ m m).

Fixpoint tydom (τ:ty) : PLT :=
  match τ with
  | ty_bool => disc finbool
  | (τ₁ ⇒ τ₂)%ty => tydom τ₁ ⇒ tydom τ₂
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
  | tapp σ₁ σ₂ m₁ m₂ => apply ∘ 〈 〚m₁〛, 〚m₂〛 〉
  | tlam x σ₁ σ₂ m' => Λ(〚m'〛 ∘ bind Γ x σ₁)
  end
 where "〚 m 〛" := (denote _ _ m) : lam_scope.

(* FIXME: move to profinite.v *)
Lemma plt_terminate_univ : forall (A:PLT) (f:A → 1),
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

Lemma alpha_cong_denote (Γ₁ Γ₂:env) τ (m:term Γ₁ τ) (n:term Γ₂ τ) :
  alpha_cong Γ₁ Γ₂ τ m n -> 

  forall A (h₁:A → cxt Γ₁) (h₂:A → cxt Γ₂),

  (forall a b τ (IN1:inenv Γ₁ a τ) (IN2:inenv Γ₂ b τ),
    var_cong Γ₁ Γ₂ a b ->
    castty IN1 ∘ proj Γ₁ a ∘ h₁ ≈ castty IN2 ∘ proj Γ₂ b ∘ h₂) ->

  〚m〛 ∘ h₁ ≈ 〚n〛 ∘ h₂.
Proof.
  intro H. induction H.
  simpl; intros. apply H0. auto.
  simpl; intros.
  do 2 rewrite <- (cat_assoc PLT).
  apply cat_respects; auto.
  transitivity (PLT.terminate false A).
  apply plt_terminate_univ.
  symmetry.
  apply plt_terminate_univ.
  simpl; intros.
  do 2 rewrite <- (cat_assoc PLT).
  apply cat_respects; auto.
  do 2 rewrite (PLT.pair_compose_commute false).
  apply PLT.pair_eq.
  apply IHalpha_cong1. auto.
  apply IHalpha_cong2. auto.
  simpl; intros.
  do 2 rewrite (PLT.curry_compose_commute false).
  apply PLT.curry_eq.
  do 2 rewrite <- (cat_assoc PLT).
  apply IHalpha_cong.  
  intros. inv H1.
  do 2 rewrite <- (cat_assoc PLT).
  rewrite (cat_assoc PLT _ _ _ _ (proj ((a,σ₁)::Γ) a)).
  rewrite (finprod.proj_bind false).
  rewrite <- (cat_assoc PLT).
  unfold PLT.pair_map.
  rewrite PLT.pair_commute2.
  rewrite (cat_ident2 PLT).
  symmetry.  
  rewrite (cat_assoc PLT _ _ _ _ (proj ((b,σ₁)::Γ') b)).
  rewrite (finprod.proj_bind false).
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute2.
  do 2 rewrite (cat_assoc PLT).
  apply cat_respects; auto.  
  etransitivity.
  apply cast_compose.
  symmetry.
  etransitivity.
  apply cast_compose.

  generalize (Logic.eq_trans (finprod.lookup_eq string string_dec ty Γ a σ₁) IN1).
  generalize (Logic.eq_trans (finprod.lookup_eq string string_dec ty Γ' b σ₁) IN2).
  hnf in IN1. simpl in *.
  destruct (string_dec a a).
  inv IN1. intros.
  replace e0 with e1. auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  elim n; auto.

  do 2 rewrite <- (cat_assoc PLT).
  rewrite (cat_assoc PLT _ _ _ _ (proj ((x₁,σ₁)::Γ) a)).
  rewrite (finprod.proj_bind_neq false); auto.
  instantiate (1:=H9).
  unfold PLT.pair_map.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  symmetry.
  rewrite (cat_assoc PLT _ _ _ _ (proj ((x₂,σ₁)::Γ') b)).
  rewrite (finprod.proj_bind_neq false); auto.
  instantiate (1:=H10).
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  repeat rewrite (cat_assoc PLT).
  apply cat_respects; auto.
  rewrite (cast_compose false).  
  rewrite (cast_compose false).  
  symmetry. apply H0. auto.
Qed.  

Lemma alpha_cong_denote_closed τ (m:term nil τ) (n:term nil τ) :
  alpha_cong nil nil τ m n -> 〚m〛 ≈ 〚n〛.
Proof.
  intros.
  cut (〚m〛∘ id ≈ 〚n〛∘ id ).
  intro. do 2 rewrite (cat_ident1 PLT) in H0. auto.
  apply alpha_cong_denote; auto.
  intros. inv H0.
Qed.

Definition varmap_denote (Γ Γ':env) (VAR:varmap Γ Γ') : cxt Γ' → cxt Γ.
Admitted.  

Lemma varmap_extend_bind Γ Γ' 
 (VAR:varmap Γ Γ') x σ (m:term Γ' σ) :

 varmap_denote _ _ (extend_map Γ Γ' VAR x σ m) ≈
 bind Γ x σ ∘ 〈 varmap_denote _ _ VAR, 〚m〛〉.
Admitted.

Lemma varmap_var_id Γ :
  varmap_denote Γ Γ (tvar Γ) ≈ id.
Admitted.

Definition unbind : forall (Γ:env) x' σ (Hx:x' ∉ ‖Γ‖),
  cxt ((x',σ)::Γ) → cxt Γ.
Admitted.

Lemma unbind_bind Γ x σ Hx :
  unbind Γ x σ Hx ∘ bind Γ x σ ≈ π₁.
Admitted.

Lemma weaken_map_denote Γ Γ'
  (VAR:varmap Γ Γ')
  x' σ (Hx1:x' ∉ ‖Γ‖) (Hx2:x' ∉ ‖Γ'‖) :
  varmap_denote _ _ (weaken_map Γ Γ' VAR x' σ Hx1 Hx2)
  ≈
  varmap_denote _ _ VAR ∘ unbind Γ' x' σ Hx2.
Admitted.

Lemma varmap_denote_proj Γ Γ' (VAR:varmap Γ Γ') x σ i :
  〚 VAR x σ i 〛 ≈ castty i ∘ proj Γ x ∘ varmap_denote Γ Γ' VAR.
Admitted.


Lemma term_subst_soundness Γ τ m : forall Γ' (VAR:varmap Γ Γ'),
  〚 term_subst Γ Γ' τ VAR m 〛 ≈ 〚m〛 ∘ varmap_denote Γ Γ' VAR.
Proof.
  induction m; simpl; intros.

  apply varmap_denote_proj.

  rewrite <- (cat_assoc PLT).
  apply cat_respects. auto.
  symmetry. apply plt_terminate_univ.

  rewrite <- (cat_assoc PLT).
  apply cat_respects. auto.
  rewrite (PLT.pair_compose_commute false).
  rewrite IHm1. rewrite IHm2. auto.
  rewrite IHm.
  rewrite PLT.curry_compose_commute.
  apply PLT.curry_eq.
  rewrite <- (cat_assoc PLT).
  rewrite <- (cat_assoc PLT).
  apply cat_respects; auto.
  unfold shift_vars'.
  unfold shift_vars.
  rewrite varmap_extend_bind.
  rewrite <- (cat_assoc PLT).
  apply cat_respects; auto.
  rewrite (PLT.pair_compose_commute false).
  unfold PLT.pair_map.
  apply PLT.pair_eq.
  rewrite weaken_map_denote.
  rewrite <- (cat_assoc PLT).
  rewrite unbind_bind. auto.
  simpl denote.
  rewrite <- (cat_assoc PLT).
  generalize (finprod.proj_bind false string string_dec ty tydom
    Γ' (fresh_atom (‖Γ‖++‖Γ'‖++nil)) σ₁).
  simpl. intros. 
  etransitivity. apply cat_respects. reflexivity.
  apply H.
  rewrite (cat_assoc PLT).
  match goal with 
    [ |- castty ?H1 ∘ castty ?H2 ∘ π₂ ≈ _ ] =>
    generalize H1 H2
  end.
  intros.
  etransitivity. apply cat_respects. 
  apply (cast_compose false _ (finprod.ty false ty tydom) _ _ _ e i).
  reflexivity.
  etransitivity. apply cat_respects. 
  refine (cast_dec_id false _ (finprod.ty false ty tydom) _
    (Some σ₁) (Logic.eq_trans e i)).
  decide equality. decide equality.
  reflexivity.
  auto.
Qed.  

Lemma subst_soundness Γ x σ₁ σ₂ n₁ n₂ :
   〚 n₁ 〛 ∘ bind Γ x σ₁ ∘ 〈id, 〚 n₂ 〛〉 ≈ 〚 subst Γ σ₂ σ₁ x n₁ n₂ 〛.
Proof.
  unfold subst.
  rewrite term_subst_soundness.
  rewrite <- (cat_assoc PLT).
  apply cat_respects; auto.
  rewrite varmap_extend_bind.
  rewrite varmap_var_id. auto.
Qed.


(**  Evaluation preserves the denotation of terms. *)
Theorem soundness : forall Γ τ (m z:term Γ τ),
  m ⇓ z -> 〚m〛 ≈ 〚z〛.
Proof.
  intros. induction H; simpl; auto.
  rewrite IHeval1.
  rewrite IHeval2.
  rewrite <- IHeval3.
  simpl.
  rewrite PLT.curry_apply2.
  apply subst_soundness.
Qed.


(**  Now we move on to the more difficult adequacy proof.
     For this we will first need a variety of technical results
     about the operational semantics.
  *)

Lemma eval_value Γ τ x y :
  eval Γ τ x y -> eval Γ τ y y.
Proof.
  intro H. induction H.
  apply evar.
  apply ebool.
  apply elam.
  auto.
Qed.

Lemma eval_eq Γ τ x y1 y2 :
  eval Γ τ x y1 -> eval Γ τ x y2 -> y1 = y2.
Proof.
  intro H. revert y2.
  induction H.

  intros. inv H. 
  f_equal.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  intros. inv H. auto.
  intros. inv H. auto.

  intros. inv H2.
  apply IHeval1 in H8.
  apply IHeval2 in H9.
  inv H8.
  apply IHeval3; auto.
Qed.

Lemma eval_trans Γ τ x y z :
  eval Γ τ x y -> eval Γ τ y z -> eval Γ τ x z.
Proof.
  intros.
  replace z with y; auto.
  eapply eval_eq with y; auto.
  eapply eval_value; eauto.
Qed.


Lemma eval_app_congruence Γ σ₁ σ₂ : forall x x' y y' z,
  (forall q, eval _ _ x q -> eval _ _ x' q) ->
  (forall q, eval _ _ y q -> eval _ _ y' q) ->
  eval Γ _ (@tapp Γ σ₁ σ₂ x y) z ->
  eval Γ _ (@tapp Γ σ₁ σ₂ x' y') z.
Proof.
  intros.
  inv H1.
  apply H in H7.
  apply H0 in H8.
  eapply eapp; eauto.
Qed.


(**  Now we define the logical relation.  It is defined by induction
     on the structure of types, in a standard way.
  *)
Fixpoint LR (τ:ty) : term nil τ -> (cxt nil → tydom τ) -> Prop :=
  match τ as τ' return term nil τ' -> (cxt nil → tydom τ') -> Prop
  with
  | ty_bool => fun m h =>
        exists b:bool, m = tbool nil b /\ 
                h ≈ disc_elem b ∘ PLT.terminate _ _
  | ty_arrow σ₁ σ₂ => fun m h =>
        forall n h', 
          LR σ₁ n h' -> eval nil σ₁ n n ->
          exists z1 z2, 
            eval _ _ (m•n) z1 /\
            alpha_cong nil nil σ₂ z1 z2 /\
            LR σ₂ z2 (apply ∘ 〈h, h'〉)
  end.

Lemma LR_equiv τ : forall m h h',
  h ≈ h' -> LR τ m h -> LR τ m h'.
Proof.
  induction τ; simpl. intros.
  destruct H0 as [b [??]]. exists b; split; auto.
  rewrite <- H; auto.
  simpl; intros.
  destruct (H0 n h'0 H1 H2) as [z1 [z2 [?[??]]]].
  exists z1; exists z2; split; auto.split; auto.
  revert H5. apply IHτ2.
  apply cat_respects; auto.
  apply PLT.pair_eq; auto.
Qed.

(**  The fundamental lemma states that every term stands in the logical relation
     with its denotation when applied to related substitutions.
  *)
Lemma fundamental_lemma : forall Γ τ (m:term Γ τ) 
  (VAR:varmap Γ nil) (VARh : cxt nil → cxt Γ),
  (forall a σ H, VAR a σ H ↓ /\
       LR σ (VAR a σ H) (castty H ∘ proj Γ a ∘ VARh)) ->
  exists z1 z2,
    eval nil τ (term_subst Γ nil τ VAR m) z1 /\
    alpha_cong nil nil τ z1 z2 /\
    LR τ z2 (〚m〛 ∘ VARh ).
Proof.
  induction m; simpl; intros.

  (* var case *)  
  simpl. exists (VAR x σ i). exists (VAR x σ i). 
  destruct (H x σ i); intuition.
  apply alpha_eq_refl.
  
  (* bool case *)
  exists (tbool nil n). 
  exists (tbool nil n). 
  split. apply ebool.
  split. apply acong_bool.
  exists n. split; auto.
  rewrite <- (cat_assoc PLT). apply cat_respects; auto.
  apply plt_terminate_univ.

  (* application case *)  
  destruct (IHm1 VAR VARh H) as [z1 [z1' [?[??]]]].
  destruct (IHm2 VAR VARh H) as [z2 [z2' [?[??]]]].
  simpl in H1.
  destruct (H2 z2' (〚 m2 〛 ∘ VARh)) as [z3 [z3' [?[??]]]]; auto.
admit.
  exists z3. exists z3'.
  split.
  inv H6.
  eapply eapp.
  apply eval_trans with z1; auto. eauto. eauto.
  replace z2 with n₂; auto.
  apply eval_eq with z2; auto.
  eapply eval_value; eauto.
  revert H5.
  apply LR_equiv.
  rewrite <- (cat_assoc PLT).
  apply cat_respects. auto.
  symmetry. apply PLT.pair_compose_commute.

  (* lambda case *)
  econstructor. split. apply elam.
  intros.
  set (VAR' := extend_map Γ nil VAR x σ₁ n).
  set (VARh' := bind Γ x σ₁ ∘ 〈 VARh, h' 〉). 
  destruct (IHm VAR' VARh') as [z [??]].
  simpl; intros.
  split.
  subst VAR' VARh'. unfold extend_map.
  hnf in H2. simpl in *.
  destruct (string_dec a x). inv H2.
  replace H2 with (Logic.eq_refl (Some σ)). simpl.
  unfold eq_rect_r. simpl. auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply H.
  subst VAR' VARh'. unfold extend_map.
  hnf in H2. simpl in *. unfold eq_rect_r. simpl.
  unfold f_equal. unfold eq_sym. simpl.
  revert H2.

  generalize (finprod.proj_bind_neq false string string_dec ty tydom Γ x σ₁ a).
  generalize (finprod.proj_bind false string string_dec ty tydom Γ a σ₁).
  generalize (proj ((x,σ₁)::Γ) a).
  unfold finprod.ty. simpl.
  unfold finprod.lookup_neq. simpl.
  destruct (string_dec a x). simpl; intros.
admit.
  intros.
  destruct (H a σ H4). revert H6.
  apply LR_equiv.
  rewrite cast_refl in H3.
  rewrite (cat_ident2 PLT) in H3.
  rewrite <- (cat_assoc PLT).
  rewrite <- (cat_assoc PLT).
  rewrite (cat_assoc PLT _ _ _ _ h).
  rewrite H3; auto.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  auto.
  exists z.
  split.
  eapply eapp.
  apply elam. eauto.
  unfold subst.
admit. (* ?? *)

  revert H3. apply LR_equiv.
  rewrite PLT.curry_apply3.
  unfold VARh'.
  rewrite (cat_assoc PLT). auto.
Qed.

(**  A simpified form of the fundamental lemma that follows
     from the inductively-strong one above.
  *)
Lemma fundamental_lemma' : forall τ (m:term nil τ),
  exists z, eval nil τ m z /\ LR τ z 〚 m 〛.
Proof.
  intros.
  destruct (fundamental_lemma nil τ m (tvar nil) id) as [z [??]].
  intros. hnf in H. simpl in H. discriminate.
  exists z. split.
admit.
  revert H0. apply LR_equiv.
  apply cat_ident1.
Qed.


(**  Now we define contextual equivalance.  Contexts here are
     given in "inside-out" form, which makes the induction in the
     adequacy proof significantly easier.
  *)

Inductive context τ : env -> ty -> Type :=
  | cxt_top : context τ nil τ
  | cxt_appl : forall Γ σ₁ σ₂,
                    term Γ σ₁ ->
                    context τ Γ σ₂ ->
                    context τ Γ (σ₁ ⇒ σ₂)
  | cxt_appr : forall Γ σ₁ σ₂,
                    term Γ (σ₁ ⇒ σ₂) ->
                    context τ Γ σ₂ ->
                    context τ Γ σ₁
  | cxt_lam : forall Γ (x:atom) σ₁ σ₂,
                    context τ Γ (σ₁ ⇒ σ₂) ->
                    context τ ((x,σ₁)::Γ) σ₂.

Fixpoint plug τ Γ σ (C:context τ Γ σ) : term Γ σ -> term nil τ :=
  match C in context _ Γ' σ' return term Γ' σ' -> term nil τ with
  | cxt_top => fun x => x
  | cxt_appl Γ σ₁ σ₂ t C' => fun x => plug τ _ _ C' (tapp x t)
  | cxt_appr Γ σ₁ σ₂ t C' => fun x => plug τ _ _ C' (tapp t x)
  | cxt_lam  Γ a σ₁ σ₂ C' => fun x => plug τ _ _ C' (tlam Γ a σ₁ σ₂ x)
  end.

Definition cxt_eq τ Γ σ (m n:term Γ σ):=
  forall (C:context τ Γ σ) (z:term nil τ),
    eval nil τ (plug τ Γ σ C m) z <-> eval nil τ (plug τ Γ σ C n) z.

Lemma terminate_le_cancel (hf:bool) (A B:PLT.PLT hf) (f g:1 → B) (a:A) :
  f ∘ PLT.terminate hf A ≤ g ∘ PLT.terminate hf A ->
  f ≤ g.
Proof.
  repeat intro.
  destruct a0. destruct c.
  assert ((a,c0) ∈ PLT.hom_rel (f ∘ PLT.terminate hf A)).
  apply PLT.compose_hom_rel. exists tt. split; auto.
  apply eprod_elem. split; apply eff_complete.
  apply H in H1.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [[] [??]]. auto.
Qed.

Lemma terminate_cancel (hf:bool) (A B:PLT.PLT hf) (f g:1 → B) (a:A) :
  f ∘ PLT.terminate hf A ≈ g ∘ PLT.terminate hf A ->
  f ≈ g.
Proof.
  intros. destruct H; split; eapply terminate_le_cancel; eauto.
Qed.

(**  Adequacy means that terms with equivalant denotations
     are contextually equivalant in any boolean context.
  *)
Theorem adequacy : forall Γ τ (m n:term Γ τ),
  〚m〛 ≈ 〚n〛 -> cxt_eq ty_bool Γ τ m n.
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
  apply (terminate_cancel false (cxt nil) _ _ _ (fun i => tt)) in H5.
  apply disc_elem_inj in H5. auto.
  subst bn.
  split; intro.
  assert (z = (tbool nil bm)).
  eapply eval_eq; eauto.
  subst z. auto.
  assert (z = (tbool nil bm)).
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

  simpl; intros.
  apply IHC. simpl.
  apply PLT.curry_eq.
  apply cat_respects; auto.
Qed.

(**  As a corollary of the fundamental lemma, we learn that
     the calculus is strongly normalizing.
  *)
Corollary normalizing : forall τ (m:term nil τ), exists z, eval nil τ m z.
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
