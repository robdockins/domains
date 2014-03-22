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
Require Import flat.
Require Import profinite_adj.
Require Import fixes.
Require Import strict_utils.


Require Import List.

Inductive ty :=
  | ty_bool
  | ty_arrow : ty -> ty -> ty.

Delimit Scope ty_scope with ty.
Notation "2" := ty_bool : ty_scope.
Notation "x ⇒ y" := (ty_arrow (x)%ty (y)%ty) : ty_scope.
Bind Scope ty_scope with ty.

Delimit Scope lam_scope with lam.
Open Scope lam_scope.

Fixpoint tydom (τ:ty) : ∂PLT :=
  match τ with
  | ty_bool => flat enumbool
  | ty_arrow τ₁ τ₂ => colift (tydom τ₁ ⊸ tydom τ₂)
  end.

Module env_input <: FINPROD_INPUT.
  Definition I := string.
  Definition Idec := string_dec.
  Definition A := ty.
  Definition F τ := U (tydom τ).
End env_input.

Module ENV := finprod.finprod(env_input).

Definition env := list (atom * ty).

Definition env_supp (Γ:env) := map (@fst atom ty) Γ.

Canonical Structure env_supported :=
  Supported env env_supp.

Definition inenv (Γ:env) (x:atom) (σ:ty) :=
  ENV.lookup x Γ = Some σ.

Inductive rawterm : Type :=
  | rawvar : atom -> rawterm
  | rawbool : bool -> rawterm
  | rawapp : rawterm -> rawterm -> rawterm
  | rawif : rawterm -> rawterm -> rawterm -> rawterm
  | rawfix : atom -> rawterm -> rawterm
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
  | tif : forall σ,
                term Γ ty_bool ->
                term Γ σ ->
                term Γ σ ->
                term Γ σ
  | tlam : forall x σ₁ σ₂,
                term ((x,σ₁)::Γ) σ₂ ->
                term Γ (σ₁ ⇒ σ₂)
  | tfix : forall x σ,
                term ((x,σ)::Γ) σ ->
                term Γ σ.

Arguments tapp [_ _ _] _ _.
Notation "x • y" := (tapp x y) 
  (at level 52, left associativity, format "x • y") : lam_scope.

Definition concat A := fold_right (@app A) nil.

Notation "'fresh' '[' x , .. , z ']'" :=
  (fresh_atom (concat atom
   (cons (Support.support _ x) .. (cons (Support.support _ z) nil) ..))).
    
Canonical Structure atom_supp :=
  Supported atom (fun x => x::nil).


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

  | acong_if : forall Γ Γ' σ x1 x2 y1 y2 z1 z2,
                  alpha_cong Γ Γ' ty_bool x1 x2 ->
                  alpha_cong Γ Γ' σ y1 y2 ->
                  alpha_cong Γ Γ' σ z1 z2 ->
                  alpha_cong Γ Γ' σ (tif Γ σ x1 y1 z1) (tif Γ' σ x2 y2 z2)
  
  | acong_fix : forall (Γ Γ':env) (x₁ x₂:atom) σ m₁ m₂,
                  alpha_cong ((x₁,σ)::Γ) ((x₂,σ)::Γ') σ m₁ m₂ ->
                  alpha_cong Γ Γ' σ (tfix Γ x₁ σ m₁) (tfix Γ' x₂ σ m₂)

  | acong_lam : forall (Γ Γ':env) (x₁ x₂:atom) σ₁ σ₂ m₁ m₂,
                  alpha_cong ((x₁,σ₁)::Γ) ((x₂,σ₁)::Γ') σ₂ m₁ m₂ ->
                  alpha_cong Γ Γ' (σ₁ ⇒ σ₂) (tlam Γ x₁ σ₁ σ₂ m₁) (tlam Γ' x₂ σ₁ σ₂ m₂).

Fixpoint raw (Γ:env) (τ:ty) (m:term Γ τ) : rawterm :=
  match m with
  | tvar x _ _ => rawvar x
  | tbool b => rawbool b
  | tapp σ₁ σ₂ t1 t2 => rawapp (raw Γ (σ₁ ⇒ σ₂) t1) (raw Γ σ₁ t2)
  | tif σ x y z => rawif (raw Γ ty_bool x) (raw Γ σ y) (raw Γ σ z)
  | tlam x σ₁ σ₂ m' => rawlam x σ₁ (raw ((x,σ₁)::Γ) σ₂ m')
  | tfix x σ m' => rawfix x (raw ((x,σ)::Γ) σ m')
  end.

Definition env_incl (Γ₁ Γ₂:env) :=
  forall x τ, inenv Γ₁ x τ -> inenv Γ₂ x τ.

Lemma env_incl_wk (Γ₁ Γ₂:env) y σ :
  env_incl Γ₁ Γ₂ ->
  env_incl ((y,σ)::Γ₁) ((y,σ)::Γ₂).
Proof.
  unfold env_incl. unfold inenv.
  simpl; repeat intro.
  destruct (string_dec y x); auto.
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
  | tif σ x y z =>
        tif Γ₂ σ (term_wk Γ₁ Γ₂ ty_bool x H)
                 (term_wk Γ₁ Γ₂ σ y H)
                 (term_wk Γ₁ Γ₂ σ z H)
  | tfix x σ m' =>
        tfix Γ₂ x σ
          (term_wk ((x,σ)::Γ₁) ((x,σ)::Γ₂) σ m'
             (env_incl_wk Γ₁ Γ₂ x σ H))

  | tlam x σ₁ σ₂ m' =>
        tlam Γ₂ x σ₁ σ₂ 
            (term_wk ((x,σ₁)::Γ₁) ((x,σ₁)::Γ₂) σ₂ m'
              (env_incl_wk Γ₁ Γ₂ x σ₁ H))
  end.

Lemma weaken_fresh
  (Γ Γ' : env) (σ: ty) x' :
  x' ∉ ‖Γ'‖ -> 
  forall (x : atom) (τ : ty),
    inenv Γ' x τ -> inenv ((x', σ) :: Γ') x τ.
Proof.
  intros.
  unfold inenv. simpl. intros.
  destruct (string_dec x' x).
  assert (x' ∈ (‖Γ'‖)).
  rewrite e.
  revert H0. clear e. 
  induction Γ'; simpl in *; intuition.
  discriminate.
  destruct a. 
  hnf in H0. simpl in H0.
  destruct (string_dec s x).
  apply cons_elem; simpl; auto. left. subst s; auto.
  apply cons_elem; right; auto.
  apply IHΓ'.
  intro.
  apply H.
  apply cons_elem. right; auto.
  auto.
  elim H; auto.
  auto.
Qed.

Definition varmap (Γ Γ':env) :=
  forall a τ, inenv Γ a τ -> term Γ' τ.

Definition extend_map Γ Γ' 
  (VAR:varmap Γ Γ') x σ (m:term Γ' σ) :
  varmap ((x,σ)::Γ) Γ'.
Proof.
  red. unfold inenv. simpl; intros.
  destruct (string_dec x a). subst a.
  injection H. intro. subst σ. exact m.
  exact (VAR a τ H).
Defined.

Definition weaken_map Γ Γ'
  (VAR:varmap Γ Γ')
  x' σ (Hx:x' ∉ ‖Γ'‖) :
  varmap Γ ((x',σ)::Γ')

  := fun a τ H => 
       term_wk Γ' ((x', σ) :: Γ') τ (VAR a τ H) 
          (weaken_fresh Γ Γ' σ x' Hx).

Program Definition newestvar Γ x σ : term ((x,σ)::Γ) σ := tvar _ x σ _.
Next Obligation.
  intros. hnf; simpl.
  destruct (string_dec x x); auto. elim n; auto.
Defined.

Definition shift_vars Γ Γ' x x' σ
  (Hx:x' ∉ ‖Γ'‖)
  (VAR:varmap Γ Γ')
  : varmap ((x,σ)::Γ) ((x',σ)::Γ')

  := extend_map Γ ((x', σ) :: Γ')
      (weaken_map Γ Γ' VAR x' σ Hx) 
       x σ (newestvar Γ' x' σ).

Lemma shift_vars' : forall Γ Γ' x σ,
  let x' := fresh[ Γ' ] in
    varmap Γ Γ' ->
    varmap ((x,σ)::Γ) ((x',σ)::Γ').
Proof.
  intros.
  refine (shift_vars Γ Γ' x x' σ _ X).

  apply fresh_atom_is_fresh'.
  simpl. red; intros.
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
  | tif σ x y z =>
      tif Γ' σ (term_subst Γ Γ' ty_bool VAR x)
            (term_subst Γ Γ' σ VAR y)
            (term_subst Γ Γ' σ VAR z)
  | tfix x σ m' =>
      let x' := fresh[ Γ' ] in
      tfix Γ' x' σ
          (term_subst ((x,σ)::Γ) ((x',σ)::Γ') σ
            (shift_vars' Γ Γ' x σ VAR)
            m')
  | tlam x σ₁ σ₂ m' =>
      let x' := fresh[ Γ' ] in
      tlam Γ' x' σ₁ σ₂
          (term_subst ((x,σ₁)::Γ) ((x',σ₁)::Γ') σ₂
            (shift_vars' Γ Γ' x σ₁ VAR) 
            m')
  end.

Program Definition subst (Γ:env) (τ₁ τ₂:ty) (a:atom)
  (m:term ((a,τ₂)::Γ) τ₁) (z:term Γ τ₂) : term Γ τ₁ :=

  term_subst ((a,τ₂)::Γ) Γ τ₁ (extend_map Γ Γ (tvar Γ) a τ₂ z) m.

(*
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
*)

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


Reserved Notation "m ⇓ z" (at level 82, left associativity).
Reserved Notation "m ↓" (at level 82, left associativity).

Inductive eval (Γ:env) : forall τ, term Γ τ -> term Γ τ -> Prop :=
  | ebool : forall b,
               tbool Γ b ↓
  | eif : forall σ x y z b q,
               x ⇓ (tbool Γ b) ->
               (if b then y else z) ⇓ q ->
               (tif Γ σ x y z) ⇓ q
  | elam : forall x σ₁ σ₂ m,
               tlam Γ x σ₁ σ₂ m ↓
  | efix : forall x σ m z,
               subst Γ σ σ x m (tfix Γ x σ m) ⇓ z ->
               tfix Γ x σ m ⇓ z
  | eapp : forall x σ₁ σ₂ m₁ m₂ n₁ n₂ z,
               m₁ ⇓ (tlam Γ x σ₁ σ₂ n₁) ->
               m₂ ⇓ n₂ ->
               subst Γ σ₂ σ₁ x n₁ n₂ ⇓ z ->
               m₁ • m₂ ⇓ z
 where "m ⇓ z" := (eval _ _ m z)
  and "m ↓" := (eval _ _ m m).

Notation cxt := ENV.finprod.
Notation castty := (cast ENV.ty).
Notation proj := ENV.proj.
Notation bind := ENV.bind.

Definition dom (Γ:env) (τ:ty) : Type := cxt Γ → U (tydom τ).

Fixpoint denote (Γ:env) (τ:ty) (m:term Γ τ) : dom Γ τ :=
  match m in term _ τ' return dom Γ τ' with
  | tvar x σ IN => castty IN ∘ proj Γ x
  | tbool b => flat_elem' b
  | tif σ x y z => 
      flat_cases' (fun b:bool => if b then 〚y〛 else 〚z〛) ∘ 〈 id, 〚x〛 〉
  | tapp σ₁ σ₂ m₁ m₂ => strict_app' ∘ 〈 〚m₁〛, 〚m₂〛 〉
  | tfix x σ m' => fixes (cxt Γ) (tydom σ) (Λ(〚m'〛 ∘ bind Γ x σ))
  | tlam x σ₁ σ₂ m' => strict_curry' (〚m'〛 ∘ bind Γ x σ₁)
  end
 where "〚 m 〛" := (denote _ _ m) : lam_scope.

Lemma alpha_cong_denote (Γ₁ Γ₂:env) τ (m:term Γ₁ τ) (n:term Γ₂ τ) :
  alpha_cong Γ₁ Γ₂ τ m n -> 

  forall A
    (h₁:A → cxt Γ₁) (h₂:A → cxt Γ₂),

  (forall a b τ (IN1:inenv Γ₁ a τ) (IN2:inenv Γ₂ b τ),
    var_cong Γ₁ Γ₂ a b ->
    castty IN1 ∘ proj Γ₁ a ∘ h₁ ≈ castty IN2 ∘ proj Γ₂ b ∘ h₂) ->

  〚m〛 ∘ h₁ ≈ 〚n〛 ∘ h₂.
Proof.
  intro H. induction H.
  simpl; intros. apply H0. auto.
  simpl; intros.

  etransitivity.
  
  symmetry. apply flat_elem'_ignores_arg.
  apply flat_elem'_ignores_arg.

  simpl; intros.
  rewrite <- (cat_assoc PLT).
  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  rewrite (PLT.pair_compose_commute false).
  rewrite (IHalpha_cong1 _ h₁ h₂ H1).
  rewrite (IHalpha_cong2 _ h₁ h₂ H1).
  auto.

  intros. simpl.
  rewrite <- (cat_assoc PLT).
  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  rewrite (PLT.pair_compose_commute false).
  rewrite (cat_ident2 PLT _ _ h₁).
  rewrite (cat_ident2 PLT _ _ h₂).
  rewrite (flat_cases_commute _ _ _ _ _ h₁).
  rewrite (flat_cases_commute _ _ _ _ _ h₂).
  apply cat_respects; auto.
  apply flat_cases_univ'.
  intros.
  eapply flat_cases'_strict.
  apply H3. auto.
  intros.
  rewrite flat_cases_elem'.
  rewrite (cat_ident1 PLT).
  destruct x.
  apply IHalpha_cong2; auto.
  apply IHalpha_cong3; auto.
  apply PLT.pair_eq; auto.

  simpl; intros.

  do 2 rewrite fixes_compose_commute.
  apply fixes_eq.
  do 2 rewrite PLT.curry_compose_commute.
  apply PLT.curry_eq.
  do 2 rewrite <- (cat_assoc PLT).
  apply IHalpha_cong.  
  
(* FIXME: extract lemma here *)
  intros. inv H1.
  do 2 rewrite <- (cat_assoc PLT).
  rewrite (cat_assoc PLT _ _ _ _ (proj ((a,σ)::Γ) a)).
  rewrite (ENV.proj_bind_eq _ _ _ _ (refl_equal a)).
  rewrite <- (cat_assoc PLT).
  unfold PLT.pair_map.
  rewrite PLT.pair_commute2.
  rewrite (cat_ident2 PLT).
  symmetry.  
  rewrite (cat_assoc PLT _ _ _ _ (proj ((b,σ)::Γ') b)).
  rewrite (ENV.proj_bind_eq _ _ _ _ (refl_equal b)).
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute2.
  do 2 rewrite (cat_assoc PLT).
  apply cat_respects; auto.  
  etransitivity.
  apply cast_compose.
  symmetry.
  etransitivity.
  apply cast_compose.

  match goal with [ |- castty ?X ≈ castty ?Y ] => generalize X Y end.
  hnf in IN1. simpl in *.
  destruct (string_dec a a).
  inv IN1. intros.
  replace e0 with e1. auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  elim n; auto.

  do 2 rewrite <- (cat_assoc PLT).
  rewrite (cat_assoc PLT _ _ _ _ (proj ((x₁,σ)::Γ) a)).
  rewrite (ENV.proj_bind_neq x₁ σ a Γ H9); auto.
  unfold PLT.pair_map.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  symmetry.
  rewrite (cat_assoc PLT _ _ _ _ (proj ((x₂,σ)::Γ') b)).
  rewrite (ENV.proj_bind_neq x₂ σ b Γ' H10); auto.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  repeat rewrite (cat_assoc PLT).
  apply cat_respects; auto.
  rewrite (cast_compose false).  
  rewrite (cast_compose false).  
  symmetry. apply H0. auto.
(* end lemma *)

  simpl; intros.
  do 2 rewrite strict_curry_compose_commute'.
  apply strict_curry'_eq.
  do 2 rewrite <- (cat_assoc PLT).
  apply IHalpha_cong.  

(* FIXME: use lemma here *)
  intros. inv H1.
  do 2 rewrite <- (cat_assoc PLT).
  rewrite (cat_assoc PLT _ _ _ _ (proj ((a,σ₁)::Γ) a)).
  rewrite (ENV.proj_bind_eq _ _ _ _ (refl_equal a)).
  rewrite <- (cat_assoc PLT).
  unfold PLT.pair_map.
  rewrite PLT.pair_commute2.
  rewrite (cat_ident2 PLT).
  symmetry.  
  rewrite (cat_assoc PLT _ _ _ _ (proj ((b,σ₁)::Γ') b)).
  rewrite (ENV.proj_bind_eq _ _ _ _ (refl_equal b)).
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute2.
  do 2 rewrite (cat_assoc PLT).
  apply cat_respects; auto.  
  etransitivity.
  apply cast_compose.
  symmetry.
  etransitivity.
  apply cast_compose.

  match goal with [ |- castty ?X ≈ castty ?Y ] => generalize X Y end.
  hnf in IN1. simpl in *.
  destruct (string_dec a a).
  inv IN1. intros.
  replace e0 with e1. auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  elim n; auto.

  do 2 rewrite <- (cat_assoc PLT).
  rewrite (cat_assoc PLT _ _ _ _ (proj ((x₁,σ₁)::Γ) a)).
  rewrite (ENV.proj_bind_neq x₁ σ₁ a Γ H9); auto.
  unfold PLT.pair_map.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  symmetry.
  rewrite (cat_assoc PLT _ _ _ _ (proj ((x₂,σ₁)::Γ') b)).
  rewrite (ENV.proj_bind_neq x₂ σ₁ b Γ' H10); auto.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  repeat rewrite (cat_assoc PLT).
  apply cat_respects; auto.
  rewrite (cast_compose false).  
  rewrite (cast_compose false).  
  symmetry. apply H0. auto.
(* END: use lemma *)
Qed.

Lemma alpha_cong_denote' Γ τ (m:term Γ τ) (n:term Γ τ) :
  alpha_cong Γ Γ τ m n -> 〚m〛 ≈ 〚n〛.
Proof.
  intros.
  cut (〚m〛∘ id ≈ 〚n〛∘ id ).
  intro. do 2 rewrite (cat_ident1 PLT) in H0. auto.
  apply alpha_cong_denote; auto.
  intros. cut (a = b). intro. subst b.
  replace IN2 with IN1; auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  cut (forall Γ₁ Γ₂ a b, var_cong Γ₁ Γ₂ a b -> Γ₁ = Γ₂ -> a = b).
  intros. eapply H1; eauto.
  clear.
  intros. induction H.
  inv H0; auto.
  inv H0; auto.
Qed.


Definition varmap_denote (Γ Γ':env) (VAR:varmap Γ Γ') 
  : cxt Γ' → cxt Γ
  := ENV.mk_finprod Γ (cxt Γ') 
      (fun i => match ENV.lookup i Γ as a return
                  ENV.lookup i Γ = a -> cxt Γ' → ENV.ty a
                with
                | None => fun H => PLT.terminate _ _
                | Some a => fun H =>〚VAR i a H〛
                end refl_equal).

Definition weaken_denote (Γ Γ':env) (Hwk:env_incl Γ Γ')
  : cxt Γ' → cxt Γ
  := ENV.mk_finprod Γ (cxt Γ')
      (fun i => match ENV.lookup i Γ as a return 
                  ENV.lookup i Γ = a -> ENV.ty (ENV.lookup i Γ') → ENV.ty a
                with
                | None => fun H => PLT.terminate _ _
                | Some a => fun H => castty (Hwk i a H)
                end refl_equal ∘ proj Γ' i).

Lemma varmap_extend_bind Γ Γ' 
 (VAR:varmap Γ Γ') x σ (m:term Γ' σ) :

  varmap_denote _ _ (extend_map Γ Γ' VAR x σ m) ≈
  bind Γ x σ ∘ 〈 varmap_denote _ _ VAR, 〚m〛〉.
Proof.
  symmetry. unfold varmap_denote at 2.
  apply ENV.finprod_universal. intros.
  rewrite (cat_assoc PLT).
  pose (string_dec x i). destruct s.
  subst i.
  rewrite (ENV.proj_bind_eq x σ x Γ refl_equal).
  simpl. unfold ENV.lookup_eq.
  simpl.
  unfold extend_map. simpl.
  destruct (string_dec x x). simpl.
  unfold eq_rect_r. simpl.
  rewrite cast_refl.
  rewrite (cat_ident2 PLT).
  rewrite PLT.pair_commute2. auto.
  elim n; auto.
  rewrite (ENV.proj_bind_neq x σ i Γ n).
  unfold ENV.lookup_neq. simpl.
  unfold extend_map; simpl.
  destruct (string_dec x i).
  contradiction.
  rewrite cast_refl.
  rewrite (cat_ident2 PLT).
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  unfold varmap_denote.
  rewrite ENV.finprod_proj_commute.
  auto.
Qed.

Lemma weaken_term_denote Γ a m : forall Γ' H,
  〚m〛 ∘ weaken_denote Γ Γ' H ≈〚 term_wk Γ Γ' a m H 〛.
Proof.
  induction m; simpl; intros.
  unfold weaken_denote.
  rewrite <- (cat_assoc PLT).
  rewrite ENV.finprod_proj_commute.
  generalize (Logic.eq_refl (ENV.lookup x Γ)).
  generalize (H x σ i).
  revert i. unfold inenv.
  pattern (ENV.lookup x Γ) at 1 3 4 5 6 7 .
  case (ENV.lookup x Γ); intros.
  inv i. 
  rewrite (cat_assoc PLT). apply cat_respects; auto.
  replace i with (refl_equal (Some σ)).
  rewrite cast_refl. rewrite (cat_ident2 PLT).
  generalize (H x σ e). generalize i0.
  unfold inenv. rewrite i0.
  intros. 
  replace i2 with (refl_equal (Some σ)).
  replace i1 with (refl_equal (Some σ)). auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  discriminate.

  symmetry. apply flat_elem'_ignores_arg.

  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  apply cat_respects; auto.
  apply PLT.pair_eq.
  apply IHm1; auto.
  apply IHm2; auto.
  
  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  rewrite (cat_ident2 PLT).
  rewrite (flat_cases_commute _ _ _ _ _ (weaken_denote Γ Γ' H)).
  rewrite IHm1. apply cat_respects; auto.
  apply flat_cases_univ'.
  intros.
  eapply flat_cases'_strict. apply H0. auto.
  intros. rewrite flat_cases_elem'.
  rewrite (cat_ident1 PLT).
  destruct x; auto.

  rewrite strict_curry_compose_commute'.
  apply strict_curry'_eq.
  rewrite <- IHm.

(* lemma here ? *)
  do 2 rewrite <- (cat_assoc PLT). apply cat_respects; auto.

  symmetry.
  unfold weaken_denote at 1.
  rewrite ENV.mk_finprod_compose_commute.
  symmetry. apply ENV.finprod_universal.
  intros.
  rewrite (cat_assoc PLT).
  unfold bind.
  rewrite (ENV.finprod_proj_commute ((x,σ₁)::Γ)).
  symmetry.
  rewrite <- (cat_assoc PLT).
  rewrite ENV.finprod_proj_commute. simpl.
  generalize (env_incl_wk Γ Γ' x σ₁ H i).
  unfold env_incl. simpl. unfold inenv. simpl.
  destruct (string_dec  x i).
  intros.
  unfold PLT.pair_map.
  rewrite (cat_ident2 PLT).
  symmetry. etransitivity. apply PLT.pair_commute2.
  replace (i0 σ₁ Logic.eq_refl) with (refl_equal (Some σ₁)).
  rewrite cast_refl. rewrite (cat_ident2 PLT); auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.

  symmetry.
  unfold PLT.pair_map.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  rewrite (cat_assoc PLT).
  unfold weaken_denote.
  rewrite (ENV.finprod_proj_commute Γ).
  rewrite <- (cat_assoc PLT).
  apply cat_respects; auto.
  match goal with [ |- _ ?X ≈ _ ] => generalize X end.
  pattern (ENV.lookup i Γ) at 2 3 4 8.
  case (ENV.lookup i Γ); auto.
  intros.
  generalize (H i t e) (i0 t e).
  unfold inenv.
  case (ENV.lookup i Γ'); intros.
  inv i1.
  replace i1 with (refl_equal (Some t)).
  replace e0 with (refl_equal (Some t)).
  auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  discriminate.  
(* end lemma? *)

  rewrite fixes_compose_commute.
  apply fixes_eq.
  rewrite PLT.curry_compose_commute.
  apply PLT.curry_eq.
  rewrite <- IHm.

(* use lemma here? *)

  do 2 rewrite <- (cat_assoc PLT). apply cat_respects; auto.

  symmetry.
  unfold weaken_denote at 1.
  rewrite ENV.mk_finprod_compose_commute.
  symmetry. apply ENV.finprod_universal.
  intros.
  rewrite (cat_assoc PLT).
  unfold bind.
  rewrite (ENV.finprod_proj_commute ((x,σ)::Γ)).
  symmetry.
  rewrite <- (cat_assoc PLT).
  rewrite ENV.finprod_proj_commute. simpl.
  generalize (env_incl_wk Γ Γ' x σ H i).
  unfold env_incl. simpl. unfold inenv. simpl.
  destruct (string_dec  x i).
  intros.
  unfold PLT.pair_map.
  rewrite (cat_ident2 PLT).
  symmetry. etransitivity. apply PLT.pair_commute2.
  replace (i0 σ Logic.eq_refl) with (refl_equal (Some σ)).
  rewrite cast_refl. rewrite (cat_ident2 PLT); auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.

  symmetry.
  unfold PLT.pair_map.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  rewrite (cat_assoc PLT).
  unfold weaken_denote.
  rewrite (ENV.finprod_proj_commute Γ).
  rewrite <- (cat_assoc PLT).
  apply cat_respects; auto.
  match goal with [ |- _ ?X ≈ _ ] => generalize X end.
  pattern (ENV.lookup i Γ) at 2 3 4 8.
  case (ENV.lookup i Γ); auto.
  intros.
  generalize (H i t e) (i0 t e).
  unfold inenv.
  case (ENV.lookup i Γ'); intros.
  inv i1.
  replace i1 with (refl_equal (Some t)).
  replace e0 with (refl_equal (Some t)).
  auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  discriminate.  
(* end use lemma? *)
Qed.

Lemma weaken_map_denote Γ Γ'
  (VAR:varmap Γ Γ')
  x' σ (Hx:x' ∉ ‖Γ'‖) Hx' :
  varmap_denote _ _ (weaken_map Γ Γ' VAR x' σ Hx)
  ≈
  varmap_denote _ _ VAR ∘ ENV.unbind Γ' x' σ Hx'.
Proof.
  symmetry. apply ENV.finprod_universal. intros.
  rewrite (cat_assoc PLT).
  unfold varmap_denote.
  rewrite (ENV.finprod_proj_commute Γ).
  unfold weaken_map; simpl.
  generalize (Logic.eq_refl (ENV.lookup i Γ)).
  generalize (weaken_fresh Γ Γ' σ x' Hx).
  simpl.
  pattern (ENV.lookup i Γ) at 2 3 4 5 9.
  case (ENV.lookup i Γ); intros.
  2: apply plt_terminate_univ.
  rewrite <- weaken_term_denote.
  apply cat_respects. auto.
  apply ENV.finprod_universal.
  intros. 

  unfold ENV.unbind.  
  rewrite (ENV.finprod_proj_commute Γ').
  symmetry.
  match goal with [ |- _ ≈ _ ∘ ?X ] => set (p := X) end.
  simpl in *.
  set (p' := proj ((x',σ)::Γ') i1). 
  change p' with p. clear p'.
  generalize p; clear p.
  simpl.
  unfold ENV.unbind_lemma. simpl.
  unfold eq_ind_r. simpl.
  generalize (i0 i1).
  unfold inenv. simpl.
  pattern (string_dec x' i1).
  destruct (string_dec x' i1). subst i1.
  simpl. rewrite Hx'.
  intros.
  apply cat_respects; auto.
  symmetry. apply plt_terminate_univ.

  generalize (Logic.eq_refl (ENV.lookup i1 Γ')).
  destruct (ENV.lookup i1 Γ'); intros.
  replace (i2 t0 e0) with (refl_equal (Some t0)).
  rewrite cast_refl. auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply cat_respects; auto.
  symmetry. apply plt_terminate_univ.
Qed.


Lemma varmap_denote_proj Γ Γ' (VAR:varmap Γ Γ') x σ i :
  〚 VAR x σ i 〛 ≈ castty i ∘ proj Γ x ∘ varmap_denote Γ Γ' VAR.
Proof.
  unfold varmap_denote.
  rewrite <- (cat_assoc PLT).
  rewrite ENV.finprod_proj_commute.
  red in i. 
  generalize (Logic.eq_refl (ENV.lookup x Γ)).
  generalize i at 2.
  pattern (ENV.lookup x Γ) at 1 3 4 5 6.
  case (ENV.lookup x Γ). intros.
  inv i0.
  rewrite cast_dec_id.
  rewrite (cat_ident2 PLT).
  replace e with i. auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  decide equality. decide equality.
  intros. rewrite i in e. discriminate.
Qed.

Lemma term_subst_soundness Γ τ m : forall Γ' (VAR:varmap Γ Γ'),
  〚 term_subst Γ Γ' τ VAR m 〛 ≈ 〚m〛 ∘ varmap_denote Γ Γ' VAR.
Proof.
  induction m; simpl; intros.

  apply varmap_denote_proj.
  apply flat_elem'_ignores_arg.

  rewrite <- (cat_assoc PLT).
  apply cat_respects. auto.
  rewrite (PLT.pair_compose_commute false).
  rewrite IHm1. rewrite IHm2. auto.

  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  rewrite (cat_ident2 PLT).
  rewrite (flat_cases_commute _ _ _ _ _ (varmap_denote Γ Γ' VAR)).
  apply cat_respects.
  2: apply PLT.pair_eq; auto.
  apply flat_cases_univ'. intros.
  eapply flat_cases'_strict. apply H. auto.
  intros.
  rewrite flat_cases_elem'.
  rewrite (cat_ident1 PLT).
  destruct x; auto.

  rewrite IHm.
  rewrite strict_curry_compose_commute'.
  apply strict_curry'_eq.

(* begin lemma? *)
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
  rewrite ENV.bind_unbind. auto.

  simpl denote.
  rewrite <- (cat_assoc PLT).
  generalize (ENV.proj_bind_eq
    (fresh_atom (‖Γ'‖++nil)) σ₁ (fresh_atom (‖Γ'‖++nil)) Γ' Logic.refl_equal).
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
  apply (cast_compose false _ (ENV.ty) _ _ _ e i).
  reflexivity.
  etransitivity. apply cat_respects. 
  refine (cast_dec_id false _ (ENV.ty) _
    (Some σ₁) (Logic.eq_trans e i)).
  decide equality. decide equality.
  reflexivity.
  auto.
(* end lemma? *)

  rewrite IHm.
  rewrite fixes_compose_commute.
  apply fixes_eq.
  rewrite PLT.curry_compose_commute.
  apply PLT.curry_eq.

(* use lemma? *)
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
  rewrite ENV.bind_unbind. auto.

  simpl denote.
  rewrite <- (cat_assoc PLT).
  generalize (ENV.proj_bind_eq
    (fresh_atom (‖Γ'‖++nil)) σ (fresh_atom (‖Γ'‖++nil)) Γ' Logic.refl_equal).
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
  apply (cast_compose false _ (ENV.ty) _ _ _ e i).
  reflexivity.
  etransitivity. apply cat_respects. 
  refine (cast_dec_id false _ (ENV.ty) _
    (Some σ) (Logic.eq_trans e i)).
  decide equality. decide equality.
  reflexivity.
  auto.
(* end use lemma? *)

Grab Existential Variables.
  simpl.
  set (q := fresh [Γ']). simpl in q. fold q.
  cut (q ∉ ‖Γ'‖).
  clearbody q. clear. induction Γ'; simpl; intros; auto.
  destruct a. simpl in *.
  destruct (string_dec c q). subst q.
  elim H. apply cons_elem. simpl; auto.
  apply IHΓ'. intro. apply H. apply cons_elem; auto.
  unfold q. apply fresh_atom_is_fresh'.
  red; intros. apply app_elem. auto.

(* another copy of same *)
  simpl.
  set (q := fresh [Γ']). simpl in q. fold q.
  cut (q ∉ ‖Γ'‖).
  clearbody q. clear. induction Γ'; simpl; intros; auto.
  destruct a. simpl in *.
  destruct (string_dec c q). subst q.
  elim H. apply cons_elem. simpl; auto.
  apply IHΓ'. intro. apply H. apply cons_elem; auto.
  unfold q. apply fresh_atom_is_fresh'.
  red; intros. apply app_elem. auto.
Qed.  

Lemma varmap_var_id Γ :
  varmap_denote Γ Γ (tvar Γ) ≈ id.
Proof.
  symmetry. unfold varmap_denote.
  apply ENV.finprod_universal.
  intros.
  rewrite (cat_ident1 PLT). simpl.
  generalize (proj Γ i).
  destruct (ENV.lookup i Γ); intros.
  rewrite cast_refl. rewrite (cat_ident2 PLT); auto.
  apply plt_terminate_univ.
Qed.

Lemma varmap_compose_denote Γ₁ Γ₂ Γ₃ f g :
  varmap_denote _ _  (varmap_compose Γ₁ Γ₂ Γ₃ f g) ≈
  varmap_denote _ _ g ∘ varmap_denote _ _ f.
Proof.
  symmetry. apply ENV.finprod_universal.
  intros.
  rewrite (cat_assoc PLT).
  unfold varmap_denote at 1.
  rewrite (ENV.finprod_proj_commute Γ₁).
  generalize (Logic.eq_refl (ENV.lookup i Γ₁)).
  pattern (ENV.lookup i Γ₁) at 2 3 4 5 9.
  case (ENV.lookup i Γ₁); intros.
  2: apply plt_terminate_univ.
  unfold varmap_compose.
  symmetry. apply term_subst_soundness.
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

Lemma value_semvalue Γ τ (m z:term Γ τ) : m ⇓ z -> semvalue 〚z〛.
Proof.
  intro H; induction H; auto.
  simpl. apply flat_elem'_semvalue.
  simpl. apply strict_curry'_semvalue.
Qed.


(**  Evaluation preserves the denotation of terms. *)
Theorem soundness : forall Γ τ (m z:term Γ τ),
  m ⇓ z -> 〚m〛 ≈ 〚z〛.
Proof.
  intros. induction H; simpl; auto.

  rewrite IHeval1.
  simpl.
  rewrite flat_cases_elem'.
  rewrite (cat_ident1 PLT).
  destruct b; auto.

  rewrite fixes_unroll.
  rewrite PLT.curry_apply2.
  rewrite <- IHeval.
  apply (subst_soundness Γ x σ σ m (tfix Γ x σ m)).

  rewrite IHeval1.
  rewrite IHeval2.
  rewrite <- IHeval3.
  simpl.
  rewrite strict_curry_app'.
  apply subst_soundness.
  eapply value_semvalue; eauto.
Qed.


Lemma var_cong_refl Γ x τ:
  inenv Γ x τ ->
  var_cong Γ Γ x x.
Proof.
  induction Γ; intro H.
  inv H.
  hnf in H. simpl in H.
  destruct a.
  destruct (string_dec c x). inv H.
  apply vcong_here; auto.
  apply vcong_there; auto.
Qed.

Lemma var_cong_sym Γ₁ Γ₂ x y :
  var_cong Γ₁ Γ₂ x y ->
  var_cong Γ₂ Γ₁ y x.
Proof.
  intro H. induction H.
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
  apply acong_if; auto.
  apply acong_lam; auto.
  apply acong_fix; auto.
Qed.

Lemma alpha_eq_sym Γ₁ Γ₂ τ m n :
  alpha_cong Γ₁ Γ₂ τ m n ->
  alpha_cong Γ₂ Γ₁ τ n m.
Proof.
  intro H; induction H.
  apply acong_var. apply var_cong_sym. auto.
  apply acong_bool.
  apply acong_app; auto.
  apply acong_if; auto.
  apply acong_fix; auto.
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
  apply acong_if; eauto.
  apply acong_lam; eauto.
  apply acong_fix; eauto.
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
  apply acong_if; auto.
  apply acong_fix. apply IHalpha_cong.
  intros. inv H1.
  apply vcong_here; auto.
  apply vcong_there; auto.

  apply acong_lam. apply IHalpha_cong.
  intros. inv H1.
  apply vcong_here; auto.
  apply vcong_there; auto.
Qed.

(**  Now we move on to the more difficult adequacy proof.
     For this we will first need a variety of technical results
     about the operational semantics.
  *)

Lemma eval_value Γ τ x y :
  eval Γ τ x y -> eval Γ τ y y.
Proof.
  intro H. induction H.
  apply ebool.
  auto.
  apply elam.
  auto.
  auto.
Qed.

Lemma eval_eq Γ τ x y1 y2 :
  eval Γ τ x y1 -> eval Γ τ x y2 -> y1 = y2.
Proof.
  intro H. revert y2.
  induction H.

  intros. inv H.  auto.
  intros. inv H1.
  assert (tbool Γ b = tbool Γ b0).
  apply IHeval1. auto.
  inv H2.
  apply IHeval2; auto.
  intros. inv H. auto.

  intros. inv H0.
  apply IHeval; auto.

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

(*
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
*)


(**  Now we define the logical relation.  It is defined by induction
     on the structure of types, in a standard way.
  *)
Fixpoint LR (τ:ty) : term nil τ -> (cxt nil → U (tydom τ)) -> Prop :=
  match τ as τ' return term nil τ' -> (cxt nil → U (tydom τ')) -> Prop
  with
  | ty_bool => fun m h =>
        exists b:bool, m = tbool nil b /\ h ≈ flat_elem' b
  | ty_arrow σ₁ σ₂ => fun m h =>
        forall n h', 
          LR σ₁ n h' -> n↓ -> semvalue h' ->
          semvalue (strict_app' ∘ 〈 h, h' 〉) ->
          exists z1 z2, 
            eval _ _ (m•n) z1 /\
            alpha_cong nil nil σ₂ z1 z2 /\
            LR σ₂ z2 (strict_app' ∘ 〈h, h'〉)
  end.

Lemma LR_equiv τ : forall m h h',
  h ≈ h' -> LR τ m h -> LR τ m h'.
Proof.
  induction τ; simpl. intros.
  destruct H0 as [b [??]]. exists b; split; auto.
  rewrite <- H; auto.
  simpl; intros.
  destruct (H0 n h'0 H1 H2) as [z1 [z2 [?[??]]]]; auto.
  rewrite H. auto.
  exists z1; exists z2; split; auto. split; auto.
  revert H7. apply IHτ2.
  apply cat_respects; auto.
  apply PLT.pair_eq; auto.
Qed.

Lemma varcong_inenv1 Γ₁ Γ₂ a b :
  var_cong Γ₁ Γ₂ a b -> exists τ, inenv Γ₁ a τ.
Proof.
  intro H. induction H. unfold inenv.
  simpl. destruct (string_dec x₁ y₁); eauto. contradiction.
  unfold inenv. simpl.
  destruct (string_dec x₁ y₁); eauto.
Qed.

Lemma varcong_inenv2 Γ₁ Γ₂ a b :
  var_cong Γ₁ Γ₂ a b -> exists τ, inenv Γ₂ b τ.
Proof.
  intro H. induction H. unfold inenv.
  simpl. destruct (string_dec x₂ y₂); eauto. contradiction.
  unfold inenv. simpl.
  destruct (string_dec x₂ y₂); eauto.
Qed.

Lemma varcong_eq Γ₁ Γ₂ a b :
  var_cong Γ₁ Γ₂ a b -> Γ₁ = Γ₂ -> a = b.
Proof.
  intro H. induction H; simpl; intros.
  inv H1; auto. inv H2; auto.
Qed.  

Lemma inenv_varcong Γ a τ :
  inenv Γ a τ -> var_cong Γ Γ a a.
Proof.
  unfold inenv.
  induction Γ; simpl; intros.
  discriminate. destruct a0.
  destruct (string_dec c a). subst.
  apply vcong_here; auto.
  apply vcong_there; auto.
Qed.

Lemma env_supp_inenv Γ a :
  a ∈ ‖Γ‖ <-> exists τ, inenv Γ a τ.
Proof.
  induction Γ; simpl; split; intros.
  apply nil_elem in H. elim H.
  destruct H. inv H.
  unfold Support.support in H. simpl in H.
  unfold inenv. simpl. destruct a0.
  simpl in H.
  destruct (string_dec c a); eauto.
  apply cons_elem in H. destruct H.
  apply atom_strong_eq in H.
  elim n; auto.  
  apply IHΓ in H.
  auto.
  unfold inenv in H.
  simpl in H.
  destruct a0.
  destruct (string_dec c a).
  unfold Support.support. simpl.
  apply cons_elem; auto.
  left; auto. subst c; auto.
  apply IHΓ in H.
  unfold Support.support. simpl.
  apply cons_elem; auto.
Qed.  

Lemma term_subst_cong : forall Γ τ (m:term Γ τ) Γ' (n:term Γ' τ) Γ₁ Γ₂
  (VAR1 : varmap Γ Γ₁) (VAR2 : varmap Γ' Γ₂),
  
  (forall a1 a2 σ IN1 IN2,
    var_cong Γ Γ' a1 a2 ->
    alpha_cong Γ₁ Γ₂ σ (VAR1 a1 σ IN1) (VAR2 a2 σ IN2)) ->

  alpha_cong Γ Γ' τ m n ->

  alpha_cong Γ₁ Γ₂ τ
    (term_subst Γ Γ₁ τ VAR1 m)
    (term_subst Γ' Γ₂ τ VAR2 n).
Proof.
  intros until m; induction m; simpl; intros; auto.
  inv H0. simpl.
  apply H. auto.
  inv H0.
  apply acong_bool.
  inv H0.
  apply acong_app; auto.

  inv H0. simpl.
  apply acong_if; auto.

  inv H0. simpl.
  apply acong_lam; auto.
  apply IHm. 

(* lemma ? *)
  intros.
  unfold shift_vars', shift_vars, extend_map, weaken_map.
  hnf in IN1. hnf in IN2. simpl in IN1. simpl in IN2.
  revert IN1 IN2.
  destruct (string_dec x a1); simpl; intros.
  destruct (string_dec x₂ a2); simpl; intros.
  subst x. subst x₂. unfold eq_rect_r.
  inv IN1.
  replace IN1 with (Logic.eq_refl (Some σ)). simpl.
  replace IN2 with (Logic.eq_refl (Some σ)). simpl.
  unfold newestvar. simpl.
  apply acong_var.
  apply vcong_here; auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  inv H1. elim n; auto.
  elim H10; auto.
  destruct (string_dec x₂ a2); simpl; intros.
  subst x₂. inv H1.
  elim n; auto. elim H11; auto.
  apply alpha_cong_wk; auto.
  intros.
  apply vcong_there; auto.
  apply varcong_inenv1 in H2.
  apply env_supp_inenv in H2.
  intro. subst a. revert H2.
  apply fresh_atom_is_fresh'.
  red; intros. apply app_elem; auto.
  apply varcong_inenv2 in H2.
  apply env_supp_inenv in H2.
  intro. subst b. revert H2.
  apply fresh_atom_is_fresh'.
  red; intros. apply app_elem; auto.
  apply H. inv H1. elim n; auto. auto.
  auto.
(* end lemma? *)

  inv H0. simpl.
  apply acong_fix; auto.
  apply IHm.
(* use lemma? *)
  intros.
  unfold shift_vars', shift_vars, extend_map, weaken_map.
  hnf in IN1. hnf in IN2. simpl in IN1. simpl in IN2.
  revert IN1 IN2.
  destruct (string_dec x a1); simpl; intros.
  destruct (string_dec x₂ a2); simpl; intros.
  subst x. subst x₂. unfold eq_rect_r.
  inv IN1.
  replace IN1 with (Logic.eq_refl (Some σ0)). simpl.
  replace IN2 with (Logic.eq_refl (Some σ0)). simpl.
  unfold newestvar. simpl.
  apply acong_var.
  apply vcong_here; auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  inv H1. elim n; auto.
  elim H10; auto.
  destruct (string_dec x₂ a2); simpl; intros.
  subst x₂. inv H1.
  elim n; auto. elim H11; auto.
  apply alpha_cong_wk; auto.
  intros.
  apply vcong_there; auto.
  apply varcong_inenv1 in H2.
  apply env_supp_inenv in H2.
  intro. subst a. revert H2.
  apply fresh_atom_is_fresh'.
  red; intros. apply app_elem; auto.
  apply varcong_inenv2 in H2.
  apply env_supp_inenv in H2.
  intro. subst b. revert H2.
  apply fresh_atom_is_fresh'.
  red; intros. apply app_elem; auto.
  apply H. inv H1. elim n; auto. auto.
  auto.
(* end use lemma? *)
Qed.


Lemma eval_alpha Γ τ (m z:term Γ τ) :
  (m ⇓ z) -> forall Γ' (n:term Γ' τ),
  alpha_cong Γ Γ' τ m n -> 
  exists z', (n ⇓ z') /\ alpha_cong Γ Γ' τ z z'.
Proof.
  intro H. induction H; intros.

  inv H. exists (tbool Γ' b). split.
  apply ebool. apply acong_bool.

  inv H1.
  destruct (IHeval1 Γ' x2) as [m [??]]; auto.
  inv H3.
  destruct (IHeval2 Γ' (if b then y2 else z2)) as [n [??]]; auto.
  destruct b; auto.
  exists n.
  split; auto.
  eapply eif. eauto. auto.

  inv H. exists (tlam Γ' x₂ σ₁ σ₂ m₂).
  split. apply elam.
  apply acong_lam. auto.

  (**)
  inv H0.
  destruct (IHeval Γ' (subst Γ' σ σ x₂ m₂ (tfix Γ' x₂ σ m₂))) as [z' [??]].
  unfold subst. apply term_subst_cong; auto.
(* use lemma *)
  intros. 
  inv H1.
  unfold extend_map. simpl.
  revert IN1 IN2. unfold inenv; simpl.
  destruct (string_dec a1 a1).
  destruct (string_dec a2 a2).
  intros. inv IN1.
  replace IN1 with (Logic.eq_refl (Some σ0)). simpl.
  replace IN2 with (Logic.eq_refl (Some σ0)). simpl.
  unfold eq_rect_r; simpl. auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  elim n; auto. elim n; auto.
  unfold extend_map. simpl.
  revert IN1 IN2. unfold inenv; simpl.
  destruct (string_dec x a1).
  elim H10; auto.
  destruct (string_dec x₂ a2).
  elim H11; auto.
  intros. 
  apply acong_var. auto.
(* end use lemma *)
  exists z'. split; auto.
  eapply efix. auto.

  inv H2.
  destruct (IHeval1 Γ' n₁0 H8) as [z1' [??]].
  destruct (IHeval2 Γ' n₂0 H11) as [z2' [??]].
  inv H4.
  destruct (IHeval3 Γ' (subst Γ' σ₂ σ₁ x₂ m₂0 z2')) as [z' [??]].
  unfold subst.
  apply term_subst_cong.
(* begin lemma. *)
  intros. 
  inv H7.
  unfold extend_map. simpl.
  revert IN1 IN2. unfold inenv; simpl.
  destruct (string_dec a1 a1).
  destruct (string_dec a2 a2).
  intros. inv IN1.
  replace IN1 with (Logic.eq_refl (Some σ)). simpl.
  replace IN2 with (Logic.eq_refl (Some σ)). simpl.
  unfold eq_rect_r; simpl. auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  elim n; auto. elim n; auto.
  unfold extend_map. simpl.
  revert IN1 IN2. unfold inenv; simpl.
  destruct (string_dec x a1).
  elim H18; auto.
  destruct (string_dec x₂ a2).
  elim H19; auto.
  intros. 
  apply acong_var. auto.
(* end lemma *)
  auto.    
  exists z'; split; auto.
  eapply eapp; eauto.
Qed.

Lemma app_not_value Γ σ (x y:term Γ σ) :
  x⇓y -> forall σ₂ (m:term Γ (σ₂ ⇒ σ)) n, y = m•n -> False.
Proof.
  intro H. induction H; intros; try discriminate.
  eapply IHeval2; eauto.
  subst z.
  eapply IHeval; eauto.
  subst z.
  eapply IHeval3; eauto.
Qed.

Lemma if_not_value Γ σ (x y:term Γ σ) :
  x⇓y -> forall a b c, y = tif Γ σ a b c -> False.
Proof.
  intro H. induction H; intros; try discriminate.
  eapply IHeval2; eauto.
  subst z.
  eapply IHeval; eauto.
  subst z.
  eapply IHeval3; eauto.
Qed.

Lemma fix_not_value Γ σ (x y:term Γ σ) :
  x⇓y -> forall x m, y = tfix Γ x σ m -> False.
Proof.
  intro H. induction H; intros; try discriminate.
  eapply IHeval2; eauto.
  subst z.
  eapply IHeval; eauto.
  subst z.
  eapply IHeval3; eauto.
Qed.

Lemma alpha_cong_value Γ Γ' σ x y :
  alpha_cong Γ Γ' σ x y -> x↓ -> y↓.
Proof.
  intro H. induction H; intros.
  inv H0.
  apply ebool.
  inv H1.
  eapply app_not_value in H9; eauto. elim H9.
  eapply if_not_value in H2. elim H2. eauto.
  eapply fix_not_value in H0. elim H0. eauto.
  apply elam.
Qed.  

Lemma term_wk_ident : forall Γ σ m H,
  term_wk Γ Γ σ m H = m.
Proof.
  intros until m; induction m; simpl; intros; auto.
  f_equal.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  f_equal; auto.
  f_equal; auto.
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
  apply IHm1.
  apply IHm2.
  apply IHm3.
  f_equal.
  apply IHm.
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
  apply acong_if; auto.
  apply acong_lam.

  apply IHm; clear IHm.

(* begin lemma? *)
  intros. unfold shift_vars'. unfold shift_vars.
  unfold extend_map. simpl. unfold weaken_map. simpl.
  unfold newestvar. simpl. unfold newestvar_obligation_1. simpl.
  generalize Ha1 Ha2. unfold inenv; simpl.
  destruct (string_dec x a); simpl.
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
  assert (forall x τ, inenv Γ₂ x τ -> inenv ((fresh[Γ₂],σ₁)::Γ₂) x τ).
    intros.
    hnf. hnf in H1. simpl. simpl in H1.
    rewrite H1.
    set (q := fresh [Γ₂]).
    simpl in q. fold q.
    destruct (string_dec q x0).
    subst q.
    elimtype False.
    clear -H1 e.
    assert (x0 ∈ ‖Γ₂‖).
    apply env_supp_inenv. eauto.
    subst x0. revert H.
    apply fresh_atom_is_fresh'.
    red; intros. apply app_elem. auto.
    auto.

  apply alpha_eq_trans with
    ((fresh [Γ₂],σ₁)::Γ₂) 
    (term_wk Γ₂ ((fresh [Γ₂],σ₁)::Γ₂) σ
      (term_wk Γ₁ Γ₂ σ (VAR1 a σ Ha0) H₁) H1).
  rewrite term_wk_compose'.
  apply alpha_cong_wk.
  intros.
 apply vcong_there; auto.
  clear -H2.
  intro.
  apply varcong_inenv1 in H2.
  apply env_supp_inenv in H2. subst a0.  revert H2.
  apply fresh_atom_is_fresh'.
  red; intros. apply app_elem. auto.
  clear -H2 H₁.
    intro.
    apply varcong_inenv2 in H2.
    assert (exists τ, inenv Γ₂ b τ).
    destruct H2; eauto.
    apply env_supp_inenv in H0. subst b. revert H0.
    apply fresh_atom_is_fresh'.
    red; intros. apply app_elem. auto.
  clear -H₁ H2.
    assert (a0 = b).
    apply varcong_eq in H2; auto.
    subst a0.
    apply varcong_inenv1 in H2.
    destruct H2. apply H₁ in H.
    eapply inenv_varcong; eauto.

  apply alpha_eq_refl.
  apply alpha_cong_wk.
  intros.
  apply vcong_there.
  clear -H2.
    intro.
    apply varcong_inenv1 in H2.
    apply env_supp_inenv in H2. subst a0. revert H2.
    apply fresh_atom_is_fresh'.
    red; intros. apply app_elem; auto.
  clear -H2.
    intro.
    apply varcong_inenv2 in H2.
    apply env_supp_inenv in H2. subst b. revert H2.
    apply fresh_atom_is_fresh'.
    red; intros. apply app_elem; auto.
  auto.
  apply H.
(* end lemma ? *)

  apply acong_fix.
  apply IHm; clear IHm.
(* use lemma *)
  intros. unfold shift_vars'. unfold shift_vars.
  unfold extend_map. simpl. unfold weaken_map. simpl.
  unfold newestvar. simpl. unfold newestvar_obligation_1. simpl.
  generalize Ha1 Ha2. unfold inenv; simpl.
  destruct (string_dec x a); simpl.
  subst a. intros.
  inv Ha0. unfold eq_rect_r.
  replace Ha0 with (Logic.eq_refl (Some σ0)).
  replace Ha3 with (Logic.eq_refl (Some σ0)). simpl.
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
  assert (forall x τ, inenv Γ₂ x τ -> inenv ((fresh[Γ₂],σ)::Γ₂) x τ).
    intros.
    hnf. hnf in H1. simpl. simpl in H1.
    rewrite H1.
    set (q := fresh [Γ₂]).
    simpl in q. fold q.
    destruct (string_dec q x0).
    subst q.
    elimtype False.
    clear -H1 e.
    assert (x0 ∈ ‖Γ₂‖).
    apply env_supp_inenv. eauto.
    subst x0. revert H.
    apply fresh_atom_is_fresh'.
    red; intros. apply app_elem. auto.
    auto.

  apply alpha_eq_trans with
    ((fresh [Γ₂],σ)::Γ₂) 
    (term_wk Γ₂ ((fresh [Γ₂],σ)::Γ₂) σ0
      (term_wk Γ₁ Γ₂ σ0 (VAR1 a σ0 Ha0) H₁) H1).
  rewrite term_wk_compose'.
  apply alpha_cong_wk.
  intros.
 apply vcong_there; auto.
  clear -H2.
  intro.
  apply varcong_inenv1 in H2.
  apply env_supp_inenv in H2. subst a0.  revert H2.
  apply fresh_atom_is_fresh'.
  red; intros. apply app_elem. auto.
  clear -H2 H₁.
    intro.
    apply varcong_inenv2 in H2.
    assert (exists τ, inenv Γ₂ b τ).
    destruct H2; eauto.
    apply env_supp_inenv in H0. subst b. revert H0.
    apply fresh_atom_is_fresh'.
    red; intros. apply app_elem. auto.
  clear -H₁ H2.
    assert (a0 = b).
    apply varcong_eq in H2; auto.
    subst a0.
    apply varcong_inenv1 in H2.
    destruct H2. apply H₁ in H.
    eapply inenv_varcong; eauto.

  apply alpha_eq_refl.
  apply alpha_cong_wk.
  intros.
  apply vcong_there.
  clear -H2.
    intro.
    apply varcong_inenv1 in H2.
    apply env_supp_inenv in H2. subst a0. revert H2.
    apply fresh_atom_is_fresh'.
    red; intros. apply app_elem; auto.
  clear -H2.
    intro.
    apply varcong_inenv2 in H2.
    apply env_supp_inenv in H2. subst b. revert H2.
    apply fresh_atom_is_fresh'.
    red; intros. apply app_elem; auto.
  auto.
  apply H.
(* end use lemma *)
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
  apply acong_if; auto.

  apply acong_lam.
  eapply alpha_eq_trans. 2: apply IHm. clear IHm.

(* begin lemma? *)
  apply term_subst_cong.
  clear. unfold shift_vars', shift_vars. simpl.
  intros.
  simpl.
  unfold inenv in *. simpl in *.
  unfold extend_map.
  destruct (string_dec x a1).
  unfold eq_rect_r. simpl.
  subst a1. inv IN1.
  replace IN1 with (Logic.eq_refl (Some σ)).
  unfold newestvar; simpl.
  unfold newestvar_obligation_1. simpl.
  revert IN2.
  destruct (string_dec x a2).
  subst a2; intros.
  replace IN2 with (Logic.eq_refl (Some σ)).
  simpl.
  unfold weaken_map; simpl.
  
  set (q := (fresh_atom (‖Γ₂‖ ++ nil))).
  simpl in *. fold q.
  destruct (string_dec q q). simpl.
  apply acong_var.
  apply vcong_here; auto.
  elim n; auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  intros.
  elim n. inv H; auto. elim H7; auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  revert IN2.
  destruct (string_dec x a2).
  subst a2; intros.
  elim n. inv H; auto. elim H8; auto.
  intros.
  simpl.
  unfold weaken_map; simpl.
  simpl.
  assert (a1 = a2).
  inv H; auto.
  clear -H9.
  apply varcong_eq in H9; auto.
  subst a2.
  replace IN2 with IN1.

  apply term_subst_wk_cong. simpl. intros.
  set (q1 := fresh [ Γ₂ ]). 
  set (q2 := fresh [ Γ₃ ]).
  unfold inenv in *. simpl in *.
  revert Ha2.
  simpl in *. fold q1. fold q2.  
  destruct (string_dec q1 a).
  subst a.
  elimtype False.
  
  assert (q1 ∈ ‖Γ₂‖).
  apply env_supp_inenv. eauto.
  revert H1. unfold q1.
  apply fresh_atom_is_fresh'.
  red; intros. apply app_elem; auto.
  intros.
  apply alpha_cong_wk.
  intros. apply vcong_there; auto.
    intro.
    apply varcong_inenv1 in H1.
    apply env_supp_inenv in H1. subst a0.
    revert H1. apply fresh_atom_is_fresh'.
    red; intros. apply app_elem; auto.
  unfold q2.
    intro.
    apply varcong_inenv2 in H1.
    apply env_supp_inenv in H1. subst b.
    revert H1. apply fresh_atom_is_fresh'.
    red; intros. apply app_elem; auto.

  replace Ha2 with Ha1.
  apply alpha_eq_refl.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply alpha_eq_refl.
(* end lemma *)

  apply acong_fix.
  eapply alpha_eq_trans. 2: apply IHm. clear IHm.

(* use lemma *)
  apply term_subst_cong.
  clear. unfold shift_vars', shift_vars. simpl.
  intros.
  simpl.
  unfold inenv in *. simpl in *.
  unfold extend_map.
  destruct (string_dec x a1).
  unfold eq_rect_r. simpl.
  subst a1. inv IN1.
  replace IN1 with (Logic.eq_refl (Some σ0)).
  unfold newestvar; simpl.
  unfold newestvar_obligation_1. simpl.
  revert IN2.
  destruct (string_dec x a2).
  subst a2; intros.
  replace IN2 with (Logic.eq_refl (Some σ0)).
  simpl.
  unfold weaken_map; simpl.
  
  set (q := (fresh_atom (‖Γ₂‖ ++ nil))).
  simpl in *. fold q.
  destruct (string_dec q q). simpl.
  apply acong_var.
  apply vcong_here; auto.
  elim n; auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  intros.
  elim n. inv H; auto. elim H7; auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  revert IN2.
  destruct (string_dec x a2).
  subst a2; intros.
  elim n. inv H; auto. elim H8; auto.
  intros.
  simpl.
  unfold weaken_map; simpl.
  simpl.
  assert (a1 = a2).
  inv H; auto.
  clear -H9.
  apply varcong_eq in H9; auto.
  subst a2.
  replace IN2 with IN1.

  apply term_subst_wk_cong. simpl. intros.
  set (q1 := fresh [ Γ₂ ]). 
  set (q2 := fresh [ Γ₃ ]).
  unfold inenv in *. simpl in *.
  revert Ha2.
  simpl in *. fold q1. fold q2.  
  destruct (string_dec q1 a).
  subst a.
  elimtype False.
  
  assert (q1 ∈ ‖Γ₂‖).
  apply env_supp_inenv. eauto.
  revert H1. unfold q1.
  apply fresh_atom_is_fresh'.
  red; intros. apply app_elem; auto.
  intros.
  apply alpha_cong_wk.
  intros. apply vcong_there; auto.
    intro.
    apply varcong_inenv1 in H1.
    apply env_supp_inenv in H1. subst a0.
    revert H1. apply fresh_atom_is_fresh'.
    red; intros. apply app_elem; auto.
  unfold q2.
    intro.
    apply varcong_inenv2 in H1.
    apply env_supp_inenv in H1. subst b.
    revert H1. apply fresh_atom_is_fresh'.
    red; intros. apply app_elem; auto.

  replace Ha2 with Ha1.
  apply alpha_eq_refl.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  apply alpha_eq_refl.
(* end use lemma *)  
Qed.  


Lemma subst_weaken_alpha Γ Γ' σ
  (x:term Γ σ) (y:term Γ' σ) :

  alpha_cong Γ Γ' σ x y ->

  forall Γ₁ Γ₂ (VAR:varmap Γ₁ Γ₂) H,

  (forall a b τ H1 H2, var_cong Γ Γ' a b ->
    alpha_cong Γ₂ Γ' τ (VAR a τ H1) (tvar Γ' b τ H2)) ->
    
  alpha_cong _ _ σ (term_subst _ _ σ VAR (term_wk _ _ _ x H)) y.
Proof.
  intro. induction H; simpl; intros.
  apply H1. auto.
  apply acong_bool.
  apply acong_app; auto.
  apply acong_if; auto.

  apply acong_fix; auto.
  apply IHalpha_cong.
(* use lemma *)
  intros.
  unfold shift_vars'.
  unfold shift_vars. simpl.
  unfold newestvar. unfold extend_map; simpl.
  revert H2. unfold inenv; simpl.
  unfold newestvar_obligation_1. simpl.
  destruct (string_dec x₁ a). intros.
  subst a. inv H2.
  replace H2 with (refl_equal (Some τ)).
  unfold eq_rect_r; simpl.
  apply acong_var.
  apply vcong_here; auto.
  inv H4; auto. elim H12; auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  intros.  
  inv H4. elim n; auto.
  unfold weaken_map. simpl.
  assert (inenv Γ' b τ).
  revert H3. unfold inenv; simpl.
  destruct (string_dec x₂ b).
  contradiction. auto.
  generalize (H1 a b τ H2 H5 H14). intros.
  inv H6. rewrite <- H7. simpl.
  apply acong_var.
  apply vcong_there; auto.
  clear -H₁. intro.
  assert (x₁0 ∈ ‖Γ₂‖).
  apply env_supp_inenv. eauto.
  subst x₁0. revert H0.
  apply fresh_atom_is_fresh'.
  red; intros.
  apply app_elem; auto.
(* end lemma *)

  apply acong_lam; auto.
  apply IHalpha_cong.

(* begin lemma *)
  intros.
  unfold shift_vars'.
  unfold shift_vars. simpl.
  unfold newestvar. unfold extend_map; simpl.
  revert H2. unfold inenv; simpl.
  unfold newestvar_obligation_1. simpl.
  destruct (string_dec x₁ a). intros.
  subst a. inv H2.
  replace H2 with (refl_equal (Some τ)).
  unfold eq_rect_r; simpl.
  apply acong_var.
  apply vcong_here; auto.
  inv H4; auto. elim H12; auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  intros.  
  inv H4. elim n; auto.
  unfold weaken_map. simpl.
  assert (inenv Γ' b τ).
  revert H3. unfold inenv; simpl.
  destruct (string_dec x₂ b).
  contradiction. auto.
  generalize (H1 a b τ H2 H5 H14). intros.
  inv H6. rewrite <- H7. simpl.
  apply acong_var.
  apply vcong_there; auto.
  clear -H₁. intro.
  assert (x₁0 ∈ ‖Γ₂‖).
  apply env_supp_inenv. eauto.
  subst x₁0. revert H0.
  apply fresh_atom_is_fresh'.
  red; intros.
  apply app_elem; auto.
(* end lemma *)
Qed.

Lemma subst_alpha_ident Γ Γ' σ
  (x:term Γ σ) (y:term Γ' σ) :
  alpha_cong Γ Γ' σ x y ->

  forall Γ₂ (VAR:varmap Γ Γ₂),

  (forall a b τ H1 H2, var_cong Γ Γ' a b ->
    alpha_cong Γ₂ Γ' τ (VAR a τ H1) (tvar Γ' b τ H2)) ->
    
  alpha_cong _ _ σ (term_subst _ _ σ VAR x) y.
Proof.
  intros.
  rewrite <- (term_wk_ident _ _ x (fun a b H => H)).
  apply subst_weaken_alpha; auto.
Qed.

Lemma extend_shift_alpha : forall
  (Γ : env)
  (x : atom)
  (σ₁ : ty)
  (VAR : varmap Γ nil)
  (n : term nil σ₁)
  (a1 a2 : atom)
  (σ : ty)
  (IN1 : inenv ((x, σ₁) :: Γ) a1 σ)
  (IN2 : inenv ((x, σ₁) :: Γ) a2 σ)
  (x':atom) Hx,

   var_cong ((x, σ₁) :: Γ) ((x, σ₁) :: Γ) a1 a2 ->

   alpha_cong nil nil σ
     (varmap_compose ((x, σ₁) :: Γ) ((x', σ₁) :: nil) nil
        (extend_map nil nil (tvar nil) x' σ₁ n)
        (shift_vars Γ nil x x' σ₁ Hx VAR) a1 σ IN1)
     (extend_map Γ nil VAR x σ₁ n a2 σ IN2).
Proof.
  intros.
  unfold varmap_compose.
  unfold shift_vars.
  unfold extend_map at 2. simpl.
  unfold newestvar. simpl.
  unfold newestvar_obligation_1. simpl.
  revert IN1. unfold inenv. simpl.
  destruct (string_dec x a1).  
  subst a1.
  assert (x = a2).
  inv H. auto. elim H7; auto.
  subst a2.
  intro. inv IN1.
  replace IN1 with (refl_equal (Some σ)). simpl.
  unfold extend_map. simpl.
  revert IN2. unfold inenv; simpl.
  destruct (string_dec x x).
  intros.
  destruct (string_dec x' x').
  unfold eq_rect_r; simpl.
  replace IN2 with (refl_equal (Some σ)). simpl.
  apply alpha_eq_refl.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  elim n0; auto.  
  elim n0; auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  intros.   
  assert (x <> a2 /\ var_cong Γ Γ a1 a2).
  inv H; auto. elim n0. auto.
  destruct H0.
  assert (a1 = a2).
  cut (forall Γ₁ Γ₂ a b, var_cong Γ₁ Γ₂ a b -> Γ₁ = Γ₂ -> a = b).
  intros. eapply H2; eauto.
  clear.
  intros. induction H.
  inv H0; auto.
  inv H0; auto.
  subst a2.
  revert IN2. unfold inenv. simpl.
  unfold extend_map at 2. simpl.
  destruct (string_dec x a1).
  contradiction.
  simpl; intros.
  unfold weaken_map.
  replace IN2 with IN1.
  2: apply Eqdep_dec.UIP_dec; decide equality; decide equality.
  clear.
  
  unfold extend_map. simpl.
  apply subst_weaken_alpha.
  apply alpha_eq_refl.
  intros.
  inv H.
Qed.

Lemma LR_alpha_cong τ : forall m1 m2 h,
  alpha_cong nil nil τ m1 m2 ->
  LR τ m1 h -> LR τ m2 h.
Proof.
  induction τ; simpl; intros.
  destruct H0 as [b [??]]. exists b; split; auto.
  inv H; try discriminate. auto.

  destruct (H0 n h' H1 H2 H3 H4) as [z1 [z2 [?[??]]]].
  destruct (eval_alpha _ _ _ _ H5 _ (m2•n)) as [z' [??]].
  apply acong_app; auto.
  apply alpha_eq_refl.
  exists z'. exists z2. split; auto. split; auto.
  apply alpha_eq_trans with nil z1; auto.
  apply alpha_eq_sym; auto.
Qed.

(* FIXME: move this somewhere else; share with skiy.v ? *)
Lemma semvalue_sup (B:∂PLT) (XS:dirset (PLT.homset_cpo _ (cxt nil) (U B))) : 
  semvalue (∐XS) -> exists x, x ∈ XS /\ semvalue x.
Proof.
  intros.
  destruct (H ENV.empty_cxt_inh) as [q ?].
  simpl in H0.
  apply union_axiom in H0.
  destruct H0 as [q' [??]].
  apply image_axiom2 in H0.
  destruct H0 as [q'' [??]].
  simpl in *.
  exists q''. split; auto.
  red; intro. 
  exists q. rewrite <- H2; auto.
  revert H1. apply member_eq.
  split; split; simpl; auto.
  apply ENV.empty_cxt_le.
  apply ENV.empty_cxt_le.
Qed.

Lemma plt_semvalue_bot (Γ:PLT) (A:∂PLT) (x:Γ) :
  semvalue (⊥ : Γ → U A) -> False.
Proof.  
  intros.
  red in H.
  destruct (H x).
  simpl in H0.
  unfold plt_hom_adj' in H0.
  rewrite (PLT.compose_hom_rel false _ _ _ η (U·(cppo_bot (PLT.homset_cpo true (L Γ) A)))) in H0.
  destruct H0 as [y [??]].
  simpl in H0. apply adj_unit_rel_elem in H0.
  rewrite (U_hom_rel _ _ (cppo_bot (PLT.homset_cpo true (L Γ) A))) in H1.
  destruct H1. discriminate.
  destruct H1 as [?[?[?[??]]]].
  simpl in H1.
  apply union_axiom in H1.
  destruct H1 as [?[??]].
  apply image_axiom2 in H1.
  destruct H1 as [?[??]]. apply empty_elem in H1. auto.
Qed.

Lemma LR_admissible τ : 
  forall m (XS:dirset (PLT.homset_cpo _ _ (U (tydom τ)))),
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
  destruct a.
  assert ((c,Some b : U (flat enumbool)) ∈ PLT.hom_rel x1).
  apply H6.
  unfold flat_elem'.
  apply PLT.compose_hom_rel. exists (Some c).
  split. simpl. apply adj_unit_rel_elem. auto.
  apply U_hom_rel. right.
  exists c. exists b. split; auto.
  apply PLT.compose_hom_rel; auto.
  exists tt. split.
  simpl. apply eprod_elem. split; simpl.
  apply eff_complete. apply single_axiom; auto.
  simpl. apply single_axiom; auto.
  destruct H3. apply H9.
  unfold flat_elem'.
  apply PLT.compose_hom_rel.
  exists (Some c). split.
  simpl. apply adj_unit_rel_elem; simpl; auto.
  apply U_hom_rel.
  destruct c0; auto. right.
  exists c. exists c0. split; auto.
  apply PLT.compose_hom_rel.
  exists tt.
  split. simpl.
  apply eprod_elem. split.
  apply eff_complete. apply single_axiom; auto.
  simpl. apply single_axiom; auto.
  cut (c0 = b). intros. subst c0; auto.
  destruct (PLT.hom_directed _ _ _ x1 c ((Some c0::Some b::nil))).
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
  destruct (H4 ENV.empty_cxt_inh) as [q ?].
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
  revert H8. apply PLT.hom_order; auto.
  apply ENV.empty_cxt_le.

  destruct H7 as [q [??]].
  assert (semvalue q).
  apply semvalue_app_out1' in H8. auto.
  destruct (H0 q H7 H9 n h' H1 H2 H3 H8) as [z1 [z2 [?[??]]]].
  exists z1. exists z2. split; auto. split; auto.
  cut (LR τ2 z2 (∐(image g XS))).
  apply LR_equiv; auto.
  apply IHτ2; auto.
  rewrite <- H6. auto.

  intros.
  apply image_axiom2 in H13. destruct H13 as [y [??]].
  rewrite H15 in H14.
  simpl in H14.
  assert (semvalue y).
  apply semvalue_app_out1' in H14. auto.
  destruct (H0 y H13 H16 n h' H1 H2 H3) as [z1' [z2' [?[??]]]]; auto.
  assert (z1 = z1').
  eapply eval_eq; eauto. subst z1'.
  cut (LR τ2 z2' x). 
  apply LR_alpha_cong. 
  apply alpha_eq_trans with nil z1; auto.
  apply alpha_eq_sym; auto.
  revert H19.
  apply LR_equiv; auto.
Qed.


(**  The fundamental lemma states that every term stands in the logical relation
     with its denotation when applied to related substitutions.
  *)
Lemma fundamental_lemma : forall Γ τ (m:term Γ τ) 
  (VAR:varmap Γ nil) (VARh : cxt nil → cxt Γ),
  (forall a σ (H:inenv Γ a σ), 
       semvalue (castty H ∘ proj Γ a ∘ VARh) ->
       exists z,
         (VAR a σ H ⇓ z) /\
         LR σ z (castty H ∘ proj Γ a ∘ VARh)) ->
  semvalue (〚m〛 ∘ VARh) ->
  exists z,
    eval nil τ (term_subst Γ nil τ VAR m) z /\
    LR τ z (〚m〛 ∘ VARh ).
Proof.
  induction m; simpl; intros.

  (* var case *)  
  auto.
  
  (* bool case *)
  exists (tbool nil n). 
  split. apply ebool.
  exists n. split; auto.
  symmetry. apply flat_elem'_ignores_arg.

  (* application case *)  
  rewrite <- (cat_assoc PLT) in H0.
  rewrite (PLT.pair_compose_commute false) in H0.
  destruct (IHm1 VAR VARh H) as [z1 [??]]; auto.
  apply semvalue_app_out1' in H0. auto.
  destruct (IHm2 VAR VARh H) as [z2 [??]].
  apply semvalue_app_out2' in H0. auto.
  simpl in H2.
  destruct (H2 z2 (〚 m2 〛 ∘ VARh)) as [z3 [z3' [?[??]]]]; auto.
  eapply eval_value. eauto.
  apply semvalue_app_out2' in H0. auto.
  exists z3. split.
  inv H5.
  eapply eapp; eauto.
  eapply eval_trans. apply H1. eauto.
  replace z2 with n₂. auto.
  eapply eval_eq. eauto.
  eapply eval_value; eauto.
  cut (LR σ₂ z3' (strict_app' ∘ 〈〚 m1 〛, 〚 m2 〛〉 ∘ VARh)).
  apply LR_alpha_cong.
  apply alpha_eq_sym; auto.
  revert H7.
  apply LR_equiv.
  rewrite <- (cat_assoc PLT).
  apply cat_respects; auto.
  symmetry; apply PLT.pair_compose_commute.

  (* if case *)
  destruct (IHm1 VAR VARh H) as [x' [??]]; auto.
  rewrite <- (cat_assoc PLT) in H0.
  rewrite (PLT.pair_compose_commute false) in H0.
  rewrite (cat_ident2 PLT) in H0.
  apply flat_cases'_semvalue in H0. auto.

  simpl in H2.
  destruct H2 as [b [??]].
  destruct b.

  destruct (IHm2 VAR VARh H) as [y' [??]].
  rewrite <- (cat_assoc PLT) in H0.
  rewrite (PLT.pair_compose_commute false) in H0.
  rewrite H3 in H0.
  rewrite (cat_ident2 PLT) in H0.
  rewrite (flat_cases_elem') in H0.
  auto.
  exists y'.
  split; auto.
  subst x'.
  eapply eif; eauto.
  revert H5.
  apply LR_equiv.
  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  rewrite (cat_ident2 PLT).
  rewrite H3.
  rewrite flat_cases_elem'. auto.

  destruct (IHm3 VAR VARh H) as [z' [??]].
  rewrite <- (cat_assoc PLT) in H0.
  rewrite (PLT.pair_compose_commute false) in H0.
  rewrite H3 in H0.
  rewrite (cat_ident2 PLT) in H0.
  rewrite (flat_cases_elem') in H0.
  auto.
  exists z'.
  split; auto.
  subst x'.
  eapply eif; eauto.
  revert H5.
  apply LR_equiv.
  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  rewrite (cat_ident2 PLT).
  rewrite H3.
  rewrite flat_cases_elem'. auto.
  
  (* lam case *)  
  econstructor. split. apply elam.
  intros.
  set (VAR' := extend_map Γ nil VAR x σ₁ n).
  set (VARh' := bind Γ x σ₁ ∘ 〈 VARh, h' 〉). 
  destruct (IHm VAR' VARh') as [z [??]]; clear IHm.
  simpl; intros.

  unfold VARh'.
  cut (
    exists z : term nil σ,
     (VAR' a σ H5 ⇓ z) /\
     LR σ z (castty H5 ∘ (proj ((x, σ₁) :: Γ) a ∘ bind Γ x σ₁) ∘ 〈VARh, h'〉)).
  intros [z [??]]. exists z. split; auto.
  revert H8. apply LR_equiv.
  rewrite (cat_assoc PLT).
  rewrite (cat_assoc PLT). auto.
  assert (semvalue (castty H5 ∘ (proj ((x,σ₁)::Γ) a ∘ bind Γ x σ₁) ∘ 〈 VARh, h'〉)).
  rewrite (cat_assoc PLT).
  unfold VARh' in H6.
  rewrite (cat_assoc PLT) in H6.
  auto.  
  revert H7. clear H6.
  generalize (ENV.proj_bind_eq x σ₁ a Γ).
  generalize (ENV.proj_bind_neq x σ₁ a Γ).
  set (p := (proj ((x,σ₁)::Γ) a ∘ bind Γ x σ₁)).
  simpl in *. fold p. clearbody p.
  revert p.
  revert H5. unfold inenv; simpl.
  subst VAR' VARh'. simpl.
  unfold extend_map; simpl.
  unfold ENV.lookup_neq. simpl.
  unfold ENV.lookup_eq. simpl.
  destruct (string_dec x a); simpl; intros.
  inv H5.
  replace H5 with (Logic.eq_refl (Some σ)).
  unfold eq_rect_r; simpl.
  exists n. split; auto.
  revert H1. apply LR_equiv.
  rewrite H7.
  rewrite <- (cat_assoc PLT).
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute2.
  rewrite (cat_assoc PLT).
  rewrite cast_refl.
  rewrite (cat_ident2 PLT).
  rewrite (cat_ident2 PLT).
  auto. auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.

  destruct (H a σ H5) as [z [??]].
  rewrite (H6 n0) in H8.
  rewrite cast_refl in H8.
  rewrite (cat_ident2 PLT) in H8.
  rewrite <- (cat_assoc PLT) in H8.
  rewrite <- (cat_assoc PLT) in H8.
  rewrite (PLT.pair_commute1) in H8.
  rewrite (cat_assoc PLT) in H8.
  auto.
  exists z; split; auto.
  revert H10. apply LR_equiv.
  rewrite (H6 n0).
  rewrite cast_refl.
  rewrite (cat_ident2 PLT).
  rewrite <- (cat_assoc PLT).
  rewrite <- (cat_assoc PLT).
  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_commute1).
  auto.

  rewrite strict_curry_app2' in H4.
  unfold VARh'.
  rewrite (cat_assoc PLT). auto.
  auto.

  assert (alpha_cong _ _ _ 
    (term_subst ((x, σ₁) :: Γ) nil σ₂ VAR' m)
    (subst nil σ₂ σ₁ (fresh_atom nil) 
      (term_subst ((x, σ₁) :: Γ) ((fresh_atom nil, σ₁) :: nil) σ₂
             (shift_vars' Γ nil x σ₁ VAR) m)
      n)).
    unfold VAR'.
    unfold subst. 
    apply alpha_eq_sym.
    eapply alpha_eq_trans. apply alpha_eq_sym. apply compose_term_subst.
    apply term_subst_cong.
    unfold shift_vars'.
    intros. apply extend_shift_alpha; auto.
    apply alpha_eq_refl.

  destruct (eval_alpha _ _ _ _ H5 _ _ H7) as [q' [??]].
  exists q'. exists z.
  split.
  eapply eapp. apply elam. eauto. auto.
  split. apply alpha_eq_sym. auto.

  revert H6. apply LR_equiv.
  rewrite strict_curry_app2'.
  unfold VARh'.
  rewrite (cat_assoc PLT). auto.
  auto.

  (* fix case *)
  revert VAR VARh H H0.
  unfold fixes.
  apply scott_induction.
  red; split.
  intros.
  rewrite plt_bot_chomp in H0.
  apply plt_semvalue_bot in H0.
  elim H0.
  apply ENV.empty_cxt_inh.

  intros.
  assert (∐XS ∘ VARh ≈ ∐(image (precompose _ VARh) XS)).
  destruct (CPO.continuous_sup' _ _ _ (precompose (U (tydom σ)) VARh)).
  apply H3. apply (precompose_continuous false _ _ (U (tydom σ)) VARh).
  rewrite H3 in H2.
  destruct (semvalue_sup _ (image (precompose (U (tydom σ)) VARh) XS) H2)
     as [q [??]].
  apply image_axiom2 in H4.  
  destruct H4 as [q' [??]]. simpl in H6.
  rewrite H6 in H5.
  destruct (H0 q' H4 VAR VARh H1 H5) as [z [??]].
  exists z. split; auto.
  cut (LR σ z (∐(image (precompose (U (tydom σ)) VARh) XS))).
  apply LR_equiv. auto.
  apply LR_admissible; auto.
  intros. apply image_axiom2 in H9.
  destruct H9 as [w [??]]. simpl in H11.
  rewrite H11 in H10.
  destruct (H0 w H9 VAR VARh H1 H10) as [z' [??]].
  assert (z = z').
  eapply eval_eq; eauto. subst z'.
  revert H13; apply LR_equiv; auto.

  intros.
  destruct (H0 VAR VARh H1) as [z [??]].
  rewrite H; auto.
  exists z. split; auto.
  revert H4. apply LR_equiv. rewrite H; auto.

  simpl; intros. unfold fixes_step in H1. unfold fixes_step.
  rewrite PLT.curry_apply2 in H1.
  repeat rewrite <- (cat_assoc PLT) in H1.
  set (n := (tfix nil (fresh_atom nil) σ
        (term_subst ((x, σ) :: Γ) ((fresh_atom nil, σ) :: nil) σ
           (shift_vars' Γ nil x σ VAR) m))).
  set (VAR' := extend_map Γ nil VAR x σ n).
  set (VARh' := bind Γ x σ ∘ 〈 VARh, x0 ∘ VARh 〉). 
  destruct (IHm VAR' VARh') as [z [??]]; clear IHm.
  simpl; intros.

  unfold VARh'.
  cut (
    exists z : term nil σ0,
     (VAR' a σ0 H2 ⇓ z) /\
     LR σ0 z (castty H2 ∘ (proj ((x, σ) :: Γ) a ∘ bind Γ x σ) ∘ 〈VARh, x0 ∘ VARh〉)).
  intros [z [??]]. exists z. split; auto.
  revert H5. apply LR_equiv.
  rewrite (cat_assoc PLT).
  rewrite (cat_assoc PLT). auto.
  assert (semvalue (castty H2 ∘ (proj ((x,σ)::Γ) a ∘ bind Γ x σ) ∘ 〈 VARh, x0 ∘ VARh〉)).
  rewrite (cat_assoc PLT).
  unfold VARh' in H3.
  rewrite (cat_assoc PLT) in H3.
  auto.  
  revert H4. clear H3.
  generalize (ENV.proj_bind_eq x σ a Γ).
  generalize (ENV.proj_bind_neq x σ a Γ).
  set (p := (proj ((x,σ)::Γ) a ∘ bind Γ x σ)).
  simpl in *. fold p. clearbody p.
  revert p.
  revert H2. unfold inenv; simpl.
  subst VAR' VARh'. simpl.
  unfold extend_map; simpl.
  unfold ENV.lookup_neq. simpl.
  unfold ENV.lookup_eq. simpl.
  destruct (string_dec x a); simpl; intros.
  injection H2. intro. subst σ0.
  replace H2 with (Logic.eq_refl (Some σ)).
  unfold eq_rect_r; simpl.
  destruct (H VAR VARh); auto.
  rewrite (H4 e) in H5.
  rewrite cast_refl in H5.
  rewrite (cat_ident2 PLT) in H5.
  rewrite <- (cat_assoc PLT) in H5.
  rewrite PLT.pair_commute2 in H5.
  replace H2 with (Logic.eq_refl (Some σ)) in H5.
  rewrite cast_refl in H5.
  rewrite (cat_ident2 PLT) in H5.
  auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.
  destruct H6.  
  exists x1; split; auto.
  revert H7. apply LR_equiv.
  rewrite (H4 e).
  rewrite cast_refl.
  rewrite (cat_ident2 PLT).
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute2.
  rewrite (cat_ident2 PLT).
  auto.
  apply Eqdep_dec.UIP_dec. decide equality. decide equality.

  destruct (H0 a σ0 H2) as [z [??]].
  rewrite (H3 n0) in H5.
  rewrite cast_refl in H5.
  rewrite (cat_ident2 PLT) in H5.
  rewrite <- (cat_assoc PLT) in H5.
  rewrite <- (cat_assoc PLT) in H5.
  rewrite (PLT.pair_commute1) in H5.
  rewrite (cat_assoc PLT) in H5.
  auto.
  exists z; split; auto.
  revert H7. apply LR_equiv.
  rewrite (H3 n0).
  rewrite cast_refl.
  rewrite (cat_ident2 PLT).
  rewrite <- (cat_assoc PLT).
  rewrite <- (cat_assoc PLT).
  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_commute1).
  auto.

  unfold VARh'.
  rewrite (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false) in H1.
  rewrite (cat_ident2 PLT) in H1.
  rewrite (cat_assoc PLT) in H1.
  auto.

  assert (alpha_cong _ _ _ 
    (term_subst ((x, σ) :: Γ) nil σ VAR' m)
    (subst nil σ σ (fresh_atom nil) 
      (term_subst ((x, σ) :: Γ) ((fresh_atom nil, σ) :: nil) σ
             (shift_vars' Γ nil x σ VAR) m)
      n)).
    unfold VAR'.
    unfold subst. 
    apply alpha_eq_sym.
    eapply alpha_eq_trans. apply alpha_eq_sym. apply compose_term_subst.
    apply term_subst_cong.
    unfold shift_vars'.
    intros. apply extend_shift_alpha; auto.
    apply alpha_eq_refl.

  destruct (eval_alpha _ _ _ _ H2 _ _ H4) as [q' [??]].
  exists q'.
  split.
  eapply efix. auto.
  cut (LR σ q' (〚m〛 ∘ VARh')).
  apply LR_equiv.
  rewrite PLT.curry_apply2.
  unfold VARh'.
  rewrite <- (cat_assoc PLT).
  rewrite (PLT.pair_compose_commute false).
  rewrite (cat_ident2 PLT).
  rewrite (cat_assoc PLT).
  auto.

  revert H3.
  apply LR_alpha_cong. auto.

Qed.

(**  A simpified form of the fundamental lemma that follows
     from the inductively-strong one above.
  *)
Lemma fundamental_lemma' : forall τ (m:term nil τ),
  semvalue 〚m〛 -> exists z, eval nil τ m z /\ LR τ z 〚 m 〛.
Proof.
  intros.
  destruct (fundamental_lemma nil τ m (tvar nil) id) as [z [??]].
  intros. discriminate.
  rewrite (cat_ident1 PLT). auto.
  destruct (eval_alpha _ _ _ _ H0 nil m) as [q [??]].
  apply subst_alpha_ident. apply alpha_eq_refl.
  intros. inv H4.
  exists q. split; auto.
  cut (LR τ z 〚m〛).  
  apply LR_alpha_cong; auto.
  revert H1. apply LR_equiv.
  apply cat_ident1.
Qed.

Lemma closed_bools_semvalue : forall Γ τ (m z:term Γ τ),
  m ⇓ z -> Γ = nil -> τ = 2%ty -> semvalue 〚z〛.
Proof.
  do 4 intro. 
  revert m; case z; intros; subst; simpl.
  inv i.
  apply flat_elem'_semvalue.
  elimtype False. eapply app_not_value; eauto.
  elimtype False. eapply if_not_value; eauto.
  discriminate.
  elimtype False. eapply fix_not_value; eauto.
Qed.


(**  Now we define contextual equivalance.  Contexts here are
     given in "inside-out" form, which makes the induction in the
     adequacy proof significantly easier.
  *)

Inductive context τ : env -> ty -> Type :=
  | cxt_top : context τ nil τ
  | cxt_if : forall Γ σ,
                    term Γ σ ->
                    term Γ σ ->
                    context τ Γ σ ->
                    context τ Γ ty_bool
  | cxt_appl : forall Γ σ₁ σ₂,
                    term Γ σ₁ ->
                    context τ Γ σ₂ ->
                    context τ Γ (σ₁ ⇒ σ₂)
  | cxt_appr : forall Γ σ₁ σ₂,
                    term Γ (σ₁ ⇒ σ₂) ->
                    context τ Γ σ₂ ->
                    context τ Γ σ₁
  | cxt_fix : forall Γ (x:atom) σ,
                    context τ Γ σ ->
                    context τ ((x,σ)::Γ) σ

  | cxt_lam : forall Γ (x:atom) σ₁ σ₂,
                    context τ Γ (σ₁ ⇒ σ₂) ->
                    context τ ((x,σ₁)::Γ) σ₂.

Fixpoint plug τ Γ σ (C:context τ Γ σ) : term Γ σ -> term nil τ :=
  match C in context _ Γ' σ' return term Γ' σ' -> term nil τ with
  | cxt_top => fun x => x
  | cxt_if Γ σ y z C' => fun x => plug τ _ _ C' (tif Γ σ x y z)
  | cxt_appl Γ σ₁ σ₂ t C' => fun x => plug τ _ _ C' (tapp x t)
  | cxt_appr Γ σ₁ σ₂ t C' => fun x => plug τ _ _ C' (tapp t x)
  | cxt_lam  Γ a σ₁ σ₂ C' => fun x => plug τ _ _ C' (tlam Γ a σ₁ σ₂ x)
  | cxt_fix Γ a σ C' => fun x => plug τ _ _ C' (tfix Γ a σ x)
  end.

Definition cxt_eq τ Γ σ (m n:term Γ σ):=
  forall (C:context τ Γ σ) (z:term nil τ),
    eval nil τ (plug τ Γ σ C m) z <-> eval nil τ (plug τ Γ σ C n) z.



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
  split; intros.

  destruct (fundamental_lemma' _ m) as [zm [??]]. 
  assert (semvalue 〚z〛).
  eapply closed_bools_semvalue; eauto.
  apply soundness in H0.
  rewrite H0. auto.
  destruct (fundamental_lemma' _ n) as [zn [??]].
  rewrite <- H.
  assert (semvalue 〚z〛).
  eapply closed_bools_semvalue; eauto.
  apply soundness in H0.
  rewrite H0. auto.
  destruct H2 as [bm [??]].
  destruct H4 as [bn [??]].
  assert (bm = bn).
  rewrite H in H5.
  rewrite H5 in H6.
  apply flat_elem'_inj in H6. auto.
  exact (ENV.empty_cxt_inh).
  subst bn.
  assert (z = (tbool nil bm)).
  eapply eval_eq; eauto.
  subst; auto.
  subst; auto.

  destruct (fundamental_lemma' _ m) as [zm [??]].
  assert (semvalue 〚z〛).
  eapply closed_bools_semvalue; eauto.
  apply soundness in H0.
  rewrite H. rewrite H0. auto.
  destruct (fundamental_lemma' _ n) as [zn [??]]. 
  assert (semvalue 〚z〛).
  eapply closed_bools_semvalue; eauto.
  apply soundness in H0.
  rewrite H0. auto.
  simpl in *.
  destruct H2 as [bm [??]].
  destruct H4 as [bn [??]].
  subst zm zn. 
  simpl in *.
  rewrite H in H5.
  rewrite H5 in H6.
  assert (bm = bn).
  apply flat_elem'_inj in H6. auto.
  exact (ENV.empty_cxt_inh).
  subst bn.
  assert (z = (tbool nil bm)).
  eapply eval_eq; eauto.
  subst z. auto.

  simpl; intros.
  apply IHC. simpl.
  apply cat_respects; auto.
  apply PLT.pair_eq; auto.

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
  apply fixes_eq.
  apply PLT.curry_eq.
  apply cat_respects; auto.

  simpl; intros.
  apply IHC. simpl.
  apply strict_curry'_eq.
  apply cat_respects; auto.
Qed.

Corollary denote_bottom_nonvalue : forall τ (m:term nil τ),
  (~exists z, eval nil τ m z) <-> 〚m〛 ≈ ⊥.
Proof.
  intros. split; intro.

  split. 2: apply bottom_least.
  hnf. intros [u x] Hx. destruct x.
  elimtype False.
  destruct (fundamental_lemma' τ m) as [z [??]].
  red; intros. simpl.
  exists c.
  revert Hx. apply PLT.hom_order; auto.
  apply ENV.empty_cxt_le.

  elim H. eauto.
  apply PLT.compose_hom_rel.    
  simpl. exists None.
  split.
  apply adj_unit_rel_elem. hnf; auto.
  apply U_hom_rel. auto.

  intros [z ?].
  assert (denote nil τ z ≈ ⊥).
  rewrite <- soundness; eauto.
  assert (z↓).
  eapply eval_value; eauto.
  apply value_semvalue in H2.

  destruct (H2 ENV.empty_cxt_inh) as [x ?].
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


(** These should print "Closed under the global context", meaning these
    theorems hold without the use of any axioms.
  *)
Print Assumptions adequacy.
Print Assumptions denote_bottom_nonvalue.
