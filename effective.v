Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.

Require Import NArith.


Record effective_order (A:preord) :=
  EffectiveOrder
  { eff_ord_dec : forall x y:A, {x ≤ y} + {x ≰ y}
  ; eff_enum : eset A
  ; eff_complete : forall x:A, x ∈ eff_enum
  }.

Canonical Structure eff_to_ord_dec A (Heff:effective_order A) : ord_dec A :=
  OrdDec A (eff_ord_dec A Heff).


Program Definition Ndisc_ord : preord :=
  Preord.Pack N (Preord.Mixin N (@eq N) _ _).
Solve Obligations of Ndisc_ord using intros; subst; auto.
Canonical Structure Ndisc_ord.

Program Definition effective_Nord : effective_order Ndisc_ord
  := EffectiveOrder Ndisc_ord _ (fun n => Some n) _.
Next Obligation.
  simpl. unfold Preord.ord_op. simpl.
  apply N_eq_dec.
Qed.
Next Obligation.
  intros. exists x. auto.
Qed.


Definition unenumerate_set (A:preord) (Heff:effective_order A) (x:A) 
  : eset A :=
  fun n => 
    match eff_enum A Heff n with
    | Some x' => 
        if PREORD_EQ_DEC A (eff_to_ord_dec A Heff) x x' 
           then Some x'
           else None
    | None => None
    end.

Lemma unenumerate_set_inhabited A Heff x :
  einhabited (unenumerate_set A Heff x).
Proof.
  apply member_inhabited.
  generalize (eff_complete A Heff x).
  intros [n ?].
  case_eq (eff_enum A Heff n); intros.
  rewrite H0 in H.
  exists c. exists n.
  unfold unenumerate_set. rewrite H0.
  destruct (PREORD_EQ_DEC A (eff_to_ord_dec A Heff) x c); auto.
  rewrite H0 in H. elim H.
Qed.
  
Definition unenumerate (A:preord) (Heff:effective_order A) (x:A) : N :=
  proj1_sig (projT2
    (find_inhabitant A
      (unenumerate_set A Heff x)
      (unenumerate_set_inhabited A Heff x))).
  
Lemma unenumerate_correct A Heff x :
  exists x', eff_enum A Heff (unenumerate A Heff x) = Some x' /\ x ≈ x'.
Proof.
  unfold unenumerate. 
  destruct (find_inhabitant A
               (unenumerate_set A Heff x)
               (unenumerate_set_inhabited A Heff x)); simpl.
  destruct s as [n ?].
  destruct a. simpl.
  case_eq (eff_enum A Heff n); intros.
  unfold unenumerate_set in e.
  rewrite H in e.
  destruct ((PREORD_EQ_DEC A (eff_to_ord_dec A Heff)) x c).
  inversion e. subst x0.
  exists c. split; auto.
  discriminate.
  unfold unenumerate_set in e.
  rewrite H in e. discriminate.
Qed.

Lemma unenumerate_uniq A Heff x x' :
  x ≈ x' ->
  unenumerate A Heff x = unenumerate A Heff x'.
Proof.
  intros.
  unfold unenumerate. 
  destruct (find_inhabitant A
               (unenumerate_set A Heff x)
               (unenumerate_set_inhabited A Heff x)); simpl.
  destruct (find_inhabitant A
               (unenumerate_set A Heff x')
               (unenumerate_set_inhabited A Heff x')); simpl.
  destruct s as [n [??]].
  destruct s0 as [n' [??]].
  simpl.
  unfold unenumerate_set in e.
  case_eq (eff_enum A Heff n); intros.
  rewrite H0 in e.
  destruct (PREORD_EQ_DEC A (eff_to_ord_dec A Heff) x c).
  inversion e; subst x0. clear e.
  unfold unenumerate_set in e0.
  case_eq (eff_enum A Heff n'); intros.
  rewrite H1 in e0.
  destruct (PREORD_EQ_DEC A (eff_to_ord_dec A Heff) x' c0).
  inversion e0; subst x1. clear e0.
  apply N.le_antisymm.
  apply l with c0; auto.
  unfold unenumerate_set.
  rewrite H1.
  destruct (PREORD_EQ_DEC A (eff_to_ord_dec A Heff) x c0). auto.
  elim n0. rewrite H; auto.
  apply l0 with c; auto.
  unfold unenumerate_set.
  rewrite H0.
  destruct (PREORD_EQ_DEC A (eff_to_ord_dec A Heff) x' c). auto.
  elim n0. rewrite <- H; auto.
  discriminate.
  rewrite H1 in e0. discriminate.
  discriminate.
  rewrite H0 in e. discriminate.
Qed.

Lemma unenumerate_reflects A Heff x x' :
  unenumerate A Heff x = unenumerate A Heff x' ->
  x ≈ x'.
Proof.
  intros.
  unfold unenumerate in *.
  destruct (find_inhabitant A
               (unenumerate_set A Heff x)
               (unenumerate_set_inhabited A Heff x)); simpl in *.
  destruct (find_inhabitant A
               (unenumerate_set A Heff x')
               (unenumerate_set_inhabited A Heff x')); simpl in *.
  destruct s as [n [??]].
  destruct s0 as [m [??]].
  simpl in *.
  subst m.
  unfold unenumerate_set in e.
  unfold unenumerate_set in e0.
  case_eq (eff_enum A Heff n); intros.
  rewrite H in e, e0.
  destruct (PREORD_EQ_DEC A (eff_to_ord_dec A Heff) x c).
  inversion e; subst x0.
  destruct (PREORD_EQ_DEC A (eff_to_ord_dec A Heff) x' c).
  inversion e0; subst x1.
  rewrite e1; auto.
  discriminate.
  discriminate.
  rewrite H in e. discriminate.
Qed.

Lemma eff_in_dec : forall {A:preord} (Heff:effective_order A) (M:finset A) (x:A),
  { x ∈ M } + { x ∉ M }.
Proof.
  intros. apply finset_in_dec.
  apply eff_to_ord_dec. auto.
Qed.

Program Definition effective_unit : effective_order unitpo
   := EffectiveOrder unitpo (fun _ _ => left I) (single tt) _.
Next Obligation.
  intro. apply single_axiom. destruct x; auto.
Qed.

Program Definition effective_prod {A B:preord}
  (HA:effective_order A)
  (HB:effective_order B)
  : effective_order (A×B)
  := EffectiveOrder _ _ (eprod (eff_enum A HA) (eff_enum B HB)) _.
Next Obligation.
  intros. destruct x; destruct y.
  destruct (eff_ord_dec A HA c c1).
  destruct (eff_ord_dec B HB c0 c2).
  left. split; auto.
  right. intros [??]; apply n; auto.
  right. intros [??]; apply n; auto.
Qed.
Next Obligation.
  intros.
  destruct x as [a b].
  apply elem_eprod.
  split; apply eff_complete.
Qed.

Definition enum_lift (A:preord) (X:eset A) : eset (lift A) :=
  union2 (single None) (image (liftup A) X).

Program Definition effective_lift {A:preord}
  (HA:effective_order A)
  : effective_order (lift A) :=
  EffectiveOrder _ _ (enum_lift A (eff_enum A HA)) _.
Next Obligation.
  intros.
  destruct x; destruct y; simpl; auto.
  destruct (eff_ord_dec A HA c c0); auto.
  left. hnf. auto.
Qed.
Next Obligation.
  intros. unfold enum_lift.
  apply elem_union2.
  destruct x. right.
  apply image_axiom1'. exists c. split; auto.
  apply eff_complete.
  left. apply single_axiom; auto.
Qed.
