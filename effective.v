Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.

Record effective_order (A:preord) :=
  EffectiveOrder
  { eff_ord_dec : forall x y:A, {x ≤ y} + {x ≰ y}
  ; eff_enum : eset A
  ; eff_complete : forall x:A, x ∈ eff_enum
  }.

Canonical Structure eff_to_ord_dec A (Heff:effective_order A) : ord_dec A :=
  OrdDec A (eff_ord_dec A Heff).

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
