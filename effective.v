Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.

Require Import NArith.

(**  * Effective preorders.

       We define the notion of "effective" preorders: those
       for which the order relation is decidable and the
       members of the preorder are enumerable.
  *)

Record effective_order (A:preord) :=
  EffectiveOrder
  { eff_ord_dec : forall x y:A, {x ≤ y} + {x ≰ y}
  ; eff_enum : eset A
  ; eff_complete : forall x:A, x ∈ eff_enum
  }.


(**  Effective orders have a decidable equality.
  *)
Canonical Structure eff_to_ord_dec A (Heff:effective_order A) : ord_dec A :=
  OrdDec A (eff_ord_dec A Heff).


(**  The positive integers form an effective preorder.
  *)
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


(**  Given an effective preorder, we can calculate a canonical
     index value for any given element of the preorder.

     We do this by first generating the subset of the enumeration set
     containing all elements equal to [x]; then we choose the smallest
     index from that set that is defined.  Such an element exists
     because we know the set is inhabited.  The principle of countable
     choice then suffices to choose the index.
  *)

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

(**  The unenumeration index is unique (up to Leibniz equality)
     and equal indexes imply equal elements.
  *)
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

(** The one-point preorder is effective. *)
Program Definition effective_unit : effective_order unitpo
   := EffectiveOrder unitpo (fun _ _ => left I) (single tt) _.
Next Obligation.
  intro. apply single_axiom. destruct x; auto.
Qed.

(** The binary product of effective preorders is effective. *)
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
  apply eprod_elem.
  split; apply eff_complete.
Qed.

(** The binary sum of effective preorders is effective. *)
Program Definition effective_sum {A B:preord}
  (HA:effective_order A)
  (HB:effective_order B)
  : effective_order (sum_preord A B)
  := EffectiveOrder _ _ (esum (eff_enum A HA) (eff_enum B HB)) _.
Next Obligation.
  intros.
  destruct x; destruct y.
  destruct (eff_ord_dec A HA c c0).
  left. auto.
  right. auto.
  right. intro. elim H.
  right. intro. elim H.
  destruct (eff_ord_dec B HB c c0).
  left. auto.
  right. auto.
Qed.
Next Obligation.
  intros.
  destruct x.
  apply esum_left_elem. apply eff_complete.
  apply esum_right_elem. apply eff_complete.
Qed.


(** The lift of an effective preorder is effective. *)
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
  apply union2_elem.
  destruct x. right.
  apply image_axiom1'. exists c. split; auto.
  apply eff_complete.
  left. apply single_axiom; auto.
Qed.


(** FIXME? this doesn't really fit here, but the current
    module tree means it can't go in esets.v.  Maybe semidec
    should get split out into a separate file?
  *)
Lemma semidec_ex (A B:preord) P
  (HB:effective_order B) :
  @semidec (A×B) (fun ab => P (fst ab) (snd ab)) ->
  @semidec A (fun a => @ex B (P a)).
Proof.
  intros.
  destruct X.
  apply Semidec with (fun a n =>
    let (p,q) := pairing.unpairing n in
       match eff_enum B HB p with
       | None => None
       | Some b => decset (a,b) q
       end).
  intros.
  destruct H0. exists x0.
  apply (decset_prop_ok (x,x0) (y,x0)); auto.
  split; split; auto.
  simpl; intros. split; intros.
  destruct H as [n ?].
  case_eq (pairing.unpairing n); intros.
  rewrite H0 in H.
  destruct (eff_enum B HB n0); intros.
  case_eq (decset (a,c) n1); intros.
  rewrite H1 in H.
  assert (c0 ∈ decset (a,c)).
  exists n1. rewrite H1; auto.
  apply decset_correct in H2.
  simpl in H2. eauto.
  rewrite H1 in H. elim H. elim H.
  destruct H as [b ?].
  generalize (eff_complete B HB b).
  intros [p ?].
  case_eq (eff_enum B HB p); intros.
  rewrite H1 in H0.
  assert (P a c).
  apply (decset_prop_ok (a,b) (a,c)); auto.
  split; split; auto.
  assert (tt ∈ decset (a,c)).
  apply decset_correct. simpl; auto.
  destruct H3 as [q ?].
  exists (pairing.pairing (p,q)).
  rewrite pairing.unpairing_pairing.
  destruct (eff_enum B HB p); auto.
  inversion H1; subst.
  destruct (decset (a,c) q); intros; auto.
  discriminate.
  rewrite H1 in H0. elim H0.
Qed.
