(* Copyright (c) 2014, Robert Dockins *)

Require Import Relations.
Require Import List.
Require Import NArith.

Require Import basics.
Require Import preord.
Require Import categories.
Require Import pairing.
Require Import sets.
Require Import finsets.

(**  * The theory of enumerable sets.

       Here we define the theory of "enumerable" sets.  Concretely,
       enumerable sets of [A] represented by functions [N -> option A].
       We consider an element [x] to be in a set [X] if there exists
       an [n] such that [X n = Some x'] with [x ≈ x'].

       The singleton set is given by the constant function.  The image function
       is defined in the straightforward way as a composition of functions.
       Union is defined by using the isomorphism between [N] and [N×N] defined
       in pairing.
  *)
Module eset.
Section eset.
  Definition eset (A:preord) := N -> option A.
  Definition esingle (A:preord) (a:A) := fun n:N => Some a.
  Definition emember (A:preord) (a:A) (P:eset A) :=
      exists n, match P n with None => False | Some a' => a ≈ a' end.
  Definition eimage (A B:preord) (f:A → B) (P:eset A) (n:N) :=
      match P n with None => None | Some x => Some (f#x) end.
  Definition eunion (A:preord) (PS : eset (set.set_preord eset emember A)) : eset A :=
    fun n => let (p,q) := unpairing n in
       match PS p with
       | None => None
       | Some P => P q
       end.

  Theorem mixin : set.mixin_of eset emember esingle eimage eunion.
  Proof.
    constructor.

    intros.
    destruct H0 as [n ?]. exists n.
    destruct (X n); eauto.

    unfold emember, esingle.
    simpl; firstorder.
    exact N0.

    intros.
    intuition.
    destruct H as [n ?].
    unfold eunion in H.
    case_eq (unpairing n); intros.
    rewrite H0 in H.
    unfold emember.
    case_eq (XS n0); intros.
    rewrite H1 in H.
    case_eq (c n1); intros.
    rewrite H2 in H.
    exists c. split; eauto.
    exists n0. rewrite H1. auto.
    exists n1. rewrite H2. auto.
    rewrite H2 in H. elim H.
    rewrite H1 in H. elim H.
    destruct H as [X [??]].
    destruct H as [n1 ?].
    destruct H0 as [n2 ?].
    case_eq (XS n1); intros.
    rewrite H1 in H.
    case_eq (X n2); intros.
    rewrite H2 in H0.
    destruct H.
    destruct (H c0); eauto.
    hnf; eauto.
    exists n2. rewrite H2. auto.
    case_eq (c x); intros.
    rewrite H5 in H4.
    exists (pairing (n1,x)).
    unfold eunion.
    rewrite unpairing_pairing.
    rewrite H1.
    rewrite H5.
    eauto.
    rewrite H5 in H4. elim H4.
    rewrite H2 in H0. elim H0.
    rewrite H1 in H. elim H.

    intros.
    split; intros [n ?].
    exists n.
    unfold eimage in *.
    destruct (X n); auto.
    exists n.
    unfold eimage in *.
    destruct (X n); auto.

    intros.
    destruct H as [n ?].
    exists n.
    unfold eimage.
    destruct (P n); auto.

    intros.
    destruct H as [n ?].
    unfold eimage in H.
    case_eq (P n); intros.
    rewrite H0 in H.
    exists c. split; auto.
    exists n. rewrite H0. auto.
    rewrite H0 in H. elim H.
  Qed.
End eset.
End eset.

Canonical Structure eset_theory : set.theory :=
  set.Theory
    eset.eset
    eset.emember
    eset.esingle
    eset.eimage
    eset.eunion
    eset.mixin.

Notation eset := (set_preord eset_theory).

Section eset_lemmas.
  Variable A:preord.

  (** The empty set is easily definable.  *)
  Definition empty : eset A := fun n => None.

  (** Every list (qua finite set) generates an enumerable set. *)
  Definition elist (l:list A) : eset A := fun n => nth_error l (N.to_nat n).

  (** Here we define inhabitedness of an enumerable set as an inductive
      predicate with a single constructor.  This enables us to define
      a constructive choice function on inhabited enumerable sets.
    *)
  Inductive einhabited (P:eset A) : Prop :=
    | einh :
        (P N0 = None -> einhabited (fun n => P (Nsucc n))) ->
        einhabited P.

  Lemma member_inhabited : forall (P:eset A), (exists a, a ∈ P) -> einhabited P.
  Proof.
    intros. destruct H as [a [n ?]].
    revert P H.
    induction n using N.peano_ind; intros.
    constructor; intros.
    rewrite H0 in H. elim H.
    constructor; intros.
    apply IHn. auto.
  Defined.

  (**  [find_inhabitant] is defined by recursion on the [einhabited] fact,
       and it finds the smallest index in the set [P] that is defined.
    *)
  Definition find_inhabitant : forall P (H:einhabited P),
    { a:A & { n | P n = Some a /\
      forall n' a', P n' = Some a' -> (n <= n')%N} }.
  Proof.
    fix 2. intros.
    case H.
    generalize (refl_equal (P N0)).
    pattern (P N0) at 2 3.
    case (P N0); intros.
    exists c. exists N0.
    split; auto.
    intros. 
    intros. compute. destruct n'; discriminate.

    case (find_inhabitant _ (H1 (refl_equal _))). intros x Hx.
    case Hx as [n ?].
    exists x. exists (N.succ n). 
    destruct a.
    split; auto.
    intros.
    revert H4.
    pattern n'.
    apply (N.case_analysis).
    hnf. simpl. intuition. subst; auto.
    subst; auto.
    intros. rewrite H4 in H0. discriminate.
    intros.
    apply H3 in H4; auto.
    rewrite <- N.succ_le_mono; auto.
  Defined.

Global Opaque find_inhabitant.


  Definition choose P (H:einhabited P) : A
    := projT1 (find_inhabitant P H).

  Lemma choose_elem : forall P H, (choose P H) ∈ P.
  Proof.
    intros. unfold choose. destruct (find_inhabitant); auto.
    simpl. destruct s as [n ?]. exists n. 
    destruct a. rewrite H0; auto.
  Qed.

  Lemma inhabited_einhabited : forall P, color_prop inhabited P <-> einhabited P.
  Proof.
    intuition.
    apply member_inhabited; auto.
    apply find_inhabitant in H.
    destruct H as [a H]. exists a; auto.
    destruct H as [n ?]. exists n. destruct a0. rewrite H. auto.
  Qed.
End eset_lemmas.
Arguments elist {A} l _.
Arguments einhabited {A} P.

Definition cl_eset_theory CL := cset_theory eset_theory CL.
Notation cl_eset CL := (set_preord (cl_eset_theory CL)).

(**  The intersection of enumerable sets can be defined if we have a decidable equality on the
     elements.
  *)
Definition intersection {A:preord} (eqdec:forall x y:A, {x ≈ y}+{x ≉ y}) (P Q:eset A) : eset A :=
    fun n => let (p,q) := unpairing n in 
       match P p, Q q with
       | Some x, Some y => if eqdec x y then Some x else None
       | _, _ => None
       end.

(**  We also have binary unions *)
Definition union2 {A} (P:eset A) (Q:eset A) : eset A :=
  fun n =>
    match n with
    | N0          => P N0
    | Npos xH     => Q N0
    | Npos (xO p) => P (Npos p)
    | Npos (xI q) => Q (Npos q)
    end.

(** The disjoint union of two enumerable sets. *)
Definition esum {A B} (P:eset A) (Q:eset B) : eset (sum_preord A B) :=
  fun n =>
    match n with
    | N0          => match P N0 with | None => None | Some x => Some (inl _ x) end
    | Npos xH     => match Q N0 with | None => None | Some y => Some (inr _ y) end
    | Npos (xO p) => match P (Npos p) with | None => None | Some x => Some (inl _ x) end
    | Npos (xI q) => match Q (Npos q) with | None => None | Some y => Some (inr _ y) end
    end.

(** The binary product of enumerable sets. *)
Definition eprod {A B} (P:eset A) (Q:eset B) : eset (prod_preord A B) :=
  fun n => let (p,q) := unpairing n in
    match P p, Q q with
    | Some x, Some y => Some (x,y)
    | _, _ => None
    end.

(** Correctness lemmas for the above. *)
Lemma union2_elem : forall A (P Q:eset A) x,
  x ∈ (union2 P Q) <-> (x ∈ P \/ x ∈ Q).
Proof.
  intros. split; intro.
  red in H. simpl in H.
  destruct H as [n ?].
  unfold union2 in H.
  destruct n.
  left. exists N0; auto.
  destruct p.
  right. exists (Npos p); auto.
  left. exists (Npos p); auto.
  right. exists N0; auto.
  destruct H.
  destruct H as [n ?].
  destruct n.
  exists N0. auto.
  exists (Npos (xO p)); auto.
  destruct H as [n ?].
  destruct n.
  exists (Npos xH). auto.
  exists (Npos (xI p)); auto.
Qed.

Lemma esum_left_elem :  forall A B (P:eset A) (Q:eset B) x,
  (inl B x) ∈ (esum P Q) <-> x ∈ P.
Proof.
  intuition.

  destruct H as [n ?].
  destruct n.
  simpl in H.
  case_eq (P N0); intros.
  rewrite H0 in H.
  exists N0.
  rewrite H0. apply H.
  rewrite H0 in H. elim H.
  destruct p. simpl in H.
  case_eq (Q (Npos p)); intros.
  rewrite H0 in H.
  destruct H. elim H.
  rewrite H0 in H. elim H.
  simpl in H.
  case_eq (P (Npos p)); intros.
  rewrite H0 in H.
  exists (N.pos p). rewrite H0. apply H.
  rewrite H0 in H. elim H.
  simpl in H.
  case_eq (Q N0); intros.
  rewrite H0 in H. destruct H. elim H.
  rewrite H0 in H. elim H.

  destruct H as [n ?].
  case_eq (P n); intros.
  rewrite H0 in H.
  destruct n.
  exists N0.
  unfold esum.
  rewrite H0.
  auto.
  exists (Npos (xO p)).
  unfold esum.
  rewrite H0. auto.
  rewrite H0 in H. elim H.
Qed.

Lemma esum_right_elem :  forall (A B:preord) (P:eset A) (Q:eset B) (y:B),
  (inr _ y) ∈ (esum P Q) <-> y ∈ Q.
Proof.
  intuition.

  destruct H as [n ?].
  unfold esum in H.
  destruct n.
  case_eq (P N0); intros.
  rewrite H0 in H.
  destruct H. elim H.
  rewrite H0 in H. elim H.
  destruct p.
  case_eq (Q (N.pos p)); intros.
  rewrite H0 in H. 
  exists (Npos p). rewrite H0. apply H.
  rewrite H0 in H. elim H.
  case_eq (P (Npos p)); intros.
  rewrite H0 in H.
  destruct H. elim H.
  rewrite H0 in H. elim H.
  case_eq (Q N0); intros.
  rewrite H0 in H.
  exists N0.
  rewrite H0.
  auto.
  rewrite H0 in H. elim H.

  destruct H as [n ?].
  case_eq (Q n); intros.
  rewrite H0 in H.
  destruct n.
  exists (Npos xH).
  unfold esum.
  rewrite H0.
  auto.
  exists (Npos (xI p)).
  unfold esum.
  rewrite H0. auto.
  rewrite H0 in H. elim H.
Qed.

Lemma eprod_elem : forall (A B:preord) (P:eset A) (Q:eset B) (x:A) (y:B),
  (x,y) ∈ (eprod P Q) <-> x ∈ P /\ y ∈ Q.
Proof.
  intros. split; intros.

  destruct H as [n ?].
  unfold eprod in H.
  case_eq (unpairing n); intros p q Hn.
  rewrite Hn in H.
  case_eq (P p); intros.
  rewrite H0 in H.
  case_eq (Q q); intros.
  rewrite H1 in H.
  split.
  exists p. rewrite H0. destruct H; auto.
  destruct H; destruct H2; split; auto.
  exists q. rewrite H1. destruct H.
  destruct H; destruct H2; split; auto.
  rewrite H1 in H. elim H.
  rewrite H0 in H. elim H.

  destruct H.
  destruct H as [p ?].
  destruct H0 as [q ?].
  exists (pairing (p,q)).
  case_eq (P p); intros; rewrite H1 in H. 2: elim H.
  case_eq (Q q); intros; rewrite H2 in H0. 2: elim H0.
  unfold eprod.
  rewrite unpairing_pairing.
  rewrite H1. rewrite H2.
  destruct H; destruct H0.
  split; split; simpl; auto.
Qed.

Notation "∅" := (empty _).

Lemma empty_elem : forall (A:preord) (x:A),
  x ∈ ∅ -> False.
Proof.
  intros. destruct H as [n ?].
  hnf in H. auto.
Qed.

Lemma elist_elem : forall (A:preord) (l:finset A) (x:A),
  x ∈ (elist l) <-> x ∈ l.
Proof.
  intuition.
  hnf in H.
  destruct H as [n ?].
  unfold elist in H.
  case_eq (nth_error l (N.to_nat n)); auto; intros.
  rewrite H0 in H.
  exists c. split; auto.
  clear -H0.
  revert H0. generalize (N.to_nat n).
  clear n. intro n. revert l.
  induction n; simpl; intuition.
  destruct l; inversion H0; subst.
  simpl; eauto.
  destruct l; simpl in *.
  inversion H0.
  right. eapply IHn; eauto.
  rewrite H0 in H. elim H.

  destruct H as [x' [??]].
  simpl.
  induction l. inversion H.
  simpl in H. destruct H; subst.
  exists N0. simpl. auto.
  destruct IHl as [n ?]; auto.
  exists (Nsucc n).
  unfold elist.
  rewrite N2Nat.inj_succ. simpl.
  auto.
Qed.


Lemma intersection_elem : forall (A:preord) eqdec (P Q:eset A) (x:A),
  x ∈ (intersection eqdec P Q) <->
  (x ∈ P /\ x ∈ Q).
Proof.
  intros. split; intros.
  destruct H as [z ?].
  unfold intersection in H.
  case_eq (unpairing z); intros p q ?.
  rewrite H0 in H.
  case_eq (P p); intros; rewrite H1 in H.
  case_eq (Q q); intros; rewrite H2 in H.
  destruct (eqdec c c0).
  split.
  exists p. rewrite H1. auto.
  exists q.  rewrite H2.
  eapply eq_trans; eauto.
  elim H. elim H. elim H.

  destruct H as [[p Hp] [q Hq]].
  exists (pairing (p,q)).    
  unfold intersection.
  rewrite unpairing_pairing.
  destruct (P p); intuition.
  destruct (Q q); intuition.
  destruct (eqdec c c0); auto.
  elim f. eapply eq_trans; eauto.
Qed.


(**  The finite subets of an enumerable set are enumerable.
  *)

Fixpoint choose_finset (A:preord) (X:eset A) (n:nat) (z:N) : finset A :=
  match n with
  | 0 => nil
  | S n' => let (p,q) := unpairing z in
              match X p with
              | None => choose_finset A X n' q
              | Some a => a :: choose_finset A X n' q
              end
  end.

Lemma choose_finset_sub : forall A X n z,
  choose_finset A X n z ⊆ X.
Proof.
  induction n; simpl; intros.
  red; simpl; intros.
  destruct H as [?[??]]. elim H.
  case_eq (unpairing z); intros p q ?.
  case_eq (X p); intros.
  red; simpl; intros.
  destruct H1 as [b [??]].
  simpl in H1; intuition subst.
  exists p. rewrite H0. auto.
  apply (IHn q). rewrite H2.
  exists b. split; auto.
  apply IHn.
Qed.

Lemma choose_finset_in : forall A X (Q:finset A),
  Q ⊆ X -> exists n, exists z, choose_finset A X n z ≈ Q.
Proof.
  intros. induction Q. 
  exists 0. exists N0. simpl; auto.
  destruct IHQ as [n [z ?]].
  apply incl_trans with finset_theory (a::Q); auto.
  red; simpl; intros.
  destruct H0 as [b [??]].
  exists b; split; simpl; auto.
  assert (a ∈ X).
  apply H.
  exists a. split; simpl; auto.
  destruct H1 as [p ?].
  exists (S n). exists (pairing (p,z)).
  simpl.
  rewrite unpairing_pairing.
  destruct (X p).
  split; red; simpl; intros.
  destruct H2 as [b [??]].
  simpl in H2; intuition subst.
  exists a. split; simpl; eauto.
  destruct H0.
  destruct (H0 b).
  exists b; split; auto.  
  destruct H5.
  exists x.  
  split; simpl; eauto.
  destruct H2 as [b [??]].
  simpl in H2; intuition subst.
  exists c.
  split; simpl; eauto.
  destruct H0.
  destruct (H2 b); eauto.
  exists b. split; auto.
  destruct H5.
  exists x; split; simpl; eauto.
  elim H1.
Qed.

Definition finsubsets A (X:eset A) : eset (finset A) :=
  fun n => let (p,q) := unpairing n in Some (choose_finset A X (N.to_nat p) q).

Definition ne_finsubsets A (X:eset A) : eset (finset A) :=
  fun n => 
    let (p,q) := unpairing n in
    let l := choose_finset A X (N.to_nat p) q in
    match l with
    | nil => None
    | _ => Some l
    end.

Lemma finsubsets_complete : forall A (X:eset A) (Q:finset A),
  Q ⊆ X <-> Q ∈ finsubsets A X.
Proof.
  intros. split; intros.
  apply choose_finset_in in H.
  destruct H as [n [z ?]].
  exists (pairing (N.of_nat n,z)).
  unfold finsubsets.
  rewrite unpairing_pairing.
  rewrite Nat2N.id.
  auto.
  destruct H as [z ?].
  unfold finsubsets in H.
  case_eq (unpairing z); intros.
  rewrite H0 in H.
  rewrite H.
  apply choose_finset_sub.
Qed.

Lemma ne_finsubsets_complete : forall A (X:eset A) (Q:finset A),
  ((exists x, x ∈ Q) /\ Q ⊆ X) <-> Q ∈ ne_finsubsets A X.
Proof.
  intros. split; intros.
  destruct H.
  apply choose_finset_in in H0.
  destruct H0 as [n [z ?]].
  exists (pairing (N.of_nat n,z)).
  unfold ne_finsubsets.
  rewrite unpairing_pairing.
  rewrite Nat2N.id.
  case_eq (choose_finset A X n z).
  intros.
  rewrite H1 in H0.
  destruct H0.
  destruct H as [x ?].
  destruct (H2 x); auto.
  destruct H3. elim H3.
  intros.
  rewrite <- H1.
  auto.

  destruct H as [z ?].
  unfold ne_finsubsets in H.
  case_eq (unpairing z); intros.
  rewrite H0 in H.
  case_eq (choose_finset A X (N.to_nat n) n0); intros.
  rewrite H1 in H. elim H.
  rewrite H1 in H.
  split.
  exists c.
  rewrite H.
  exists c; split; simpl; auto.
  rewrite H. rewrite <- H1.
  apply choose_finset_sub.
Qed.

Lemma unitpo_dec : ord_dec unitpo.
Proof.
  constructor. intros. left. hnf. auto.
Qed.

(**  A predicate is semidecidable if its truth is equal
     to the inhabitedness of an enumerable set.
  *)
Record semidec {A:preord} (P:A -> Prop) :=
  Semidec
  { decset : A -> eset unitpo
  ; decset_prop_ok : forall x y:A, x ≈ y -> P x -> P y
  ; decset_correct : forall x a, x ∈ (decset a) <-> P a
  }.

(**  Decidable predicates are semidecidable.
  *)
Program Definition dec_semidec (A:preord) (P:A->Prop)
  (HP:forall x y, x ≈ y -> P x -> P y)
  (Hdec : forall a, {P a}+{~P a}) :
  semidec P :=
  Semidec _ _ (fun a => if Hdec a then single tt else ∅) _ _.
Next Obligation.
  intros. eapply HP; eauto.
Qed.
Next Obligation.
  intros.
  destruct (Hdec a).
  intuition. apply single_axiom. destruct x; auto.
  intuition.
  apply empty_elem in H. elim H.
Qed.

Program Definition semidec_true (A:preord) : semidec (fun _:A => True)
  := Semidec _ _ (fun x => single tt) _ _.
Next Obligation.
  intros; auto.
Qed.
Next Obligation.
  intros; split; auto.
  intro. 
  apply single_axiom. 
  destruct x; auto.
Qed.

Program Definition semidec_false (A:preord) : semidec (fun _:A => False)
  := Semidec _ _ (fun x => ∅) _ _.
Next Obligation.
  intros; auto.
Qed.
Next Obligation.
  intuition.
  apply empty_elem in H. auto.
Qed.

Program Definition semidec_disj (A:preord) (P Q:A ->Prop) (HP:semidec P) (HQ:semidec Q)
  : semidec (fun x => P x \/ Q x)
  := Semidec _ _ (fun x => union2 (decset P HP x) (decset Q HQ x)) _ _.
Next Obligation.
  intuition.
  left. eapply (decset_prop_ok P HP); eauto.
  right. eapply (decset_prop_ok Q HQ); eauto.
Qed.
Next Obligation.
  intuition.
  apply union2_elem in H.
  destruct H.
  apply decset_correct in H. auto.
  apply decset_correct in H. auto.
  apply union2_elem.
  left. apply decset_correct. auto.
  apply union2_elem.
  right. apply decset_correct. auto.
Qed.

Program Definition semidec_conj (A:preord) (P Q:A -> Prop) (HP:semidec P) (HQ:semidec Q) 
  : semidec (fun x => P x /\ Q x)
  := Semidec _ _ (fun x => intersection (PREORD_EQ_DEC _ unitpo_dec) 
                             (decset P HP x) (decset Q HQ x)) _ _.
Next Obligation.
  intros. destruct H0; split.
  eapply decset_prop_ok; eauto.
  eapply decset_prop_ok; eauto.
Qed.
Next Obligation.
  intros; split; intros.
  apply intersection_elem in H.
  destruct H; split.
  apply decset_correct in H; auto.
  apply decset_correct in H0; auto.
  destruct H. apply intersection_elem.
  split; apply decset_correct; auto.
Qed.

Lemma semidec_iff (A:preord) (P Q:A -> Prop)  :
  (forall x:A, P x <-> Q x) ->
  semidec P -> semidec Q.
Proof.
  intros.
  destruct X.
  apply Semidec with decset0.
  intros.
  apply H. apply (decset_prop_ok0 x); auto.
  apply H; auto.
  intros. rewrite <- H. apply decset_correct0.
Qed.

Program Definition const {A B:preord} (x:B) : A → B :=
  Preord.Hom A B (fun _ => x) _.
Next Obligation.
  intros; auto.
Qed.


Lemma semidec_in (A:preord) (HA:ord_dec A) (X:eset A) :
  semidec (fun x => x ∈ X).
Proof.
  apply Semidec with (fun x => image (const tt) 
    (intersection (PREORD_EQ_DEC A HA) X (eset.esingle A x))).
  intros. rewrite <- H; auto.
  intros. split; intro.
  apply image_axiom2 in H.
  destruct H as [y [??]].
  apply intersection_elem in H.
  destruct H.
  apply single_axiom in H1. rewrite <- H1. auto.
  apply image_axiom1'.
  exists a. split.
  destruct x; simpl; auto.
  apply intersection_elem.
  split; auto.
  apply single_axiom. auto.
Qed.

Lemma semidec_in_finset (A B:preord) (HA:ord_dec A) (X:finset A) f :
  (forall b b':B, b ≤ b' -> f b ≤ f b') ->
  semidec (fun x:B => f x ∈ X).
Proof.
  intros.
  apply dec_semidec.
  intros. apply member_eq with (f x); auto.
  intro. apply finset_dec. auto.
Qed.

Fixpoint all_finset_setdec
  (A:preord) (DECSET:A -> eset unitpo) (X:finset A) : eset unitpo :=
  match X with
  | nil => single tt
  | x::xs => intersection (PREORD_EQ_DEC _ unitpo_dec)
                (DECSET x) (all_finset_setdec A DECSET xs)
  end.

Program Definition all_finset_semidec {A:preord} (P:A -> Prop) (H:semidec P)
  : semidec (fun X:finset A => forall a:A, a ∈ X -> P a)
  := Semidec _ _ (all_finset_setdec A (decset P H)) _ _.
Next Obligation.
  intros. apply H1. rewrite H0. auto.
Qed.
Next Obligation.
  intros. induction a.
  simpl; intuition.
  destruct H1 as [?[??]]. elim H1.
  apply single_axiom. destruct x; auto.
  split. intros.
  simpl all_finset_setdec in H0.
  apply intersection_elem in H0.
  destruct H0.
  rewrite IHa in H2.
  destruct H1 as [q [??]].
  simpl in H1; destruct H1; subst.
  apply decset_correct in H0.
  apply decset_prop_ok with q; auto.
  apply H2; auto.
  exists q; split; auto.
  intros.
  simpl. apply intersection_elem.
  split.
  apply decset_correct.
  apply H0. exists a. split; simpl; auto.
  apply IHa.
  intros. apply H0.
  destruct H1 as [q[??]]. exists q; split; simpl; auto.
Qed.

Fixpoint ex_finset_setdec
  (A:preord) (DECSET:A -> eset unitpo) (X:finset A) : eset unitpo :=
  match X with
  | nil => empty unitpo
  | x::xs => union2 (DECSET x) (ex_finset_setdec A DECSET xs)
  end.

Program Definition ex_finset_semidec {A:preord} (P:A -> Prop) (H:semidec P)
  : semidec (fun X:finset A => exists a:A, a ∈ X /\ P a)
  := Semidec _ _ (ex_finset_setdec A (decset P H)) _ _.
Next Obligation.
  intros.
  destruct H1 as [a [??]]. exists a; split; auto.
  rewrite <- H0; auto.
Qed.
Next Obligation.
  intros. induction a.
  split; simpl; intros.
  apply empty_elem in H0. elim H0.
  destruct H0 as [a [??]]. destruct H0 as [?[??]]. elim H0.
  split; simpl; intros.
  apply union2_elem in H0.
  destruct H0.
  apply decset_correct in H0.
  exists a. split; auto.
  exists a; split; simpl; auto.
  rewrite IHa in H0.
  destruct H0 as [b [??]].
  exists b. split; auto.
  destruct H0 as [q [??]].
  exists q; split; simpl; auto.
  destruct H0 as [b [??]].
  destruct H0 as [q[??]].
  destruct H0; subst.
  apply union2_elem.
  left. apply decset_correct; auto.
  apply decset_prop_ok with b; auto.
  apply union2_elem.
  right. apply IHa.
  exists b. split; auto.
  exists q. split; auto.
Qed.

Definition eimage' (A B:preord) (f:A -> B) (P:eset A) : eset B :=
  fun n => match P n with None => None | Some x => Some (f x) end.

Program Definition esubset {A:preord} (P:A -> Prop) (H:semidec P) (X:eset A) :=
  eset.eunion A 
    (eimage' _ _ (fun x => eimage' _ _ (fun _ => x) (decset P H x)) X).

Lemma esubset_elem (A:preord) (P:A->Prop) (dec:semidec P) X x :
  x ∈ esubset P dec X <-> (x ∈ X /\ P x).
Proof.
  split; intros.
  unfold esubset in H.
  apply union_axiom in H.
  destruct H as [Q [??]].
  destruct H as [n ?].
  unfold eimage' in H.
  case_eq (X n); intros. rewrite H1 in H.
  destruct H.
  generalize H0.
  intros.
  apply H in H0.
  destruct H0 as [m ?].
  case_eq (decset P dec c m); intros.
  rewrite H4 in H0.
  split.
  exists n. rewrite H1. auto.
  apply decset_prop_ok with c; auto.
  apply (decset_correct _ dec) with c0.
  exists m. rewrite H4. auto.
  rewrite H4 in H0. elim H0.
  rewrite H1 in H. elim H.

  destruct H.
  unfold esubset.
  apply union_axiom.
  exists
   ((fun x0 : A =>
     eimage' unitpo A (fun _ : unitpo => x0) (decset P dec x0)) x).
  split.
  red; simpl. red.
  unfold eimage'. simpl.
  destruct H as [n ?].
  exists n.
  destruct (X n); auto.
  split; simpl; intros; red; simpl; intros.
  destruct H1 as [m ?]. simpl in H1.
  case_eq (decset P dec x m); intros.
  rewrite H2 in H1.
  assert (P x).
  apply (decset_correct _ dec) with c0.
  exists m. rewrite H2. auto.
  assert (P c).
  apply decset_prop_ok with x; auto.
  rewrite <- (decset_correct _ dec tt c) in H4.
  destruct H4 as [p ?].
  exists p. destruct (decset P dec c p); auto.
  rewrite H1; auto.
  rewrite H2 in H1. elim H1.
  destruct H1 as [m ?].
  case_eq (decset P dec c m); intros.
  rewrite H2 in H1.
  assert (P c).
  rewrite <- (decset_correct _ dec c0 c).
  exists m. rewrite H2. auto.
  assert (P x).
  apply decset_prop_ok with c; auto.
  rewrite <- (decset_correct _ dec tt x) in H4.
  destruct H4 as [p ?].
  exists p. destruct (decset P dec x p); auto.
  rewrite H1; auto.
  rewrite H2 in H1. elim H1.

  rewrite <- (decset_correct _ dec tt x) in H0.
  destruct H0 as [n ?].
  case_eq (decset P dec x n); intros.
  rewrite H1 in H0.
  exists n.
  unfold eimage'.
  rewrite H1. auto.
  rewrite H1 in H0. elim H0.
Qed.

Definition esubset_dec (A:preord) (P:A -> Prop) (dec:forall x:A, {P x}+{~P x})
  (X:eset A) : eset A :=
  fun n => match X n with
           | None => None
           | Some a => 
               match dec a with
               | left H => Some a
               | right _ => None
               end
           end.

Lemma esubset_dec_elem : forall (A:preord) (P:A->Prop) dec X x,
  (forall x y, x ≈ y -> P x -> P y) ->
  (x ∈ esubset_dec A P dec X <-> (x ∈ X /\ P x)).
Proof.  
  intros. split; intros.
  red in H0. simpl in H0.
  destruct H0 as [n ?].
  unfold esubset_dec in H0.
  case_eq (X n); intros.
  rewrite H1 in H0.
  destruct (dec c).
  split; auto.
  exists n. rewrite H1. auto.
  apply H with c; auto.
  elim H0.
  rewrite H1 in H0. elim H0.
  destruct H0.
  destruct H0 as [n ?].
  exists n.
  unfold esubset_dec.
  destruct (X n); auto.
  destruct (dec c); auto.
  apply n0. apply H with x; auto.
Qed.

Definition erel (A B:preord) := eset (A × B).

Definition erel_image (A B:preord) (dec : ord_dec A) (R:erel A B) (x:A) : eset B :=
  image π₂ (esubset_dec
                    (A×B)
                    (fun p => π₁#p ≈ x)
                    (fun p => PREORD_EQ_DEC A dec (π₁#p) x) R).

Lemma erel_image_elem : forall A B dec R x y,
  y ∈ erel_image A B dec R x <-> (x,y) ∈ R.
Proof.  
  intros. split; intros.
  unfold erel_image in H.
  apply image_axiom2 in H.
  destruct H as [p [??]].
  apply esubset_dec_elem in H.
  destruct H.
  assert (p ≈ (x,y)).
  destruct p; simpl in *.
  destruct H1.
  destruct H0.
  split; split; auto.
  rewrite <- H2. auto.
  intros.
  rewrite <- H1. auto.
  unfold erel_image.
  change y with (π₂# ((x,y) : A×B)).
  apply image_axiom1.
  apply esubset_dec_elem.
  intros. rewrite <- H0; auto.
  split; auto.
Qed.

Definition erel_inv_image 
  (A B:preord) (dec : ord_dec B) (R:erel A B) (y:B) : eset A :=
  image π₁ (esubset_dec (A×B)
                    (fun p => π₂#p ≈ y)
                    (fun p => PREORD_EQ_DEC B dec (π₂#p) y) R).

Lemma erel_inv_image_elem : forall A B dec R x y,
  x ∈ erel_inv_image A B dec R y <-> (x,y) ∈ R.
Proof.  
  intros. split; intros.
  unfold erel_inv_image in H.
  apply image_axiom2 in H.
  destruct H as [p [??]].
  apply esubset_dec_elem in H.
  destruct H.
  assert (p ≈ (x,y)).
  destruct p; simpl in *.
  destruct H1; destruct H0.
  split; split; auto.
  rewrite <- H2; auto.
  intros. rewrite <- H1; auto.
  unfold erel_inv_image.
  change x with (π₁# ((x,y) : A × B)).
  apply image_axiom1.
  apply esubset_dec_elem.
  intros. rewrite <- H0; auto.
  split; auto.
Qed.
