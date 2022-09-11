(* Copyright (c) 2014, Robert Dockins *)

Require Import Ascii.
Require Export String.
Open Scope string_scope.

Require Import Setoid.
Require Import NArith.
Require Import Arith.
Require Import List.
Require Import Lia.

Require Import basics.
Require Import categories.
Require Import preord.
Require Import sets.
Require Import finsets.
Require Import esets.

(**  * Atoms for nominal types

     Atoms are concretely represented by ASCII strings.
     Here we provide some operations on atoms, including an
     operation for choosing fresh atoms.
  *)

(**  ASCII characters are ordered by inheriting their numerical order.
  *)
Definition char_ord (x y:ascii) := N.le (N_of_ascii x) (N_of_ascii y).

(**  Strings are ordered lexicographically.
  *)
Fixpoint string_ord (x y:string) :=
  match x, y with
  | "", _ => True
  | String a x', "" => False
  | String a x', String b y' =>
       (a <> b /\ char_ord a b) \/
       (a = b /\ string_ord x' y')
  end.

Obligation Tactic := idtac.

Program Definition string_ord_mixin : Preord.mixin_of string :=
  Preord.Mixin string string_ord _ _.
Next Obligation.
  induction x; simpl; auto.
Qed.
Next Obligation.
  induction x; simpl; auto.
  induction y; simpl; intuition.
  destruct z; auto.
  intuition subst.
  left. 
  unfold char_ord in *.
  split; auto.
  intro. subst a.
  apply H.
  rewrite <- (ascii_N_embedding a1).
  rewrite <- (ascii_N_embedding a0).
  f_equal.
  apply N.le_antisymm; auto.
  eapply N.le_trans; eauto.
  auto.
  destruct z. elim H0.
  subst a0.
  intuition subst; auto.
  right; split; eauto.
Qed.

(**  [atom] is the preorder of strings with their
     lexicographic order.  We use these for object-level
     variables.
  *)
Canonical Structure atom : Preord.type :=
  Preord.Pack string string_ord_mixin.

(**   The order on [atom] is decidable.
  *)
Program Definition atom_dec : ord_dec atom := OrdDec _ _.
Next Obligation.
  induction x; simpl; intros.
  left. exact I.
  destruct y.
  right. intro. apply H.
  case_eq (N_of_ascii a ?= N_of_ascii a0)%N.
  intros.
  destruct (IHx y).
  left. red. simpl.
  right. split; auto.
  rewrite <- (ascii_N_embedding a).
  rewrite <- (ascii_N_embedding a0).
  replace (N_of_ascii a) with (N_of_ascii a0); auto.
  symmetry.
  apply N.compare_eq. auto.
  right.
  intro. red in H0. simpl in H0.
  intuition.
  apply H0.
  rewrite <- (ascii_N_embedding a).
  rewrite <- (ascii_N_embedding a0).
  replace (N_of_ascii a) with (N_of_ascii a0); auto.
  symmetry.
  apply N.compare_eq. auto.
  intro.
  left. red; simpl.
  left.
  split. intro.
  subst a0.
  generalize (N.compare_ge_iff (N_of_ascii a) (N_of_ascii a)).
  intros. destruct H0. apply H1. apply N.le_refl. auto.
  red. red. rewrite H. discriminate.
  intro. right. intro.
  red in H0. simpl in H0.
  destruct H0.
  destruct H0. hnf in H1.
  apply H1; auto.
  destruct H0. subst a0.
  generalize (N.compare_le_iff (N_of_ascii a) (N_of_ascii a)).
  rewrite H. intros.
  destruct H0. apply H2; auto.
  apply N.le_refl.
Defined.

(**  [atom] is actually a partial order with respect to [=].
  *)
Lemma atom_strong_eq : forall (x y:atom), x ≈ y -> x = y.
Proof.
  induction x.
  induction y; simpl; intros; auto.
  destruct H. elim H0.
  induction y; simpl; intros; auto.
  destruct H. elim H.
  destruct H.  
  destruct H. destruct H0.
  destruct H; destruct H0.
  elim H.
  rewrite <- (ascii_N_embedding a).
  rewrite <- (ascii_N_embedding a0).
  f_equal.
  apply N.le_antisymm; auto.
  destruct H; destruct H0.
  elim H; auto.
  destruct H0.
  destruct H; destruct H0.
  elim H0; auto.
  destruct H; destruct H0.
  subst a0.
  f_equal. apply IHx.
  split; auto.
Qed.


Section unfold.
  Variables X A:Type.
  Variable step : X -> X * A.
  
  Definition unfold_stream (seed:X) (n:N) : A :=
       N.peano_rect (fun _ => X -> A)
                    (fun x => snd (step x))
                    (fun _ r x => r (fst (step x)))
                    n seed.

  Variable invariant : X -> Prop.
  Variable wf_rel : X -> X -> Prop.
  Variable out_prop : A -> Prop.

  Hypothesis wf : well_founded wf_rel.

  Hypothesis ind_step : forall x,
    invariant x -> let (x',a) := step x in
      (invariant x' /\ wf_rel x' x) \/ out_prop a.
      
  Lemma unfold_find : forall x,
    invariant x ->
    exists n a, unfold_stream x n = a /\ out_prop a.
  Proof.
    induction x using (well_founded_induction wf); intros.
    generalize (ind_step x H0).
    case_eq (step x); intros x' a ?.
    intros [[??]|?].
    destruct (H x') as [n [a' [??]]]; auto.
    exists (N.succ n). exists a'.
    split; auto.
    unfold unfold_stream; rewrite N.peano_rect_succ.
    rewrite H1. simpl. auto.
    exists N.zero. exists a.
    compute.
    rewrite H1; split; simpl; auto.   
  Defined.

End unfold.

(**  When choosing fresh atoms, these are the only characters
     that will be used.
  *)
Definition allowable_chars := "abcdefghijklmnopqrstuvwxyz".


Fixpoint adjoin_char (s:string) (ls:list string) :=
  match s with
  | "" => nil
  | String a s' => map (fun q => String a q) ls ++ 
                   adjoin_char s' ls
  end.

Fixpoint perms (n:nat) (s:string) : list string :=
  match n with
  | 0 => ""::nil
  | S n' => adjoin_char s (perms n' s)
  end.

Lemma perms_len : forall n s s',
  In s' (perms n s) -> String.length s' = n.
Proof.
  induction n; simpl; intuition subst; auto.
  revert H. generalize s at 1.
  induction s0; simpl; intros. elim H.
  apply in_app_or in H. destruct H.
  generalize (IHn s). revert H.
  generalize (perms n s).
  induction l; simpl; intuition.
  subst s'. simpl. f_equal.
  apply H0; auto.
  apply IHs0; auto.
Qed.

Lemma perms_neq_nil : forall n a s,
  perms n (String a s) = nil -> False.
Proof.
  induction n; simpl; intros.
  discriminate.
  apply (IHn a s).
  destruct (perms n (String a s)); auto.
  simpl in H. discriminate.
Qed.

Definition idents_step (x:nat * list string) :
  (nat * list string * option string) :=
  match x with
  | (n, s::l) => (n, l, Some s)
  | (n, nil)  => (S n, perms (S n) allowable_chars, None)
  end.

(**  The set of all "choosable" atoms.  We enumerate
     this set using an unfold.
  *)
Definition idents_set : eset atom :=
  unfold_stream (nat*list string) (option string) idents_step (0, nil).

(**  The [idents_set] contains at least on string of a given
     (nonzero) length.  This will be used to show that we can
     always choose a fresh atom distinct from any finite set of atoms.
  *)
Section idents_length.
  Variable len:nat.
  Hypothesis len0 : 0 < len. 

  Definition idents_inv (x:nat * list string) :=
    fst x < len \/ 
    (fst x = len /\ 
      snd x <> nil /\
      forall s, In s (snd x) -> String.length s = len).

  Definition idents_wf (x' x:nat * list string) :=
    (fst x < fst x' <= len) \/ 
    (fst x = fst x' /\ length (snd x') < length (snd x)).

  Definition idents_out (a:option string) :=
    match a with
    | None => False
    | Some s => String.length s = len
    end.

  Lemma wf_idents_wf : well_founded idents_wf.
  Proof.
    red. intros [x l].
    destruct (le_gt_dec x len) as [H|H].
    set (z := len - x).
    assert (x = len - z).
    subst z. 
    lia.
    clearbody z. revert x l H H0.
    induction z using (well_founded_induction lt_wf).
    intro x. 
    induction l using 
      (well_founded_induction (well_founded_ltof _ (@List.length string))); intros.
    constructor; intros.
    destruct y; simpl in *.
    destruct H3; simpl in *.
    apply H with (len - n); lia.
    destruct H3. subst n.
    apply H0; auto.
    induction l using 
      (well_founded_induction (well_founded_ltof _ (@List.length string))); intros.
    constructor; intros.
    destruct H1. simpl in *.
    elimtype False. lia.
    simpl in *. destruct H1.
    destruct y; simpl in *.  
    subst n. apply H0.
    auto.
  Defined.

Opaque perms.
  Lemma idents_find_len_aux :
    exists n, exists a,
      idents_set n = a /\ idents_out a.
  Proof.
    apply unfold_find with idents_inv idents_wf.
    apply wf_idents_wf.
    unfold idents_inv. unfold idents_step.
    intros [n l]. simpl.
    intros. destruct H.
    destruct l; simpl.
    left.
    split.
    destruct (eq_nat_dec (S n) len).
    right. split; auto.
    split.
    red. apply perms_neq_nil.
    rewrite e.
    apply perms_len.
    left. lia.
    red. simpl.
    left. lia.
    left. split; auto.
    red. simpl.
    right. split; auto.
    destruct H as [?[??]]. subst n.
    destruct l. elim H0. auto.
    simpl. right.
    apply H1. simpl; auto.
    hnf. simpl.
    auto.
  Defined.

  Lemma idents_find : exists s,
    s ∈ idents_set /\
    String.length s = len.
  Proof.
    destruct idents_find_len_aux as [n [a [??]]].
    hnf in H0. destruct a. 2: elim H0.
    exists c. split; auto.
    exists n. rewrite H. auto.
  Defined.

End idents_length.

Definition max_len
  := fold_right (fun x y => max (String.length x) y) 0.

Lemma max_len_le (xs:finset atom) (x:atom) :
  x ∈ xs ->
  String.length x <= max_len xs.
Proof.
  induction xs; simpl; intros.
  apply nil_elem in H. elim H.
  apply cons_elem in H. destruct H.
  apply atom_strong_eq in H. subst x.
  apply Max.le_max_l.
  apply le_trans with (max_len xs); auto.
  apply Max.le_max_r.
Qed.  

Section fresh.
  Variable atoms : finset atom.

  Program Definition fresh_idents :=
    esubset_dec atom (fun x => ~In x atoms) _ idents_set.
  Next Obligation.
    intro.
    destruct (In_dec string_dec x atoms); auto.
  Defined.

  Lemma fresh_idents_inhabited : einhabited fresh_idents.
  Proof.    
    apply member_inhabited.
    destruct (idents_find (S (max_len atoms))) as [s [??]].
    red. auto with arith.
    exists s. unfold fresh_idents.
    destruct H as [n ?].
    exists n. simpl.
    unfold esubset_dec.
    destruct (idents_set n).
    2: elim H.
    unfold fresh_idents_obligation_1.
    destruct (in_dec string_dec c atoms).
    assert (String.length s <= max_len atoms).
    apply max_len_le. exists c. split; auto.
    rewrite H0 in H1.
    lia.
    auto.
  Defined.

  Definition fresh_atom := choose atom fresh_idents fresh_idents_inhabited.

  Lemma fresh_atom_is_fresh : fresh_atom ∉ atoms.
  Proof.
    red; intro.
    unfold fresh_atom in H.
    unfold choose in H.
    destruct (find_inhabitant atom fresh_idents fresh_idents_inhabited)
      as [a [b [??]]].
    simpl in *.
    unfold fresh_idents in e.
    unfold esubset_dec in e.
    destruct (idents_set b). 2: discriminate.
    destruct (fresh_idents_obligation_1 c).
    apply n.
    inversion e. subst a.
    destruct H as [q [??]].
    apply atom_strong_eq in H0. subst q. auto.
    discriminate.
  Qed.
End fresh.

Lemma fresh_atom_is_fresh' (l1 l2:finset atom) :
  l1 ⊆ l2 ->
  fresh_atom l2 ∉ l1.
Proof.
  repeat intro.
  apply H in H0.
  apply (fresh_atom_is_fresh l2); auto.
Qed.

