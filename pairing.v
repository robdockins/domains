(* Copyright (c) 2014, Robert Dockins *)

Require Import NArith.

Local Open Scope N_scope.

(**  * Bitwise pairing function on [N].

       Here we define a "bitwise" pairing isomorphism
       on the nonnegative integers.  This is one of
       many different ways to witness the isormporphism
       between [N] and [N×N].

       We will use the pairing function to define the union
       of countable sets and other similar constructions.
       The details of the isomorphism are unimportant
       once the isomorphism is defined.  We prove this particular
       isomorphism because it requires almost no facts about
       arithmetic, and the proofs go by simple inductions on the
       binary representation of positives.
  *)

Fixpoint inflate (x:positive) : positive :=
  match x with
  | xH    => xO xH
  | xO x' => xO (xO (inflate x'))
  | xI x' => xO (xI (inflate x'))
  end.

Fixpoint inflate' (x:positive) : positive :=
  match x with
  | xH    => xH
  | xO x' => xO (xO (inflate' x'))
  | xI x' => xI (xO (inflate' x'))
  end.

Fixpoint deflate (x:positive) : N :=
  match x with
  | xH    => N0
  | xO xH => Npos xH
  | xI xH => Npos xH
  | xO (xO x') => match deflate x' with N0 => N0 | Npos q => Npos (xO q) end
  | xI (xO x') => match deflate x' with N0 => N0 | Npos q => Npos (xO q) end
  | xO (xI x') => match deflate x' with N0 => Npos xH | Npos q => Npos (xI q) end
  | xI (xI x') => match deflate x' with N0 => Npos xH | Npos q => Npos (xI q) end
  end.

Fixpoint deflate' (x:positive) : N :=
  match x with
  | xH    => Npos xH
  | xO xH => N0
  | xI xH => Npos xH
  | xO (xO x') => match deflate' x' with N0 => N0 | Npos q => Npos (xO q) end
  | xI (xO x') => match deflate' x' with N0 => Npos xH | Npos q => Npos (xI q) end
  | xO (xI x') => match deflate' x' with N0 => N0 | Npos q => Npos (xO q) end
  | xI (xI x') => match deflate' x' with N0 => Npos xH | Npos q => Npos (xI q) end
  end.

Lemma deflate_inflate0 : forall x,
  deflate (inflate x) = Npos x.
Proof.
  induction x; simpl; intros; auto.
  rewrite IHx; auto.
  rewrite IHx; auto.
Qed.

Lemma deflate_inflate0' : forall y,
  deflate' (inflate' y) = Npos y.
Proof.
  induction y; simpl; intros; auto.
  rewrite IHy; auto.
  rewrite IHy; auto.
Qed.

Lemma deflate_inflate1 : forall y,
  deflate (inflate' y) = 0.
Proof.
  induction y; simpl; auto.
  rewrite IHy; auto.
  rewrite IHy; auto.
Qed.

Lemma deflate_inflate1' : forall x,
  deflate' (inflate x) = 0.
Proof.
  induction x; simpl; auto.
  rewrite IHx; auto.
  rewrite IHx; auto.
Qed.

Lemma deflate_inflate : forall x y,
  deflate (inflate x + inflate' y) = Npos x.
Proof.
  induction x; simpl; intros.
  destruct y; simpl; f_equal; auto.
  rewrite IHx. auto.
  rewrite IHx. auto.
  rewrite deflate_inflate0. auto.
  destruct y; simpl; f_equal; auto.
  rewrite IHx. auto.
  rewrite IHx. auto.
  rewrite deflate_inflate0. auto.
  destruct y; simpl; f_equal; auto.
  rewrite deflate_inflate1. auto.
  rewrite deflate_inflate1. auto.
Qed.  

Lemma deflate_inflate' : forall y x,
  deflate' (inflate x + inflate' y) = Npos y.
Proof.
  induction y; simpl; intros; auto.
  destruct x; simpl.
  rewrite IHy. auto.
  rewrite IHy. auto.
  rewrite deflate_inflate0'. auto.
  destruct x; simpl.
  rewrite IHy. auto.
  rewrite IHy. auto.
  rewrite deflate_inflate0'. auto.
  destruct x; simpl.
  rewrite deflate_inflate1'. auto.
  rewrite deflate_inflate1'. auto.
  auto.
Qed.

Lemma deflate00 : forall p, deflate (p~0~0) = 2*(deflate p).
Proof.
  intros. simpl.
  case_eq (deflate p); auto.
Qed.

Lemma deflate01 : forall p, deflate (p~0~1) = 2*(deflate p).
Proof.
  intros. simpl.
  case_eq (deflate p); auto.
Qed.

Lemma deflate10 : forall p, deflate (p~1~0) = 2*(deflate p) + 1 .
Proof.
  intros. simpl.
  case_eq (deflate p); auto.
Qed.

Lemma deflate11 : forall p, deflate (p~1~1) = 2*(deflate p) + 1 .
Proof.
  intros. simpl.
  case_eq (deflate p); auto.
Qed.

Lemma deflate00' : forall p, deflate' (p~0~0) = 2*(deflate' p).
Proof.
  intros. simpl.
  case_eq (deflate' p); auto.
Qed.

Lemma deflate01' : forall p, deflate' (p~0~1) = 2*(deflate' p)+1.
Proof.
  intros. simpl.
  case_eq (deflate' p); auto.
Qed.

Lemma deflate10' : forall p, deflate' (p~1~0) = 2*(deflate' p).
Proof.
  intros. simpl.
  case_eq (deflate' p); auto.
Qed.

Lemma deflate11' : forall p, deflate' (p~1~1) = 2*(deflate' p) + 1 .
Proof.
  intros. simpl.
  case_eq (deflate' p); auto.
Qed.


Definition pairing (p:N*N) : N :=
  match p with
  | (N0, N0) => N0
  | (N0, Npos y) => Npos (inflate' y)
  | (Npos x, N0) => Npos (inflate x)
  | (Npos x, Npos y) => Npos (inflate x + inflate' y)
  end.

Definition unpairing (z:N) : N*N :=
  match z with
  | N0 => (N0,N0)
  | Npos z => (deflate z, deflate' z)
  end.

Lemma pairing00 : forall p q,
  pairing (2*p, 2*q) = 4*pairing (p,q).
Proof.
  simpl; intros.
  destruct p; destruct q; simpl; auto.
Qed.

Lemma pairing10 : forall p q,
  pairing (2*p + 1, 2*q) = 4*pairing (p,q)+2.
Proof.
  simpl; intros.
  destruct p; destruct q; simpl; auto.
Qed.

Lemma pairing01 : forall p q,
  pairing (2*p, 2*q + 1) = 4*pairing (p,q)+1.
Proof.
  simpl; intros.
  destruct p; destruct q; simpl; auto.
Qed.

Lemma pairing11 : forall p q,
  pairing (2*p + 1, 2*q + 1) = 4*pairing (p,q)+3.
Proof.
  simpl; intros.
  destruct p; destruct q; simpl; auto.
Qed.

Lemma unpairing_pairing : forall p, unpairing (pairing p) = p.
Proof.
  intros [x y].
  destruct x; destruct y; simpl; auto.
  rewrite deflate_inflate1. rewrite deflate_inflate0'. auto.
  rewrite deflate_inflate1'. rewrite deflate_inflate0. auto.
  rewrite deflate_inflate.
  rewrite deflate_inflate'.
  auto.
Qed.

Lemma pairing_unpairing : forall z, pairing (unpairing z) = z.
Proof.
  intro z. destruct z. simpl; auto.
  unfold unpairing.
  revert p. fix 1. intro p.
  destruct p. destruct p.
  rewrite deflate11. rewrite deflate11'.
  rewrite pairing11. rewrite pairing_unpairing.
  auto.

  rewrite deflate01. rewrite deflate01'.
  rewrite pairing01. rewrite pairing_unpairing.
  auto.
  simpl. auto.

  destruct p.
  rewrite deflate10. rewrite deflate10'.
  rewrite pairing10. rewrite pairing_unpairing.
  auto.
  rewrite deflate00. rewrite deflate00'.
  rewrite pairing00. rewrite pairing_unpairing.
  auto.
  simpl. auto.
  simpl. auto.
Qed.

Global Opaque unpairing pairing.
