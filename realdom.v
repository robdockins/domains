Require Import QArith.
Require Import Setoid.

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
Require Import profinite.
Require Import cusl.

Record rational_interval
  := RatInt
  { rint_start : Q
  ; rint_end   : Q
  ; rint_proper : rint_start <= rint_end
  }.


Definition ininterval (q:Q) (ri:rational_interval) :=
  rint_start ri <= q <= rint_end ri.

Definition rint_ord (i1 i2:rational_interval) :=
  forall q, ininterval q i2 -> ininterval q i1.


Lemma rint_ord_test (i1 i2:rational_interval) :
  rint_ord i1 i2 <->
  (rint_start i1 <= rint_start i2 /\
   rint_end i2 <= rint_end i1).
Proof.
  split; intros.
  split.
  destruct (H (rint_start i2)).
  hnf.
  split; auto.
  apply Qle_refl.
  apply rint_proper.
  auto.
  destruct (H (rint_end i2)).
  hnf.
  split; auto.
  apply rint_proper.
  apply Qle_refl.
  auto.
  hnf; intros.
  destruct H.
  destruct H0.
  split.
  apply Qle_trans with (rint_start i2); auto.
  apply Qle_trans with (rint_end i2); auto.
Qed.

Program Definition rint_preord_mixin :
  Preord.mixin_of rational_interval :=
  Preord.Mixin rational_interval rint_ord _ _.
Next Obligation.
  repeat intro; auto.
Qed.
Next Obligation.
  repeat intro; eauto.
Qed.

Canonical Structure rint_preord :=
  Preord.Pack rational_interval rint_preord_mixin.

Definition rint_dec : forall x y:rational_interval,
  { x ≤ y }+{x ≰ y }.
Proof.
  intros.
  destruct (Qlt_le_dec (rint_start y) (rint_start x)).
  right; intro.
  apply rint_ord_test in H.
  destruct H.
  assert (rint_start y < rint_start y).
  eapply Qlt_le_trans. apply q. auto.
  red in H1. omega.
  destruct (Qlt_le_dec (rint_end x) (rint_end y)).
  right; intro.  
  apply rint_ord_test in H.
  destruct H.
  assert (rint_end x < rint_end x).
  eapply Qlt_le_trans. apply q0. auto.
  red in H1. omega.
  left. apply rint_ord_test.
  split; auto.
Qed.


Definition Z_enum (n:N) :=
  match n with
  | N0 => Some Z0
  | Npos xH => None
  | Npos (xO p) => Some (Zpos p)
  | Npos (xI p) => Some (Zneg p)
  end.

Definition pos_enum (n:N) :=
  match n with
  | N0 => None
  | Npos p => Some p
   end.

Definition Q_enum (n:N) :=
  let (p,q) := pairing.unpairing n in
    match Z_enum p, pos_enum q with
    | Some n1, Some n2 => Some (n1#n2)%Q
    | _, _ => None
    end.
     
Definition rint_enum (n:N) :=
  let (p,q) := pairing.unpairing n in
    match Q_enum p, Q_enum q with
    | Some n1, Some n2 =>
      match Qlt_le_dec n2 n1 with
      | left _  => None
      | right H => Some (RatInt n1 n2 H)
      end
    | _, _ => None
    end.


Lemma Z_enum_complete : 
  forall z:Z, exists n:N,
    Z_enum n = Some z.
Proof.  
  intros. destruct z.
  exists N0. simpl; auto.
  exists (Npos (xO p)). simpl. auto.
  exists (Npos (xI p)). simpl. auto.
Qed.

Lemma pos_enum_complete : 
  forall p:positive, exists n:N,
    pos_enum n = Some p.
Proof.  
  intros.
  exists (Npos p). simpl. auto.
Qed.

Lemma Q_enum_complete :
  forall q:Q, exists n:N,
    Q_enum n = Some q.
Proof.
  intros.  
  destruct q.
  destruct (Z_enum_complete Qnum) as [p ?].
  destruct (pos_enum_complete Qden) as [q ?].
  exists (pairing.pairing (p,q)).
  unfold Q_enum.
  rewrite pairing.unpairing_pairing.
  rewrite H. rewrite H0. auto.
Qed.

Lemma rint_enum_complete :
  forall i:rint_preord, exists n:N,
    exists i', rint_enum n = Some i' /\ i ≈ i'.
Proof.
  intros. 
  destruct (Q_enum_complete (rint_start i)).
  destruct (Q_enum_complete (rint_end i)).
  exists (pairing.pairing (x,x0)).
  unfold rint_enum.
  case_eq (Qlt_le_dec (rint_end i) (rint_start i)).
  intros.
  elimtype False.
  generalize (rint_proper i). intros.
  assert (rint_end i < rint_end i).
  eapply Qlt_le_trans. apply q. auto.
  red in H3. simpl in H3. omega.
  intros.
  exists (RatInt (rint_start i) (rint_end i) q).
  rewrite pairing.unpairing_pairing.
  rewrite H. rewrite H0.
  rewrite H1. split; auto.
  destruct i as [m n R]. simpl in *.
  red. simpl. split; hnf; simpl;
    unfold ininterval; simpl; intros; auto.
Qed.


Program Definition rint_eff : effective_order rint_preord :=
  EffectiveOrder rint_preord rint_dec rint_enum _.
Next Obligation.
  intros. hnf; simpl; intros.
  destruct (rint_enum_complete x) as [n [i' [??]]].
  exists n. rewrite H. auto.
Qed.

Lemma rint_cusl : cusl rint_preord.
Proof.
  constructor.
  intros.
  
  destruct (Qlt_le_dec (rint_start x) (rint_start y)) as [H|H].
  destruct (Qlt_le_dec (rint_end x) (rint_end y)) as [H0|H0].
  destruct (Qlt_le_dec (rint_end x) (rint_start y)) as [H1|H1].

  right.
  intros.
  apply rint_ord_test in H2.
  apply rint_ord_test in H3.
  intuition.
  generalize (rint_proper z). intros.
  assert (rint_end x < rint_end x).
  apply Qlt_le_trans with (rint_start y); auto.
  apply Qle_trans with (rint_start z); auto.
  apply Qle_trans with (rint_end z); auto.
  red in H7. omega.
  left.
  exists (RatInt _ _ H1).
  split; simpl; intros.
  apply rint_ord_test. simpl.
  split; auto.
  apply Qlt_le_weak; auto.
  apply Qle_refl.
  split; auto.
  apply rint_ord_test. simpl.
  split.
  apply Qle_refl.
  apply Qlt_le_weak; auto.

  intros.
  apply rint_ord_test. simpl.
  apply rint_ord_test in H2; destruct H2.
  apply rint_ord_test in H3; destruct H3.
  split; auto.
  
  left.
  exists y.
  split.
  apply rint_ord_test.
  split; auto.
  apply Qlt_le_weak. auto.
  split; auto.

  destruct (Qlt_le_dec (rint_end x) (rint_end y)) as [H0|H0].
  left.
  exists x.
  split. auto.
  split; auto.
  apply rint_ord_test.
  split; auto.
  apply Qlt_le_weak. auto.

  destruct (Qlt_le_dec (rint_end y) (rint_start x)) as [H1|H1].
  right. intros.
  apply rint_ord_test in H2.
  apply rint_ord_test in H3.
  destruct H2. destruct H3.
  assert (rint_end y < rint_end y).
  apply Qlt_le_trans with (rint_start x); auto.
  apply Qle_trans with (rint_start z); auto.
  apply Qle_trans with (rint_end z); auto.
  apply rint_proper.
  red in H6. omega.
  
  left. exists (RatInt _ _ H1).
  split.
  apply rint_ord_test. simpl.
  split; auto. apply Qle_refl.
  split.
  apply rint_ord_test. simpl.
  split; auto. apply Qle_refl.
  intros.
  apply rint_ord_test. simpl.
  apply rint_ord_test in H2.
  apply rint_ord_test in H3.
  intuition.
Qed.

Lemma rint_plotkin : plotkin_order true rint_preord.
Proof.
  apply cusl_plotkin.
  apply rint_eff.
  apply rint_cusl.
Qed.

Definition RealDom : ∂PLT := 
  PLT.Ob true rational_interval
     (PLT.Class true rational_interval rint_preord_mixin rint_eff rint_plotkin).

