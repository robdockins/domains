Require Import Setoid.
Require Import NArith.
Require Import List.

Require Import basics.
Require Import categories.
Require Import preord.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import plotkin.

Local Open Scope N_scope.

Lemma N2_eq_dec : forall (x y:N*N), { x = y }+{x <> y}.
Proof.
  decide equality; apply N_eq_dec.
Qed.

Lemma finord_ord_dec1 (Y:list (N*N)) : forall (X:list (N*N)),
  { forall a b, In (a,b) X -> In (a,b) Y } +
  { exists a b, In (a,b) X /\ ~In (a,b) Y }.
Proof. 
  induction X; intros.
  left; simpl; intuition.
  destruct IHX.
  destruct a.
  destruct (in_dec N2_eq_dec (n,n0) Y).
  left; simpl; intuition.
  inversion H0; subst; auto.
  right; eauto.  
  exists n. exists n0. split; simpl; auto.
  right. destruct e as [p [q [??]]]; simpl; eauto.
Qed.

Lemma finord_ord_dec2 (Y:list (N*N)) : forall (X:list (N*N)),
  { forall a b, In (a,b) X -> In (a,a) Y -> In (b,b) Y -> In (a,b) Y } +
  { exists a b, In (a,b) X /\ In (a,a) Y /\ In (b,b) Y /\ ~In (a,b) Y }.
Proof. 
  induction X; intros.
  left; simpl; intuition.
  destruct IHX.
  destruct a.
  destruct (in_dec N2_eq_dec (n,n0) Y).
  left.
  simpl; intuition.
  inversion H2; subst; auto.
  destruct (in_dec N2_eq_dec (n,n) Y).
  destruct (in_dec N2_eq_dec (n0,n0) Y).
  right.
  exists n. exists n0. simpl; intuition.
  left; intros. 
  destruct H.
  inversion H; subst.
  contradiction.
  auto.
  left; intros.
  destruct H.
  inversion H; subst.
  contradiction.
  auto.
  right.
  destruct e as [p [q [?[??]]]].
  simpl; eauto.
  exists p. exists q; intuition.
Qed.

Lemma preord_graph_dec1 : forall (G H:list (N*N)),
  { forall x y, In (x,y) G -> In (x,x) H }
  +
  { ~forall x y, In (x,y) G -> In (x,x) H }.
Proof.
  induction G; simpl; intros.
  left; intuition.
  destruct (IHG H).
  destruct a as [x y].
  destruct (in_dec N2_eq_dec (x,x) H).
  left; simpl; intuition.
  inversion H1; subst; auto.
  eapply i; eauto.
  right; repeat intro.
  apply n. eapply H0; eauto.
  right; repeat intro.  
  apply n; intros.
  eapply H0; eauto.
Qed.

Lemma preord_graph_dec2 : forall (G H:list (N*N)),
  { forall x y, In (x,y) G -> In (y,y) H }
  +
  { ~forall x y, In (x,y) G -> In (y,y) H }.
Proof.
  induction G; simpl; intros.
  left; intuition.
  destruct (IHG H).
  destruct a as [x y].
  destruct (in_dec N2_eq_dec (y,y) H).
  left; simpl; intuition.
  inversion H1; subst; auto.
  eapply i; eauto.
  right; repeat intro.
  apply n. eapply H0; eauto.
  right; repeat intro.  
  apply n; intros.
  eapply H0; eauto.
Qed.

Lemma preord_graph_dec3 : forall (G H I:list (N*N)),
  { forall x y z, In (x,y) G -> In (y,z) H -> In (x,z) I }
  +
  { ~forall x y z, In (x,y) G -> In (y,z) H -> In (x,z) I }.
Proof.
  induction G.
  left; simpl; intuition.
  induction H.
  left; simpl; intuition.
  intro I.
  destruct (IHG (a0::H) I).
  clear IHG.
  destruct (IHlist I).
  destruct a as [x y].  
  destruct a0 as [y' z].
  destruct (in_dec N2_eq_dec (x,z) I).
  left.
  simpl; intuition. inversion H2; inversion H0; subst; auto.
  eapply i0; simpl; eauto.
  eapply i; simpl; eauto.
  eapply i; simpl; eauto.
  destruct (N_eq_dec y y'). subst y'.
  right; repeat intro.
  apply n. eapply H0; simpl; eauto.
  left. simpl; intuition.
  inversion H2; inversion H0; subst.
  elim n0; auto.
  eapply i0; simpl; eauto.
  eapply i; simpl; eauto.
  eapply i0; simpl; eauto.
  right; repeat intro.
  apply n.
  intros. eapply H0; simpl; eauto.
  right; repeat intro.
  apply n.
  intros. eapply H0; simpl; eauto.
Qed.    

Lemma preord_graph_dec4 : forall (hf:bool) (G:list (N*N)),
  { if hf then G <> nil else True }
  +
  { ~if hf then G <> nil else True }.
Proof.
  destruct hf; auto.
  destruct G; simpl; auto.
  left. discriminate.
Qed.

Definition preord_graph (hf:bool) (G:list (N*N)) :=
  (forall x y, In (x,y) G -> In (x,x) G) /\
  (forall x y, In (x,y) G -> In (y,y) G) /\
  (forall x y z, In (x,y) G -> In (y,z) G -> In (x,z) G) /\
  (if hf then G <> nil else True).
  

Lemma preord_graph_dec : forall hf G, { preord_graph hf G } + { ~preord_graph hf G }.
Proof.
  intros hf G.
  destruct (preord_graph_dec1 G G).
  destruct (preord_graph_dec2 G G).
  destruct (preord_graph_dec3 G G G).
  destruct (preord_graph_dec4 hf G).
  left. red; auto.
  right; intros [?[?[??]]]; apply n; auto.
  right; intros [?[?[??]]]; apply n; auto.
  right; intros [?[?[??]]]; apply n; auto.
  right; intros [?[?[??]]]; apply n; auto.
Qed.

Fixpoint graph_intersect (X:list (N*N)) (Y:list (N*N)) : list (N*N) :=
  match X with
  | nil => nil
  | a::X' => if in_dec N2_eq_dec a Y
              then a :: graph_intersect X' Y
              else graph_intersect X' Y
  end.

Lemma graph_intersect_in :
  forall X Y a, In a (graph_intersect X Y) <-> (In a X /\ In a Y).
Proof.
  induction X; simpl.
  intuition.
  intros; split; intros.
  destruct a0.
  destruct (in_dec N2_eq_dec a Y).
  destruct H. subst; auto.
  apply IHX in H.
  destruct H. split; simpl; auto.
  rewrite IHX in H.  
  destruct H; split; simpl; auto.
  destruct H.
  destruct H.
  subst a0.
  destruct (in_dec N2_eq_dec a Y).
  simpl; auto.
  contradiction.
  assert (In a0 (graph_intersect X Y)).  
  rewrite IHX; auto.
  destruct (in_dec N2_eq_dec a Y); simpl; auto.
Qed.  

Lemma preord_graph_intersect (hf:bool) (X Y:list (N*N)) :
  (if hf then exists a, In a X /\ In a Y else True) ->
  preord_graph hf X -> preord_graph hf Y ->
  preord_graph hf (graph_intersect X Y).
Proof.
  repeat intro.
  destruct H0 as [?[?[??]]].
  destruct H1 as [?[?[??]]].
  split; intros.
  apply graph_intersect_in in H8.
  apply graph_intersect_in.
  intuition; eauto.
  split; intros.
  apply graph_intersect_in in H8.
  apply graph_intersect_in.
  intuition; eauto.
  split; intros.
  apply graph_intersect_in in H8.
  apply graph_intersect_in in H9.
  apply graph_intersect_in.
  intuition; eauto.
  destruct hf; auto.
  intro.
  destruct H.
  apply graph_intersect_in in H.
  rewrite H8 in H. elim H.
Qed.

Definition finord hf := { G:list (N*N) | preord_graph hf G }.

Record finord_ord hf (X Y:finord hf) : Prop :=
  FinordOrd
  { fo_ord1 : forall a b, In (a,b) (proj1_sig X) ->
                          In (a,b) (proj1_sig Y)

  ; fo_ord2 : forall a b, In (a,b) (proj1_sig Y) ->
                          In (a,a) (proj1_sig X) -> 
                          In (b,b) (proj1_sig X) ->
                          In (a,b) (proj1_sig X)
  }.

Lemma finord_ord_dec hf (X Y:finord hf) : { finord_ord hf X Y } + {~finord_ord hf X Y}.
Proof.
  destruct (finord_ord_dec1 (proj1_sig Y) (proj1_sig X)).
  destruct (finord_ord_dec2 (proj1_sig X) (proj1_sig Y)).
  left; constructor; auto.
  right. intros [??].
  destruct e as [a [b [?[?[??]]]]].
  apply H2. eauto.
  right. intros [??].
  destruct e as [a [b [??]]].
  apply H0; eauto.
Qed.

Program Definition finord_preord_mixin hf : Preord.mixin_of (finord hf) :=
  Preord.Mixin (finord hf) (finord_ord hf) _ _.
Next Obligation.
  repeat intro.
  constructor; auto.
Qed.
Next Obligation.
  repeat intro. destruct H. destruct H0.
  constructor; intros; eauto.
Qed.

Canonical Structure finord_preord hf : preord :=
  Preord.Pack (finord hf) (finord_preord_mixin hf).


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

Definition enum_finords (hf:bool) : eset (finord_preord hf) :=
 fun n => 
  match finsubsets (Ndisc_ord × Ndisc_ord)
    (eprod (eff_enum _ effective_Nord) (eff_enum _ effective_Nord)) n with
  | None => None
  | Some G => match preord_graph_dec hf G with
              | left H => Some (exist _ G H)
              | right _ => None
              end
  end.

Lemma finord_graph_equiv : forall hf (x y:finord_preord hf),
 x ≈ y <-> (proj1_sig x:finset (Ndisc_ord × Ndisc_ord)) ≈ proj1_sig y.
Proof.
  intros; split; intros.
  destruct H. split.
  hnf. simpl; intros.
  destruct H.
  destruct H1 as [q [??]].
  exists q. split; auto.
  destruct q. apply fo_ord3. auto.
  hnf. simpl; intros.
  destruct H0.
  destruct H1 as [q [??]].
  exists q. split; auto.
  destruct q. apply fo_ord3. auto.

  destruct H.
  split. constructor.
  intros.
  destruct (H (a,b)).
  exists (a,b); auto.
  destruct H2.
  replace (a,b) with x0; auto.
  destruct H3.
  destruct H4. simpl in *.
  hnf in H4. hnf in H5. subst; auto.
  destruct x0; auto.
  intros.
  destruct (H0 (a,b)).
  exists (a,b); auto.
  destruct H4.
  replace (a,b) with x0; auto.
  destruct H5.
  destruct H6. simpl in *.
  hnf in H6. hnf in H7. subst; auto.
  destruct x0; auto.
  constructor.
  intros.
  destruct (H0 (a,b)).
  exists (a,b); auto.
  destruct H2.
  replace (a,b) with x0; auto.
  destruct H3.
  destruct H4. simpl in *.
  hnf in H4. hnf in H5. subst; auto.
  destruct x0; auto.
  intros.
  destruct (H (a,b)).
  exists (a,b); auto.
  destruct H4.
  replace (a,b) with x0; auto.
  destruct H5.
  destruct H6. simpl in *.
  hnf in H6. hnf in H7. subst; auto.
  destruct x0; auto.
Qed.

Lemma preord_graph_eq_incl (G G':finset (Ndisc_ord × Ndisc_ord)) :
  G ≤ G' -> List.incl G G'.
Proof.
  repeat intro.
  destruct (H a). exists a; split; auto.
  destruct H1.
  replace a with x; auto.
  destruct H2. destruct H2. destruct x; destruct a; auto.
  compute in *. subst; auto.
Qed.

Lemma preord_graph_ok hf (G G':finset (Ndisc_ord × Ndisc_ord)) :
  G ≈ G' -> preord_graph hf G -> preord_graph hf G'.
Proof.
  intros.
  destruct H.
  destruct H0 as [?[?[??]]].
  split; intros.
  apply preord_graph_eq_incl with G; auto.
  apply H0 with y.
  apply preord_graph_eq_incl with G'; auto.
  split; intros.
  apply preord_graph_eq_incl with G; auto.
  apply H2 with x.
  apply preord_graph_eq_incl with G'; auto.
  split; intros.
  apply preord_graph_eq_incl with G; auto.
  apply H3 with y.
  apply preord_graph_eq_incl with G'; auto.
  apply preord_graph_eq_incl with G'; auto.
  destruct hf; auto.
  intro. apply H4.
  destruct G'.
  destruct G; auto.
  destruct (H c).
  apply cons_elem; auto.
  destruct H6. elim H6.
  discriminate.
Qed.  

Program Definition effective_finords hf : effective_order (finord_preord hf) :=
  EffectiveOrder (finord_preord hf) (finord_ord_dec hf) (enum_finords hf) _.
Next Obligation.
  intros.
  assert ((proj1_sig x : finset (Ndisc_ord × Ndisc_ord)) ∈ 
    finsubsets (Ndisc_ord × Ndisc_ord)
    (eprod (eff_enum _ effective_Nord) (eff_enum _ effective_Nord))).
  apply finsubsets_complete.
  red; intros.
  destruct a.
  apply elem_eprod.
  split; apply eff_complete.
  destruct H as [n ?].
  exists n.
  unfold enum_finords.
  destruct (finsubsets (Ndisc_ord × Ndisc_ord)
            (eprod (eff_enum Ndisc_ord effective_Nord)
              (eff_enum Ndisc_ord effective_Nord)) n).
  destruct (preord_graph_dec hf c).
  apply finord_graph_equiv. auto.
  apply n0.
  apply preord_graph_ok with (proj1_sig x); auto.
  apply proj2_sig.
  auto.
Qed.

