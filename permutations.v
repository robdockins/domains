Require Import Setoid.

Require Import basics.
Require Import categories.
Require Import preord.
Require Import sets.
Require Import finsets.
Require Import atoms.

Require Import List.

(**  The [supported] record equips types with an operation to get a
     finite set of atoms; this finite set is called the "support."
     This record contains no axioms about the support, but is inteded
     to be used with nominal types, as defined in nominal.v.  We define
     [supported] here because it is convenient to have notation for the
     support of a finite permuatation and disjointness of support
     before we can define the nominal types.

     When [x] is an element of a supported type, we write [‖x‖] for
     the support of [x], and when [y] is also an element of a possibly
     different supported type, we write [x♯y] to mean that the
     support of [x] and [y] are disjoint.
  *)
Module Support.
  Record supported :=
  Supported
  { carrier :> Type
  ; support : carrier -> finset atom
  }.

  Definition disjoint (A B:supported) (a:A) (b:B) :=
    forall v, v ∈ support A a -> v ∈ support B b -> False.
End Support.

Arguments Support.support : simpl never.

Notation supported := Support.supported.
Notation Supported := Support.Supported.
Notation "‖ x ‖" := (Support.support _ x) (at level 20, format "‖ x ‖").
Notation "a ♯ b" := (Support.disjoint _ _ a b) 
   (at level 25, no associativity, format "a ♯ b").


(**  Here we define finitely supported permuatations of atoms.  Such
     permutations play an important role in the developement of nominal types.
     The support of a permutation is a finite set that contains all the
     atoms _not_ fixed by the permutation.  Note: the support may be larger
     that necessary; that is, it may contain atoms that are nonetheless
     fixed by the permutation.  In other words, for a permutation [p] every
     atom [v] is either in the support of [p] or else [p v = v].

     Permutations form a category (with a single object) and have inverses.
     When [p] and [q] are permuatations, we write [p ∘ q] for the composition,
     and [p⁻¹] represents the inverse permuatation.  [u ⇋ v] is the permuatation
     that swaps atoms [u] and [v].

     Because we only deal with the finitely supported permutations, we can
     prove interesting "swap induction" principles, where the inductive
     step must only consider only swapping of two variables.  These induction
     principles witness the fact that every finitely supported permutation
     is equivelant to a finite composition of swappings.
  *)
Module Perm.

Record perm (A B:unit) :=
  Perm
  { f : atom -> atom
  ; g : atom -> atom
  ; support : finset atom
  ; gf : forall x, g (f x) = x
  ; fg : forall x, f (g x) = x
  ; support_axiom : forall v, v ∈ support \/ f v = v
  }.
Arguments f [A B] _ _.
Arguments g [A B] _ _.
Arguments support [A B] _.
Arguments fg [A B] _ _.
Arguments gf [A B] _ _.
Arguments support_axiom [A B] _ _.

Canonical Structure perm_support (A B:unit)  : supported :=
  Supported (perm A B) (@support A B).

Program Definition eq_mixin (A B:unit) : Eq.mixin_of (perm A B) :=
  Eq.Mixin (perm A B) (fun a b => forall x, f a x = f b x) _ _ _.
Solve Obligations using intuition eauto.
Next Obligation. 
  intros. rewrite H. auto.
Qed.

Canonical Structure eq (A B:unit) : Eq.type :=
  Eq.Pack (perm A B) (eq_mixin A B).

Definition ident A : perm A A :=
  Perm A A (fun x => x) (fun x => x) nil
  (fun x => Logic.eq_refl x)
  (fun x => Logic.eq_refl x)
  (fun x => or_intror (Logic.eq_refl x)).

Program Definition compose A B C (p1:perm B C) (p2:perm A B) : perm A C :=
  Perm A C 
       (fun x => f p1 (f p2 x))
       (fun x => g p2 (g p1 x))
       (‖p1‖ ++ ‖p2‖)
       _ _ _.
Next Obligation.
  intros.
  rewrite (gf p1).
  rewrite (gf p2). auto.
Qed.
Next Obligation.
  intros.
  rewrite (fg p2).
  rewrite (fg p1). auto.
Qed.
Next Obligation.
  intros.
  destruct (support_axiom p2 v).
  left. apply app_elem; auto.
  rewrite H.
  destruct (support_axiom p1 v).
  left. apply app_elem; auto.
  right; auto.
Qed.

Definition comp_mixin : Comp.mixin_of unit perm
  := Comp.Mixin unit perm ident compose.

Canonical Structure comp : Comp.type :=
  Comp.Pack unit perm comp_mixin.

Lemma category_axioms : Category.axioms unit perm eq_mixin comp_mixin.
Proof.
  constructor; simpl; intros; auto.
  hnf; simpl; auto.
  hnf; simpl; auto.
  hnf; simpl; auto.
  hnf; simpl; intro.
  rewrite H. rewrite H0. auto.
Qed.

Canonical Structure PERM : category
  := Category unit perm eq_mixin comp_mixin category_axioms.

Program Definition inv A B (p:perm A B) : perm B A:=
  Perm B A (g p) (f p) (support p) (fg p) (gf p) _.
Next Obligation.
  intros.
  destruct (support_axiom p v); auto.
  right. rewrite <- H at 1.
  apply gf.
Qed.

Lemma inv_id1 : forall A B (p:perm A B),
  p ∘ (inv A B p) ≈ id(B).
Proof.
  repeat intro. simpl.
  apply fg.
Qed.

Lemma inv_id2 : forall A B (p:perm A B),
  inv A B p ∘ p ≈ id(A).
Proof.
  repeat intro. simpl.
  apply gf.
Qed.

Program Definition groupoid_mixin 
  := Groupoid.Mixin
       unit perm
       eq_mixin
       comp_mixin
       inv _.
Next Obligation.
  constructor.
  apply inv_id1.
  apply inv_id2.
Qed.

Definition groupoid :=
  Groupoid 
       unit perm
       eq_mixin
       comp_mixin
       category_axioms
       groupoid_mixin.

Lemma f_inj : forall A B (p:perm A B) x y,
  f p x = f p y -> x = y.
Proof.
  intros.
  rewrite <- (gf p x).
  rewrite <- (gf p y).
  rewrite H; auto.
Qed.

Lemma g_inj : forall A B (p:perm A B) x y,
  g p x = g p y -> x = y.
Proof.
  intros.
  rewrite <- (fg p x).
  rewrite <- (fg p y).
  rewrite H; auto.
Qed.

Program Definition swap A B (x y:atom) : perm A B  :=
  Perm A B 
       (fun z => if string_dec x z then y
                   else if string_dec y z then x else z)
       (fun z => if string_dec x z then y
                   else if string_dec y z then x else z) 
       (x::y::nil)
       _ _ _.
Next Obligation.
  intros. rename x0 into z.
  destruct (string_dec x z).
  destruct (string_dec x y). congruence.
  destruct (string_dec y y); congruence.
  destruct (string_dec y z); try congruence.
  destruct (string_dec x x); congruence.
  destruct (string_dec x z). congruence.
  destruct (string_dec y z); try congruence.
Qed.
Next Obligation.
  intros. rename x0 into z.
  destruct (string_dec x z).
  destruct (string_dec x y).
  congruence.
  destruct (string_dec y y); congruence.
  destruct (string_dec y z).
  destruct (string_dec x x); congruence.
  destruct (string_dec x z). congruence.
  destruct (string_dec y z); congruence.
Qed.
Next Obligation.
  intros.
  destruct (string_dec x v).
  left.
  apply cons_elem; auto.
  left. rewrite e; auto.
  destruct (string_dec y v).
  left.
  rewrite e.
  apply cons_elem; right.
  apply cons_elem; auto.
  auto.
Qed.

Lemma swap_swap A B (p q:atom) :
  swap A B p q ≈ swap A B q p.
Proof.
  hnf; simpl; intros.
  destruct (string_dec p x).
  destruct (string_dec q x); auto. congruence.
  destruct (string_dec q x); auto.
Qed.

Lemma assoc (f g h : perm tt tt) :
  f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  hnf; simpl; intros. auto.
Qed.

Lemma swap_self_inv A B p q :
  swap A B p q ∘ swap B A p q ≈ id(B).
Proof.
  hnf; simpl; intros.
  apply (fg (swap B A p q)).
Qed.

Lemma swap_same_id A p :
  swap A A p p ≈ id(A).
Proof.
  hnf; simpl; intros.
  destruct (string_dec p x); auto.
Qed.

Lemma swap_swizzle A B C (p q r:atom)
  (Hrp : r <> p) (Hrq : r <> q) (Hpq : p <> q) :
  swap B C p r ∘ swap A B r q ≈
  swap B C r q ∘ swap A B p q.
Proof.
  intros. hnf. simpl. intros.
  destruct (string_dec r x). subst x.
  destruct (string_dec p q); auto.
  elim Hpq; auto.
  destruct (string_dec r q). elim Hrq; auto.
  destruct (string_dec p r). elim Hrp; auto.
  destruct (string_dec p r). elim Hrp; auto.
  destruct (string_dec q r). elim Hrq; auto.
  destruct (string_dec r r); auto. elim n4; auto.
  destruct (string_dec q x). subst x.
  destruct (string_dec r r). 2: elim n0.
  destruct (string_dec p q).
  elim Hpq; auto.
  destruct (string_dec p r). elim Hrp; auto.
  destruct (string_dec r p). elim Hrp; auto.
  destruct (string_dec q p). elim Hpq; auto.
  auto.
  auto.
  destruct (string_dec p x). subst x.
  destruct (string_dec r q); auto.
  destruct (string_dec q q); auto. elim n2; auto.
  destruct (string_dec r x). contradiction.
  destruct (string_dec q x); auto. contradiction.
Qed.

Lemma support_perm A B (p:perm A B) (v:atom) : 
  v ∈ support p <-> f p v ∈ support p.
Proof.
  split; intros.
  destruct (support_axiom p (f p v)); auto.
  apply f_inj in H0. rewrite H0. auto.
  destruct (support_axiom p v); auto.
  rewrite <- H0. auto.
Qed.

Lemma support_perm' A B (p:perm A B) (v:atom) : 
  v ∈ support p <-> f (inv A B p) v ∈ support p.
Proof.
  split; intros.
  apply support_perm.
  simpl. rewrite fg. auto.
  apply support_perm in H.
  simpl in H. rewrite fg in H. auto.
Qed.

End Perm.

Canonical Structure Perm.eq.
Canonical Structure Perm.comp.
Canonical Structure Perm.perm_support.
Canonical Structure Perm.PERM.
Canonical Structure Perm.groupoid.

Notation perm := (Perm.perm tt tt).
Notation PERM := Perm.PERM.
Coercion Perm.f : Perm.perm >-> Funclass.

Notation "u ⇋ v" := (Perm.swap tt tt u v) (at level 20, no associativity).

(**  Permutations with disjoint support commute. *)
Lemma perm_commute (p q:perm) :
  p♯q -> p ∘ q ≈ q ∘ p.
Proof.
  intro.
  hnf; simpl; intros.
  destruct (Perm.support_axiom p x).
  destruct (Perm.support_axiom q x).
  elim (H x); auto.
  rewrite H1.
  destruct (Perm.support_axiom q (p x)).
  elim (H (p x)); auto.
  rewrite <- Perm.support_perm; auto.
  auto.
  rewrite H0.
  destruct (Perm.support_axiom p (q x)).
  destruct (Perm.support_axiom q x).
  elim (H (q x)); auto.
  rewrite <- Perm.support_perm; auto.
  rewrite H2. auto.
  auto.  
Qed.

(**  Swappings commute with any permutation by
     applying the permuatation to the swapped atoms.
  *)
Lemma swap_commute u w (p:perm) :
  (p u ⇋ p w) ∘ p ≈ p ∘ (u ⇋ w).
Proof.
  hnf; simpl; intros.
  destruct (string_dec u x).
  destruct (string_dec (p u) (p x)); auto.
  elim n. rewrite e; auto.
  destruct (string_dec (p u) (p x)); auto.
  elim n.
  apply (Perm.f_inj _ _ p) in e. auto.
  destruct (string_dec w x).
  destruct (string_dec (p w) (p x)); auto.
  elim n1. rewrite e; auto.
  destruct (string_dec (p w) (p x)); auto.
  elim n1.
  apply (Perm.f_inj _ _ p) in e. auto.
Qed.

Lemma swap_commute' u w (p:perm) :
  (u ⇋ w) ∘ p ≈ p ∘ (p⁻¹ u ⇋ p⁻¹ w).
Proof.
  rewrite <- swap_commute.
  simpl.
  rewrite Perm.fg.
  rewrite Perm.fg.
  reflexivity.
Qed.

(**  Here we prove the swapping induction principles.  The first
     decomposes a permutation on the left; the second decomposes
     on the right.

     These induction principles are proved by induction on the
     size of the support set of a permutation.  At each step
     we can reduce the support by applying a swap. 
  *)
Require Import Arith.

Lemma swap_induction (P:perm -> Prop) :
  (forall p p', p ≈ p' -> P p -> P p') ->
  P id ->
  (forall u v (p:perm), p u = u -> u <> v -> P p -> P (u ⇋ v ∘ p)) ->
  forall p, P p.
Proof.
  intros Heq Hbase Hind.
  induction p using (induction_ltof1 perm (fun p => length (Perm.support p))).
  case_eq (Perm.support p); intros.
  apply Heq with id(tt). 
  hnf; simpl.
  intro x.
  destruct (Perm.support_axiom p x); auto.
  rewrite H0 in H1.
  apply nil_elem in H1. elim H1.
  apply Hbase.

  set (f' x := (c ⇋ (p c)) (p x)).
  set (g' x := Perm.g p ((c ⇋ (p c)) x)).
  assert (Hgf : forall x, g' (f' x) = x).
    unfold g'; unfold f'. simpl.
    intro x.
    destruct (string_dec c (p x)).
    destruct (string_dec c (p c)).
    rewrite <- e0. 
    rewrite e.
    apply Perm.gf.
    destruct (string_dec (p c) (p c)); auto.
    rewrite e.
    apply Perm.gf.
    elim n0; auto.
    destruct (string_dec (p c) (p x)); auto.
    destruct (string_dec c c); auto.
    rewrite e.
    apply Perm.gf.
    elim n0. auto.
    destruct (string_dec c (p x)).
    contradiction.
    destruct (string_dec (p c) (p x)); auto.
    contradiction.
    apply Perm.gf.
    
  assert (Hfg : forall x, f' (g' x) = x).    
    unfold g'; unfold f'. simpl.
    intro x.
    destruct (string_dec c x).
    subst x.
    rewrite Perm.fg.
    destruct (string_dec (p c) (p c)).
    destruct (string_dec c (p c)); auto.
    elim n; auto.
    rewrite Perm.fg.
    destruct (string_dec (p c) x).
    rewrite e.
    destruct (string_dec c c); auto.
    elim n0. auto.
    destruct (string_dec c x); auto.
    contradiction.
    destruct (string_dec (p c) x); auto.
    contradiction.
  assert (Hsupport : forall v, v ∈ (l:finset atom) \/ f' v = v).
    intros.
    destruct (Perm.support_axiom p v); auto.
    rewrite H0 in H1.
    apply cons_elem in H1.
    destruct H1.
    right.
    apply atom_strong_eq in H1. subst v.
    unfold f'. simpl.
    destruct (string_dec (p c) (p c)).
    destruct (string_dec c (p c)); auto.
    elim n; auto.
    auto.
    right. unfold f'.
    simpl. rewrite H1.
    destruct (string_dec c v).
    subst v; auto.
    destruct (string_dec (p c) v).
    rewrite <- H1 in e.
    apply Perm.f_inj in e. auto.
    auto.

  set (p' := Perm.Perm tt tt f' g' l Hgf Hfg Hsupport : perm).
  destruct (string_dec c (p c)).
  apply Heq with p'.
  hnf; simpl.
  unfold f'; simpl; intros.
  destruct (string_dec c (p x)).
  rewrite <- e. rewrite <- e0. auto.
  destruct (string_dec (p c) (p x)).
  rewrite <- e0; auto. auto.
  
  apply H.
  hnf; simpl.
  rewrite H0. simpl. auto.

  apply Heq with (c ⇋ (p c) ∘ p').
  hnf; simpl.
  intro x. unfold f'. simpl.
  destruct (string_dec c (p x)).
  destruct (string_dec c (p c)).
  rewrite <- e. rewrite <- e0. auto.
  rewrite <- e.
  destruct (string_dec (p c) (p c)); auto.
  elim n1; auto.
  destruct (string_dec (p c) (p x)); auto.
  destruct (string_dec c c); auto.
  elim n1. auto.
  destruct (string_dec (p c) (p x)); auto.
  contradiction.
  destruct (string_dec c (p x)).
  contradiction.
  auto.

  apply Hind.
  simpl. unfold f'.
  simpl.
  destruct (string_dec c (p c)); auto.
  destruct (string_dec (p c) (p c)); auto.
  elim n1; auto.
  auto.

  apply H.
  hnf; simpl.
  rewrite H0. simpl. auto.
Qed.

Lemma swap_induction' (P:perm -> Prop) :
  (forall p p', p ≈ p' -> P p -> P p') ->
  P id ->
  (forall u v (p:perm), p u = u -> u <> v -> P p -> P (p ∘ u ⇋ v)) ->
  forall p, P p.
Proof.
  intros.
  apply swap_induction; auto.
  intros.
  apply H with
    (p0 ∘ (Perm.g p0 u) ⇋ (Perm.g p0 v)).
  2: apply H1; auto.
  symmetry; apply swap_commute'.
  rewrite Perm.fg.
  rewrite <- H2 at 2.
  rewrite Perm.gf.
  auto.
  intro. apply Perm.g_inj in H5. elim H3; auto.
Qed.  
