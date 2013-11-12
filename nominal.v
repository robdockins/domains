Require Import Setoid.

Require Import basics.
Require Import categories.
Require Import preord.
Require Import sets.
Require Import finsets.
Require Import atoms.

Obligation Tactic := intuition.

Require Import List.

Module PERM.

Record perm :=
  Perm
  { perm_f : atom -> atom
  ; perm_g : atom -> atom
  ; perm_support : finset atom
  ; perm_gf : forall x, perm_g (perm_f x) = x
  ; perm_fg : forall x, perm_f (perm_g x) = x
  ; perm_support_axiom : 
       (forall v, v ∈ perm_support \/ perm_f v = v)
  }.

Program Definition eq_mixin : Eq.mixin_of perm :=
  Eq.Mixin perm (fun a b => forall x, perm_f a x = perm_f b x) _ _ _.
Next Obligation.
  rewrite H; auto.
Qed.

Canonical Structure eq : Eq.type :=
  Eq.Pack perm eq_mixin.

Definition ident : perm :=
  Perm (fun x => x) (fun x => x) nil
  (fun x => Logic.eq_refl x) (fun x => Logic.eq_refl x)
  (fun x => or_intror (Logic.eq_refl x)).

Program Definition compose (p1:perm) (p2:perm) : perm :=
  Perm (fun x => perm_f p1 (perm_f p2 x))
       (fun x => perm_g p2 (perm_g p1 x))
       (perm_support p1 ++ perm_support p2)
       _ _ _.
Next Obligation.
  rewrite (perm_gf p1).
  rewrite (perm_gf p2). auto.
Qed.
Next Obligation.
  rewrite (perm_fg p2).
  rewrite (perm_fg p1). auto.
Qed.
Next Obligation.
  destruct (perm_support_axiom p2 v).
  left. apply app_elem; auto.
  rewrite H.
  destruct (perm_support_axiom p1 v).
  left. apply app_elem; auto.
  right; auto.
Qed.

Definition perm' := fun (_ _ :unit) => perm.

Definition comp_mixin : Comp.mixin_of unit perm'
  := Comp.Mixin unit perm' (fun _ => ident) (fun _ _ _ => compose).

Canonical Structure comp : Comp.type :=
  Comp.Pack unit perm' comp_mixin.

Program Definition inv (p:perm' tt tt) : perm' tt tt :=
  Perm (perm_g p) (perm_f p) (perm_support p) (perm_fg p) (perm_gf p) _.
Next Obligation.
  destruct (perm_support_axiom p v); auto.
  right. rewrite <- H at 1.
  apply perm_gf.
Qed.

Lemma inv_inv : forall p,
  inv (inv p) ≈ p.
Proof.
  intros. hnf. simpl. auto.
Qed.

Lemma inv_id1 : forall p:perm' tt tt,
  p ∘ (inv p) ≈ id(tt).
Proof.
  repeat intro. simpl.
  apply perm_fg.
Qed.

Lemma inv_id2 : forall p,
  inv p ∘ p ≈ id(tt).
Proof.
  repeat intro. simpl.
  apply perm_gf.
Qed.

Lemma f_inj : forall p x y,
  perm_f p x = perm_f p y -> x = y.
Proof.
  intros.
  rewrite <- (perm_gf p x).
  rewrite <- (perm_gf p y).
  rewrite H; auto.
Qed.

Lemma g_inj : forall p x y,
  perm_g p x = perm_g p y -> x = y.
Proof.
  intros.
  rewrite <- (perm_fg p x).
  rewrite <- (perm_fg p y).
  rewrite H; auto.
Qed.


Program Definition swap (x y:atom) : perm' tt tt :=
  Perm (fun z => if string_dec x z then y
                   else if string_dec y z then x else z)
       (fun z => if string_dec x z then y
                   else if string_dec y z then x else z) 
       (x::y::nil)
       _ _ _.
Next Obligation.
  rename x0 into z.
  destruct (string_dec x z).
  destruct (string_dec x y). congruence.
  destruct (string_dec y y); congruence.
  destruct (string_dec y z); try congruence.
  destruct (string_dec x x); congruence.
  destruct (string_dec x z). congruence.
  destruct (string_dec y z); try congruence.
Qed.
Next Obligation.
  rename x0 into z.
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

Lemma swap_swap (p q:atom) :
  swap p q ≈ swap q p.
Proof.
  hnf; simpl; intros.
  destruct (string_dec p x).
  destruct (string_dec q x); auto. congruence.
  destruct (string_dec q x); auto.
Qed.  

Lemma perm_assoc (f g h : perm' tt tt) :
  f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  hnf; simpl; intros. auto.
Qed.

Lemma swap_self_inv p q :
  swap p q ∘ swap p q ≈ id(tt).
Proof.
  hnf; simpl; intros.
  apply (perm_fg (swap p q)).
Qed.

Lemma swap_same_id p :
  swap p p ≈ id(tt).
Proof.
  hnf; simpl; intros.
  destruct (string_dec p x); auto.
Qed.

Lemma swap_swizzle (p q r:atom)
  (Hrp : r <> p)
  (Hrq : r <> q)
  (Hpq : p <> q) :
  swap p r ∘ swap r q ≈ swap r q ∘ swap p q.
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

End PERM.

Canonical Structure PERM.eq.
Canonical Structure PERM.comp.
Notation perm := (PERM.perm' tt tt).
Coercion PERM.perm_f : PERM.perm >-> Funclass.


Module NOMINAL.

Record mixin_of (A:Type) (eq_mixin:Eq.mixin_of A) :=
  Mixin
  { Aeq := Eq.Pack A eq_mixin
  ; papp : perm -> Aeq -> Aeq
  ; support : Aeq -> finset atom
  ; nom_ident : forall a, papp id a ≈ a
  ; nom_comp : forall a p1 p2,
       papp p1 (papp p2 a) ≈ papp (p1 ∘ p2) a
  ; papp_respects : forall p p' a a',
       p ≈ p' -> a ≈ a' -> papp p a ≈ papp p' a'
  ; support_axiom : forall (p:perm) a,
       (forall v, v ∈ support a -> p v = v) ->
       papp p a ≈ a
  ; support_papp : forall (p:perm) x v,
       v ∈ support x <-> p v ∈ support (papp p x)
  }.

Record ob :=
  Ob
  { carrier :> Type
  ; eq_mixin : Eq.mixin_of carrier
  ; nominal_mixin : mixin_of carrier eq_mixin
  }.

Canonical Structure ob_eq (A:ob) : Eq.type :=
  Eq.Pack (carrier A) (eq_mixin A).

Definition papp_op (A:ob) : perm -> A -> A :=
  papp (carrier A) (eq_mixin A) (nominal_mixin A).

Definition support_op (A:ob) : A -> finset atom :=
  support (carrier A) (eq_mixin A) (nominal_mixin A).

Record hom (A B:ob) :=
  Hom
  { map :> carrier A -> carrier B
  ; hom_support : finset atom
  ; eq_axiom : forall x y, x ≈ y -> map x ≈ map y
  ; nom_axiom : forall x (p:perm),
       (forall v, v ∈ hom_support -> p v = v) ->
       map (papp_op A p x) ≈ papp_op B p (map x)
  }.

Program Definition ident (A:ob) :=
  Hom A A (fun x => x) nil _ _.

Program Definition compose (A B C:ob) (f:hom B C) (g:hom A B) :=
  Hom A C (fun x => f (g x)) (app (hom_support _ _ f) (hom_support _ _ g))
  _ _.
Next Obligation.
  apply eq_axiom.
  apply eq_axiom.
  auto.
Qed.
Next Obligation.
  transitivity (f (papp_op B p (g x))).
  apply eq_axiom.
  apply nom_axiom.
  intros. apply H.
  apply app_elem. auto.
  apply nom_axiom.
  intros. apply H.
  apply app_elem. auto.
Qed.

Definition comp_mixin : Comp.mixin_of ob hom :=
  Comp.Mixin ob hom ident compose.

Canonical Structure comp := Comp.Pack ob hom comp_mixin.

Program Definition hom_eq_mixin (A B:ob) : Eq.mixin_of (hom A B) :=
  Eq.Mixin (hom A B) (fun f g => forall x, f x ≈ g x) _ _ _.
Next Obligation.
  rewrite H; auto.
Qed.

Lemma category_axioms : Category.category_axioms ob hom hom_eq_mixin comp_mixin.
Proof.
  constructor.
  repeat intro. simpl; auto.
  repeat intro. simpl; auto.
  repeat intro. simpl; auto.
  repeat intro. simpl; auto.
  transitivity (f (g' x)).
  apply eq_axiom. apply H0.
  apply H.
Qed.

Definition cat_class : Category.class_of ob hom :=
  Category.Class ob hom hom_eq_mixin comp_mixin category_axioms.

Canonical Structure NOMINAL : category :=
  Category ob hom cat_class.

Canonical Structure eq (A:ob) : Eq.type := Eq.Pack (carrier A) (eq_mixin A).
Canonical Structure hom_eq (A B:ob) : Eq.type := Eq.Pack (hom A B) (hom_eq_mixin A B).

End NOMINAL.

Notation NOMINAL := NOMINAL.NOMINAL.
Notation support := (NOMINAL.support_op _).
Notation nominal := NOMINAL.ob.
Canonical Structure NOMINAL.
Canonical Structure NOMINAL.eq.
Canonical Structure NOMINAL.hom_eq.
Canonical Structure NOMINAL.comp.
Coercion NOMINAL.carrier : NOMINAL.ob >-> Sortclass.

Notation "p · x" := (NOMINAL.papp_op _ p x) (at level 35, right associativity).

Add Parametric Morphism (A:nominal) : 
  (NOMINAL.papp_op A)
  with signature (@eq_op PERM.eq) ==>
                 (@eq_op (NOMINAL.eq A)) ==>
                 (@eq_op (NOMINAL.eq A))
    as papp_morphism.
Proof.           
  intros. apply NOMINAL.papp_respects; auto.
Qed.

Lemma nom_compose (A:nominal) (p1 p2:perm) (x:A) :
  p1 · p2 · x ≈ (p1 ∘ p2) · x.
Proof.
  apply NOMINAL.nom_comp.
Qed.

Lemma nom_compose' (A:nominal) (p p1 p2:perm) (x:A) :
  p1 ∘ p2 ≈ p ->
  p1 · p2 · x ≈ p · x.
Proof.
  intros. rewrite nom_compose. rewrite H. auto.
Qed.

Lemma nom_ident (A:nominal) (x:A) :
  id · x ≈ x.
Proof.
  apply NOMINAL.nom_ident.
Qed.

Lemma nom_ident' (A:nominal) (p:perm) (x:A) :
  p ≈ id(tt) ->
  p · x ≈ x.
Proof.
  intros. rewrite H.
  apply NOMINAL.nom_ident.
Qed.

Lemma support_axiom (A:nominal) (p:perm) (x:A) :
  (forall v, v ∈ support x -> p v = v) ->
  p · x ≈ x.
Proof.
  intros. apply NOMINAL.support_axiom. auto.
Qed.

Lemma support_axiom' (A:nominal) (p:perm) (x:A) :
  (forall v, v ∈ support x -> p v = v) ->
  x ≈ p · x.
Proof.  
  intros. symmetry. apply support_axiom. auto.
Qed.

Lemma support_papp (A:nominal) (p:perm) (x:A) (v:atom) :
  v ∈ support x <-> p v ∈ support (p · x).
Proof.
  intros. apply NOMINAL.support_papp.
Qed.

Lemma papp_inj (A:nominal) (p:perm) (x y:A) :
  p · x ≈ p · y -> x ≈ y.
Proof.
  intros.
  cut ((PERM.inv p ∘ p) · x ≈ (PERM.inv p ∘ p) · y).
  intros.
  rewrite PERM.inv_id2 in H0.
  rewrite nom_ident in H0.
  rewrite nom_ident in H0.
  auto.
  rewrite <- nom_compose.
  rewrite <- nom_compose.
  rewrite H. auto.
Qed.

Inductive binding_ty (A:nominal) :=
  | bind : atom -> A -> binding_ty A.

Definition binding_equiv (A:nominal) (x y:binding_ty A) :=
  let (v,x') := x in
  let (w,y') := y in
    exists u:atom, u ∉ (v :: w :: support x' ++ support y' : finset atom) /\
      PERM.swap u v · x' ≈ PERM.swap u w · y'.

Lemma fresh_atom_is_fresh' (l1 l2:finset atom) :
  l1 ⊆ l2 ->
  fresh_atom l2 ∉ l1.
Proof.
  repeat intro.
  apply H in H0.
  apply (fresh_atom_is_fresh l2); auto.
Qed.

Program Definition binding_eq_mixin (A:nominal) : Eq.mixin_of (binding_ty A) :=
  Eq.Mixin (binding_ty A) (binding_equiv A) _ _ _.
Next Obligation.
  hnf. destruct x as [v x'].
  exists (fresh_atom (v :: support x')%list).
  split. apply fresh_atom_is_fresh'.
  red; simpl; intros.
  apply cons_elem.
  apply cons_elem in H. destruct H; auto.
  apply cons_elem in H. destruct H; auto.
  apply app_elem in H; destruct H; auto.
  auto.
Qed.
Next Obligation.
  unfold binding_equiv in *.
  destruct x as [v x'].
  destruct y as [w y'].
  destruct H as [u [??]].
  exists u; split; auto.
  red; intro.
  apply H.
  apply cons_elem in H1; destruct H1.
  apply cons_elem. right. apply cons_elem. left. auto.
  apply cons_elem in H1; destruct H1.
  apply cons_elem. left. auto.
  apply cons_elem. right. apply cons_elem. right.
  apply app_elem in H1. apply app_elem. intuition.
Qed.
Next Obligation.
  unfold binding_equiv in *.
  destruct x as [v x'].
  destruct y as [w y'].
  destruct z as [u z'].
  destruct H as [q1 [??]].
  destruct H0 as [q2 [??]].
  destruct (string_dec q1 q2).
  subst q2.
  exists q1. intuition.
  apply cons_elem in H3; destruct H3.
  apply H. apply cons_elem; auto.
  apply cons_elem in H3; destruct H3.
  apply H0.
  apply cons_elem. right. apply cons_elem. left. auto.
  apply app_elem in H3. destruct H3.
  apply H.
  apply cons_elem. right. apply cons_elem. right.
  apply app_elem; auto.
  apply H0.
  apply cons_elem. right. apply cons_elem. right.
  apply app_elem; auto.
  rewrite H1. auto.

  set (atoms := (q1 :: q2 :: u :: v :: w :: (support x' ++ support y' ++  support z'))).
  set (q := fresh_atom atoms).
  exists q.
  split.
  intro.
  intros.
  eapply fresh_atom_is_fresh'.
  2: unfold q in H3; apply H3.
  unfold atoms.
    hnf; simpl; intros.
    apply cons_elem in H4. destruct H4.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. auto.
    apply cons_elem in H4. destruct H4.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. auto.
    apply app_elem in H4. destruct H4.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem; auto.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. auto.

  assert (Hqu: q <> u).
    intro.
    apply (fresh_atom_is_fresh atoms).
    fold q. rewrite H3.
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. auto.
  assert (Hqq2: q <> q2).
    intro.
    apply (fresh_atom_is_fresh atoms).
    fold q. rewrite H3.
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. auto.
  assert (Huq2 : u <> q2).
    intro.
    apply H0. rewrite H3.
    apply cons_elem. right.
    apply cons_elem. auto.
  assert (Hqw: q <> w).
    intro.
    apply (fresh_atom_is_fresh atoms).
    fold q. rewrite H3.
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. auto.
  assert (Hwq2: w <> q2).
    intro. apply H0. rewrite H3.
    apply cons_elem. auto.
  assert (Hqv : q <> v).
    intro.
    apply (fresh_atom_is_fresh atoms).
    fold q. rewrite H3.
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. auto.
  assert (Hqq1 : q <> q1).
    intro.
    apply (fresh_atom_is_fresh atoms).
    fold q. rewrite H3.
    unfold atoms.
    apply cons_elem. auto.
  assert (Hvq1 : v <> q1).
    intro.
    apply H. rewrite H3.
    apply cons_elem. auto.
  assert (Hwq1 : w <> q1).
    intro. apply H. rewrite H3.
    apply cons_elem. right.
    apply cons_elem. auto.

  rewrite <- (support_axiom A (PERM.swap q q1) x').
  rewrite (PERM.swap_swap q v).
  rewrite nom_compose.
  rewrite PERM.swap_swizzle; auto.
  rewrite <- nom_compose.
  rewrite (PERM.swap_swap v q1).
  rewrite H1.
  rewrite (PERM.swap_swap q1 w).
  rewrite nom_compose.
  rewrite <- PERM.swap_swizzle; auto.
  rewrite <- nom_compose.
  rewrite (support_axiom A (PERM.swap q q1) y').
  rewrite <- (support_axiom A (PERM.swap q q2) y').
  rewrite nom_compose.
  rewrite PERM.swap_swizzle; auto.
  rewrite <- nom_compose.
  rewrite (PERM.swap_swap w q2).
  rewrite H2.
  rewrite (PERM.swap_swap q2 u).
  rewrite nom_compose.
  rewrite <- PERM.swap_swizzle; auto.
  rewrite <- nom_compose.
  rewrite (support_axiom A (PERM.swap q q2) z').
  rewrite (PERM.swap_swap u q). auto.
  
  intros. simpl.
  destruct (string_dec q v0).
  subst v0.
    elimtype False.
    apply (fresh_atom_is_fresh atoms).
    fold q. 
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. right.
    auto.
  destruct (string_dec q2 v0).
  subst v0.
    elim H0.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. auto.
  auto.
  
  intros. simpl.
  destruct (string_dec q v0).
  subst v0.
    elimtype False.
    apply (fresh_atom_is_fresh atoms).
    fold q. 
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem.  auto.
  destruct (string_dec q2 v0); auto.
  subst v0.
    elim H0.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. auto.
  
  intros. simpl.
  destruct (string_dec q v0).
  subst v0.
    elimtype False.
    apply (fresh_atom_is_fresh atoms).
    fold q. 
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. auto.
  destruct (string_dec q1 v0); auto.
  subst v0.
    elim H.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. auto.
  
  intros. simpl.
  destruct (string_dec q v0).
  subst v0.
    elimtype False.
    apply (fresh_atom_is_fresh atoms).
    fold q. 
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. auto.
  destruct (string_dec q1 v0); auto.
  subst v0.
     elim H.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. auto.
Qed.     


Canonical Structure binding_eq (A:nominal) :=
  Eq.Pack (binding_ty A) (binding_eq_mixin A).

Definition binding_papp (A:nominal) (p:perm) (x:binding_ty A) :=
  match x with
  | bind v x' => bind A (p v) (p · x')
  end.

Definition binding_support (A:nominal) (x:binding_ty A) :=
  match x with
  | bind a x' => finset_remove atom_dec (support x') a
  end.

Lemma swap_commute u w (p:perm) :
  PERM.swap (p u) (p w) ∘ p ≈ p ∘ PERM.swap u w.
Proof.
  hnf; simpl; intros.
  destruct (string_dec u x).
  destruct (string_dec (p u) (p x)); auto.
  elim n. rewrite e; auto.
  destruct (string_dec (p u) (p x)); auto.
  elim n.
  apply (PERM.f_inj p) in e. auto.
  destruct (string_dec w x).
  destruct (string_dec (p w) (p x)); auto.
  elim n1. rewrite e; auto.
  destruct (string_dec (p w) (p x)); auto.
  elim n1.
  apply (PERM.f_inj p) in e. auto.
Qed.  

Program Definition binding_nominal_mixin (A:nominal) :
  NOMINAL.mixin_of (binding_ty A) (binding_eq_mixin A) :=
  NOMINAL.Mixin (binding_ty A) (binding_eq_mixin A)
    (binding_papp A) 
    (binding_support A)
    _ _ _ _ _.
Next Obligation.
  red; simpl.
  destruct a as [v a]; simpl.
  set (u := fresh_atom (v::support a)).
  exists u. split.
  apply (fresh_atom_is_fresh').
  hnf; simpl; intros.
  apply cons_elem.
  apply cons_elem in H. destruct H; auto.
  apply cons_elem in H. destruct H; auto.
  apply app_elem in H.
  destruct H; auto.
  right.
  rewrite (support_papp A id(tt)).
  simpl. auto.
  rewrite nom_ident. auto.
Qed.
Next Obligation.
  unfold binding_papp. destruct a; simpl.
  red. simpl.
  set (u := fresh_atom ((p1 (p2 c)) :: p1 (p2 c) ::
    support (p1 · p2 · c0) ++ support ((p1 ∘ p2) · c0))).
  exists u. split.
  apply fresh_atom_is_fresh.  
  rewrite <- nom_compose. auto.
Qed.  
Next Obligation.
  hnf; simpl. destruct a as [u a]. destruct a' as [v b].
  simpl.
  destruct H0 as [w [??]].
  exists (p w). split.
  intro. apply H0.
  apply cons_elem in H2. destruct H2.
  apply cons_elem. left.
  apply atom_strong_eq in H2.
  apply (PERM.f_inj p) in H2. subst u; auto.
  apply cons_elem in H2. destruct H2.
  apply cons_elem. right.
  apply cons_elem. left.
  hnf in H. rewrite H in H2.
  apply atom_strong_eq in H2.
  apply (PERM.f_inj p') in H2. subst v; auto.
  apply app_elem in H2. destruct H2.
  apply support_papp in H2.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; auto.
  rewrite H in H2.
  apply support_papp in H2.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; auto.
  rewrite <- H.
  rewrite <- H.
  rewrite nom_compose.
  rewrite swap_commute.
  rewrite nom_compose.
  rewrite swap_commute.
  rewrite <- nom_compose.
  rewrite H1.
  rewrite nom_compose.
  auto.
Qed.
Next Obligation.
  destruct a as [u a]; simpl.
  hnf; simpl.
  set (atoms := p u :: u :: support (p · a) ++ support a ++ PERM.perm_support p).
  set (w := fresh_atom atoms).
  exists w.
  split. apply fresh_atom_is_fresh'.
  unfold atoms.
    hnf; simpl; intros.
    apply cons_elem in H0; destruct H0.
    apply cons_elem. auto.
    apply cons_elem in H0; destruct H0.
    apply cons_elem. right.
    apply cons_elem. auto.
    apply app_elem in H0. destruct H0.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. auto.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. auto.

  rewrite nom_compose.
  assert (w = p (PERM.inv p w)).
  symmetry. apply PERM.perm_fg.
  pattern w at 1. rewrite H0.
  rewrite swap_commute.
  simpl.
  simpl in H.
  rewrite <- nom_compose.
  destruct (PERM.perm_support_axiom p w).
  elimtype False.
  eapply fresh_atom_is_fresh'.
  2: unfold w in H1; apply H1.
  unfold atoms.
    hnf; simpl; intros.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. auto.
  rewrite (support_axiom A p).
  rewrite <- H1 at 1.
  rewrite PERM.perm_gf. auto.
  simpl; intros.
  rewrite <- H1 in H2.
  rewrite PERM.perm_gf in H2.
  assert (PERM.swap w u v ∈ support a).
  apply (support_papp A (PERM.swap w u)).
  generalize (PERM.swap_self_inv w u v).
  simpl. intros. rewrite H3. auto.
  simpl in H3.
  destruct (string_dec w v).
  subst v. auto.
  destruct (string_dec u v).
  elimtype False.
  eapply fresh_atom_is_fresh'.
  2: unfold w in H3; apply H3.
  unfold atoms.
    hnf; simpl; intros.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. auto.
  apply H.  
  apply finset_remove_elem.
  split; auto.
  intro. apply atom_strong_eq in H4. elim n0; auto.
Qed.
Next Obligation.
  unfold binding_support in *. destruct x as [u x]; simpl in *.
  apply finset_remove_elem in H. destruct H.
  apply finset_remove_elem. split.
  apply support_papp. auto.
  intro. apply H0.
  apply atom_strong_eq in H1.
  apply PERM.f_inj in H1. subst v; auto.
  
  unfold binding_support in *. destruct x as [u x]; simpl in *.
  apply finset_remove_elem in H. destruct H.
  apply finset_remove_elem. split.
  apply support_papp in H. auto.
  intro. apply H0.
  apply atom_strong_eq in H1. subst v. auto.
Qed.
  
Canonical Structure binding (A:nominal) : nominal :=
  NOMINAL.Ob (binding_ty A) (binding_eq_mixin A) (binding_nominal_mixin A).

Program Definition atom_nom_mixin : NOMINAL.mixin_of atom (Preord.ord_eq atom) :=
  NOMINAL.Mixin atom _ PERM.perm_f (fun x => x::nil) _ _ _ _ _.
Next Obligation.
  rewrite H.
  apply atom_strong_eq in H0. subst a. auto.
Qed.
Next Obligation.
  rewrite H; auto.
  apply cons_elem; auto.
Qed.
Next Obligation.
  apply cons_elem in H.  
  destruct H.
  apply atom_strong_eq in H. subst v.
  apply cons_elem; auto.
  apply nil_elem in H. elim H.
  apply cons_elem in H.  
  destruct H.
  apply atom_strong_eq in H. 
  apply PERM.f_inj in H. subst v.
  apply cons_elem; auto.
  apply nil_elem in H. elim H.
Qed.  

Canonical Structure atom_nom : nominal :=
  NOMINAL.Ob atom _ atom_nom_mixin.

Goal (bind atom_nom "a" "a" ≈ bind atom_nom "b" "b").
Proof.
  hnf. simpl. exists "c".
  split; simpl.
  2: cbv; auto.
  intro.
  apply cons_elem in H. destruct H.
  apply atom_strong_eq in H. discriminate.
  apply cons_elem in H. destruct H.
  apply atom_strong_eq in H. discriminate.
  apply cons_elem in H. destruct H.
  apply atom_strong_eq in H. discriminate.
  unfold NOMINAL.support_op in H. simpl in H.
  apply cons_elem in H. destruct H.
  apply atom_strong_eq in H. discriminate.
  apply nil_elem in H. auto.
Qed.

Goal (bind atom_nom "a" "a" ≉ bind atom_nom "b" "c").
Proof.
  intros [u [??]].
  apply atom_strong_eq in H0.
  unfold PERM.swap in H0.
  unfold NOMINAL.papp_op in H0. simpl in H0.
  destruct (string_dec u "a"). subst u.
  simpl in H0. discriminate.
  destruct (string_dec u "c"). subst u.
  discriminate.  
  subst u. eapply n0; auto.
Qed.

Goal (bind atom_nom "a" "c" ≈ bind atom_nom "b" "c").
Proof.
  hnf. exists "d".
  split. 2: cbv; auto.
  intro.
  apply cons_elem in H. destruct H.
  apply atom_strong_eq in H. discriminate.
  apply cons_elem in H. destruct H.
  apply atom_strong_eq in H. discriminate.
  unfold NOMINAL.support_op in H. simpl in H.
  apply cons_elem in H. destruct H.
  apply atom_strong_eq in H. discriminate.
  apply cons_elem in H. destruct H.
  apply atom_strong_eq in H. discriminate.
  apply nil_elem in H. auto.
Qed.
