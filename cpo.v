(* Copyright (c) 2014, Robert Dockins *)

Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import directed.

Module CPO.
  Record mixin_of (CL:color) (A:preord) 
    := Mixin
    { sup : cl_eset CL A -> A
    ; sup_is_ub : forall X, upper_bound (sup X) X 
    ; sup_is_least : forall X ub, upper_bound ub X -> sup X ≤ ub
    }.

  Record type (CL:color) := Pack
    { carrier :> Type
    ; ord_mixin : Preord.mixin_of carrier
    ; ord := Preord.Pack carrier ord_mixin
    ; cpo_mixin : mixin_of CL ord
    }.

  Arguments carrier [CL] t.
  Arguments ord [CL] t.
  Arguments cpo_mixin [CL] t.

  Hint Resolve cpo_mixin.
  Canonical Structure ord.

  Definition cpo_eq CL (T:type CL) : Eq.type :=
    Eq.Pack (carrier T) (Eq.mixin (Preord_Eq (ord T))).
  Canonical Structure cpo_eq.

  Definition sup_op CL (t:type CL) : cl_eset CL (ord t) -> ord t :=
    sup CL (ord t) (cpo_mixin t).
  Arguments sup_op [CL] [t] X.

  Record hom CL (A B:type CL) :=
    Hom
    { map :> ord A -> ord B
    ; mono : forall (a b:carrier A), 
               Preord.ord_op (ord A) a b ->
               Preord.ord_op (ord B) (map a) (map b)
    ; axiom' : forall X, map (sup_op X) ≤ sup_op (image (Preord.Hom _ _ map mono) X)
    }.
  Arguments map [CL] [A] [B] h x.
  Arguments mono [CL] [A] [B] h a b _.
  Arguments axiom'  [CL] [A] [B] h X.
  
  Definition ord_hom {CL:color} {A B:type CL} (f:hom CL A B) : Preord.hom (ord A) (ord B) :=
    Preord.Hom _ _ (map f) (mono f).
  Coercion ord_hom : hom >-> Preord.hom.

  Program Definition build_hom {CL:color} (A B:type CL)
    (f:Preord.hom (ord A) (ord B))
    (H:forall X, f#(sup_op X) ≤ sup_op (image f X))
    : hom CL A B
    := Hom CL A B (Preord.map _ _ f) _ _.
  Next Obligation.
    simpl; intros. apply Preord.axiom. auto.
  Qed.
  Next Obligation.
    simpl; intros.
    etransitivity.
    apply H.
    apply sup_is_least; auto.
    red; simpl. intros.
    apply sup_is_ub; auto.
  Qed.    

  Program Definition ident {CL:color} (X:type CL) :
    hom CL X X := build_hom X X (Preord.ident (ord X)) _.
  Next Obligation.
    simpl; intros.
    apply sup_is_least; auto.
    red. intros.
    apply sup_is_ub; auto.
    destruct H as [n ?].
    exists n. simpl in *.
    unfold eset.eimage.
    case_eq (proj1_sig X0 n); auto.
    simpl; intros.
    rewrite H0. rewrite H0 in H. auto.
    simpl; intros. rewrite H0 in H. elim H.
  Qed.

  Program Definition compose {CL:color} {X Y Z:type CL} (g:hom CL Y Z) (f:hom CL X Y)
    := build_hom X Z (g ∘ f) _.
  Next Obligation.
    intros.
    transitivity (ord_hom g#(ord_hom f#(sup_op X0))).
    apply eq_ord. apply hommap_axiom.
    transitivity (ord_hom g#(sup_op (image (ord_hom f) X0))).
    apply Preord.axiom.
    apply axiom'.
    transitivity (sup_op (image g (image f X0))).
    apply axiom'.
    apply sup_is_least; auto.
    red; intros.
    apply sup_is_ub; auto.
    apply image_axiom0. auto.
  Qed.

  Definition comp_mixin CL := Comp.Mixin (type CL) (hom CL) (@ident CL) (@compose CL).
  Canonical Structure comp CL := Comp.Pack (type CL) (hom CL) (comp_mixin CL).

  Definition app {CL:color} {X Y:type CL} (f:hom CL X Y) (x:X) : Y := map f x.

  Definition hom_order {CL:color} (X Y:type CL) (f g:hom CL X Y) :=
    forall x:X, app f x ≤ app g x.

  Program Definition hom_ord_mixin CL X Y :=
    Preord.Mixin (hom CL X Y) (hom_order X Y) _ _.
  Next Obligation.
    repeat intro. auto.
  Qed.
  Next Obligation.
    repeat intro.
    transitivity (app y x0).
    apply (H x0). apply (H0 x0).
  Qed.

  Canonical Structure hom_ord CL (A B:type CL) :=
    Preord.Pack (CPO.hom CL A B) (CPO.hom_ord_mixin CL A B).

  Program Definition app_to CL (X Y:type CL) (x:X) : Preord.hom (hom_ord CL X Y) (ord Y) :=
    Preord.Hom (hom_ord CL X Y) (ord Y) (fun f => map f x) _.
  Next Obligation.
    intros. apply H.
  Qed.

  Program Definition hom_sup CL (X Y:type CL) (FS:cl_eset CL (hom_ord CL X Y)) : hom CL X Y :=
    Hom CL X Y (fun x => sup_op (image (app_to CL X Y x) FS)) _ _.
  Next Obligation.
    intros.
    apply sup_is_least. red; intros.
    apply image_axiom2 in H0.
    destruct H0 as [y [??]].
    rewrite H1.
    transitivity (app_to CL X Y b#y).
    simpl. apply mono. auto.
    apply sup_is_ub.
    apply image_axiom1. auto.
  Qed.
  Next Obligation.
    intros.
    apply sup_is_least. red; intros.
    apply image_axiom2 in H.
    destruct H as [y [??]].
    rewrite H0.
    simpl.
    etransitivity.
    apply axiom'.
    apply sup_is_least. red; intros.
    apply image_axiom2 in H1.
    destruct H1 as [z [??]].
    set (f := {|
          Preord.map := fun x1 : X =>
                        sup_op
                          (colored_sets.cimage eset_theory CL
                             (hom_ord CL X Y) (ord Y) 
                             (app_to CL X Y x1) FS);
          Preord.axiom := hom_sup_obligation_1 CL X Y FS |}).
    transitivity (f#z).
    rewrite H2.
    simpl.
    apply CPO.sup_is_ub.
    change (y z)
      with ((app_to CL X Y z)#y).
    apply image_axiom1. auto.
    apply CPO.sup_is_ub.
    apply image_axiom1. auto.
  Qed.    

  Program Definition hom_mixin CL X Y :=
    Mixin CL (hom_ord CL X Y) (hom_sup CL X Y) _ _.
  Next Obligation.
    intros CL X Y A. red. intros.
    red; intros. unfold hom_sup.
    simpl. red; simpl. intros q.
    apply sup_is_ub.
    change (app x q) with
      ((app_to CL X Y q)#x).
    apply image_axiom1; auto.
  Qed.
  Next Obligation.
    repeat intro.
    unfold hom_sup; simpl.
    apply sup_is_least.
    red; intros.
    apply image_axiom2 in H0.
    destruct H0 as [y [??]].
    rewrite H1.
    simpl.
    apply H. auto.
  Qed.

  Canonical Structure hom_cpo CL X Y := 
    Pack CL (hom CL X Y) (hom_ord_mixin CL X Y) (hom_mixin CL X Y).

  Definition cpo_eq_mixin CL X Y := Preord.ord_eq (hom_ord CL X Y).

  Lemma cat_axioms CL : Category.axioms (type CL) (hom CL) (cpo_eq_mixin CL) (comp_mixin CL).
  Proof.
    constructor.
    
    repeat intro. split. red; simpl; intros. red; simpl; intros. apply ord_refl.
    repeat intro. red; simpl; intros. apply ord_refl.

    repeat intro. split. red; simpl; intros. red; simpl; intros. apply ord_refl.
    repeat intro. red; simpl; intros. apply ord_refl.

    repeat intro. split. 
    red; simpl; intros. red; simpl; intros. apply ord_refl.
    red; simpl; intros. red; simpl; intros. apply ord_refl.
    
    repeat intro. split.
    red; simpl; intros. red; simpl; intros.
    apply ord_trans with (app f (app g' x)).
    unfold app.
    apply mono.
    destruct H0. apply H0.
    destruct H. apply H.
    red; simpl; intros.
    red; simpl; intros.
    apply ord_trans with (app f (app g' x)).
    destruct H. apply H1.
    unfold app; simpl.
    apply mono.
    destruct H0. apply H1.
  Qed.

  Canonical Structure CPO CL := Category (type CL) (hom CL) _ _ (cat_axioms CL).

  Program Definition concrete CL : concrete (CPO CL) :=
    Concrete
      (CPO CL)
      (@carrier CL)
      (fun X => Eq.mixin (Preord_Eq (ord X)))
      (@app CL)
      _ _.
  Next Obligation.
    intros.
    apply Eq.trans with (app f y).
    change (ord_hom f#(x:ord A) ≈ ord_hom f#(y:ord A)).
    apply preord_eq. auto.    
    destruct H. simpl.
    split; auto.
  Qed.
  Next Obligation.
    intros. simpl. split; apply Preord.refl.
  Qed.
  Canonical Structure concrete.

  Lemma axiom : forall CL (A B:ob (CPO CL)) (f:A → B),
    forall X, 
      f#(sup_op X) ≈ sup_op (image f X).
  Proof.
    intros. apply ord_antisym. apply axiom'.

    apply sup_is_least.
    red. intros.
    apply image_axiom2 in H.
    destruct H as [y [??]].
    transitivity (f#y).
    destruct H0; auto.
    apply mono.
    apply sup_is_ub; auto.
  Qed.

  Lemma sup_is_lub : forall CL (A:type CL) (X:cl_eset CL (ord A)),
    least_upper_bound (sup_op X) X.
  Proof.
    split. apply sup_is_ub. apply sup_is_least.
  Qed.

End CPO.

Notation cpo := CPO.type.
Notation CPO := CPO.CPO.

Canonical Structure CPO.
Canonical Structure CPO.concrete.
Canonical Structure CPO.ord.
Canonical Structure CPO.ord_hom.
Canonical Structure CPO.comp.
Canonical Structure CPO.hom_ord.
Canonical Structure CPO.hom_cpo.
Canonical Structure hom_eq CL X Y:=
  Eq.Pack (CPO.hom CL X Y) (Preord.ord_eq (CPO.hom_ord CL X Y)).
Coercion CPO.ord : cpo >-> preord.
Coercion CPO.ord_hom : CPO.hom >-> Preord.hom.

Notation "∐ XS" := (@CPO.sup_op _ _ XS) (at level 10).

Hint Resolve CPO.sup_is_lub.
