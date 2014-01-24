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
      f (sup_op X) ≈ sup_op (image f X).
  Proof.
    intros. apply ord_antisym. apply axiom'.

    apply sup_is_least.
    red. intros.
    apply image_axiom2 in H.
    destruct H as [y [??]].
    transitivity (f y).
    destruct H0; auto.
    apply mono.
    apply sup_is_ub; auto.
  Qed.

  Lemma sup_is_lub : forall CL (A:type CL) (X:cl_eset CL (ord A)),
    least_upper_bound (sup_op X) X.
  Proof.
    split. apply sup_is_ub. apply sup_is_least.
  Qed.

  Section prod.  
    Variable CL:color.
    Variables A B:type CL.

    Program Definition prod_sup (X:cl_eset CL (prod_preord (ord A) (ord B))) : A*B :=
      (sup_op (image π₁ X), sup_op (image π₂ X)).

    Program Definition prod_mixin : mixin_of CL (prod_preord (ord A) (ord B)) :=
      Mixin CL _ prod_sup _ _.
    Next Obligation.
      repeat intro. destruct x as [a b].
      unfold prod_sup. split; simpl.
      apply sup_is_ub. apply image_axiom1'.
      exists (a,b); auto.
      apply sup_is_ub. apply image_axiom1'.
      exists (a,b); auto.
    Qed.
    Next Obligation.
      repeat intro. destruct ub as [ua ub].
      unfold prod_sup; split; simpl;
        apply sup_is_least; repeat intro.
      apply image_axiom2 in H0.
      destruct H0 as [y [??]].
      rewrite H1.
      assert (y ≤ (ua,ub)).
      apply H; auto. destruct H2; auto.
      apply image_axiom2 in H0.
      destruct H0 as [y [??]].
      rewrite H1.
      assert (y ≤ (ua,ub)).
      apply H; auto. destruct H2; auto.
    Qed.     

    Definition prod_cpo :=
      Pack CL (A*B) (Preord.mixin (prod_preord (ord A) (ord B))) prod_mixin.

    Program Definition pi1 : prod_cpo → A :=
      Hom CL prod_cpo A (fun x => fst x) _ _.
    Next Obligation.
      intros. destruct H; auto.
    Qed.
    Next Obligation.
      simpl; intros.
      apply sup_is_least; repeat intro.
      apply sup_is_ub.
      apply image_axiom2 in H. destruct H as [y [??]].
      apply image_axiom1'. exists y. split; auto.
    Qed.    
    
    Program Definition pi2 : prod_cpo → B :=
      Hom CL prod_cpo B (fun x => snd x) _ _.
    Next Obligation.
      intros. destruct H; auto.
    Qed.
    Next Obligation.
      simpl; intros.
      apply sup_is_least; repeat intro.
      apply sup_is_ub.
      apply image_axiom2 in H. destruct H as [y [??]].
      apply image_axiom1'. exists y. split; auto.
    Qed.    
  End prod.

  Program Definition pair CL (C A B:type CL) (f:C → A) (g:C → B) : C → prod_cpo CL A B :=
    Hom CL C (prod_cpo CL A B) (fun x => (f x, g x)) _ _.
  Next Obligation.
    repeat intro. split; simpl; apply mono; auto.
  Qed.
  Next Obligation.
    repeat intro. split; simpl.
    rewrite axiom'.
    apply sup_is_least; repeat intro.
    apply sup_is_ub.
    apply image_axiom2 in H. destruct H as [y [??]].
    apply image_axiom1'. simpl in H0.
    exists (f y, g y). split; auto.
    apply image_axiom1'. exists y. split; auto.
    rewrite axiom'.
    apply sup_is_least; repeat intro.
    apply sup_is_ub.
    apply image_axiom2 in H. destruct H as [y [??]].
    apply image_axiom1'. simpl in H0.
    exists (f y, g y). split; auto.
    apply image_axiom1'. exists y. split; auto.
  Qed.

End CPO.

Notation cpo  := (CPO.type (directed_hf_cl false)).
Notation cppo := (CPO.type (directed_hf_cl true)).

Notation CPO := CPO.CPO.

Notation dirset := (cl_eset (directed_hf_cl _)).

Canonical Structure CPO.
Canonical Structure CPO.concrete.
Canonical Structure CPO.ord.
Canonical Structure CPO.ord_hom.
Canonical Structure CPO.comp.
Canonical Structure CPO.hom_ord.
Canonical Structure CPO.hom_cpo.
Canonical Structure hom_eq CL X Y:=
  Eq.Pack (CPO.hom CL X Y) (Preord.ord_eq (CPO.hom_ord CL X Y)).
Coercion CPO.ord : CPO.type >-> preord.
Coercion CPO.ord_hom : CPO.hom >-> Preord.hom.

Notation "∐ XS" := (@CPO.sup_op _ _ XS) (at level 10).

Hint Resolve CPO.sup_is_lub.

Arguments CPO.axiom [CL A B] f X.
Arguments CPO.mono [CL A B] h a b _.

Lemma sup_monotone : forall CL (A:CPO.type CL) (X X':cl_eset CL A),
  X ⊆ X' -> ∐X ≤ ∐X'.
Proof.
  intros. apply CPO.sup_is_least. repeat intro.
  apply CPO.sup_is_ub. auto.
Qed.  

Lemma sup_equiv : forall CL (A:CPO.type CL) (X X':cl_eset CL A),
  X ≈ X' -> ∐X ≈ ∐X'.
Proof.
  intros. destruct H; split; apply sup_monotone; auto.
Qed.

Section bottom.
  Variables X Y:cppo.
  
  Lemma empty_semidirected : color_prop (directed_hf_cl true) (∅:eset X).
  Proof.
    hnf; simpl; intros.
    destruct Hinh. apply H in H0.
    apply empty_elem in H0. elim H0.
  Qed.

  Definition empty_dir : dirset X := exist _ ∅ empty_semidirected.

  Definition bot : X := ∐ empty_dir.

  Lemma bot_least : forall x, bot ≤ x.
  Proof.
    intros. unfold bot.
    apply CPO.sup_is_least.
    repeat intro.
    red in H; simpl in H.
    apply empty_elem in H. elim H.
  Qed.
End bottom.

Notation "⊥" := (bot _).

Lemma strict_map (X Y:cppo) (f:X → Y) : f ⊥ ≈ ⊥.
Proof.
  unfold bot.
  rewrite (CPO.axiom f (empty_dir X)).
  apply sup_equiv.
  split; intros a H.
  apply image_axiom2 in H.
  destruct H as [?[??]].
  red in H; simpl in H.
  apply empty_elem in H. elim H.
  red in H; simpl in H.
  apply empty_elem in H. elim H.
Qed.    
Arguments strict_map [X Y] f.

Require Import NArith.

Lemma Niter_succ A f (a:A) : forall n,
  N.iter (N.succ n) f a = f (N.iter n f a).
Proof.
  induction n using N.peano_ind; simpl; auto.
  rewrite N2Nat.inj_iter.
  rewrite N2Nat.inj_succ.
  simpl. f_equal.
  rewrite <- N2Nat.inj_iter.
  auto.
Qed.

Section lfp.
  Variable X:cppo.
  Variable f:X → X.
  
  Definition iter_set : eset X :=
    fun q => Some (N.iter q f ⊥).

  Lemma iter_le : forall n1 n2,
    (n1 <= n2)%N -> N.iter n1 f ⊥ ≤ N.iter n2 f ⊥.
  Proof.
    induction n1 using N.peano_ind; simpl; intros.
    apply bot_least.
    induction n2 using N.peano_ind; simpl.
    elim H. destruct n1; simpl; auto.
    repeat rewrite Niter_succ.
    apply CPO.mono.
    apply IHn1.
    apply N.succ_le_mono; auto.
  Qed.    

  Lemma iter_set_directed : color_prop (directed_hf_cl true) iter_set.
  Proof.
    red. simpl. apply prove_directed; auto.
    simpl; intros.
    destruct H as [n1 ?].
    destruct H0 as [n2 ?].
    simpl in H. simpl in H0.
    destruct (N.lt_ge_cases n1 n2).
    exists y.
    split.
    rewrite H. rewrite H0.
    apply iter_le.
    hnf in H1. hnf.
    rewrite H1. discriminate.
    split; auto. exists n2. auto.
    exists x.
    split. auto.
    split.
    rewrite H. rewrite H0.
    apply iter_le; auto.
    exists n1. auto.
  Qed.

  Definition iter_dirset : dirset X := 
    exist _ iter_set iter_set_directed.

  Definition lfp : X := ∐iter_dirset.

  Lemma scott_induction (P:X -> Prop) :
    (forall XS:dirset X, (forall x, x ∈ XS -> P x) -> P (∐XS)) ->
    (forall x y, x ≈ y -> P x -> P y) ->
    (forall x, P x -> P (f x)) ->
    P lfp.
  Proof.
    intros. unfold lfp.
    apply H. intros.
    destruct H2 as [n ?]. simpl in *.
    symmetry in H2. apply (H0 _ _ H2). clear x H2.
    induction n using N.peano_ind; simpl; auto.
    unfold bot.
    apply H. intros. red in H2; simpl in H2.
    apply empty_elem in H2. elim H2.
    rewrite Niter_succ.
    apply H1. auto.
  Qed.

  Lemma lfp_fixpoint : f lfp ≈ lfp.
  Proof.
    apply scott_induction.
    intros. rewrite (CPO.axiom f XS).
    apply sup_equiv.
    split; intros ??.
    apply image_axiom2 in H0.
    destruct H0 as [y [??]].
    rewrite H1.
    rewrite H; auto.
    rewrite <- H; auto.
    apply image_axiom1; auto.
    intros.
    rewrite <- H; auto.
    intros. rewrite H at 1. auto.
  Qed.

  Lemma lfp_least : forall x, f x ≈ x -> lfp ≤ x.
  Proof.
    apply scott_induction; intros.
    apply CPO.sup_is_least. repeat intro.
    apply H; auto.
    rewrite <- H. apply H0; auto.
    rewrite <- H0.
    apply CPO.mono. apply H; auto.
  Qed.

End lfp.

Arguments lfp [X] f.
Arguments scott_induction [X] f P _ _ _.

Lemma lfp_uniform (D E:cppo) (f:D → E) (d:D → D) (e:E → E) :
  e ∘ f ≈ f ∘ d ->
  lfp e ≈ f (lfp d).
Proof.
  intros. split.

  apply (scott_induction e); intros.
  apply CPO.sup_is_least. repeat intro; auto.
  rewrite <- H0; auto.
  rewrite H0.
  rewrite <- (lfp_fixpoint D d) at 2.
  destruct H. apply H.

  apply (scott_induction d); intros.
  rewrite (CPO.axiom f XS).
  apply CPO.sup_is_least. repeat intro.
  apply image_axiom2 in H1. destruct H1 as [y [??]].
  apply H0 in H1.
  rewrite H2. auto.
  rewrite <- H0; auto.
  rewrite <- (lfp_fixpoint E e).
  rewrite <- H0.
  destruct H. apply H1.
Qed.
