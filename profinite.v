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
Require Import cpo.

Module PLT.
Section PLT.
  Variable hf:bool.

  Record class_of (A:Type) :=
    Class
    { cls_preord : Preord.mixin_of A
    ; cls_ord := Preord.Pack A cls_preord
    ; cls_effective : effective_order cls_ord
    ; cls_plotkin : plotkin_order hf cls_ord
    }.

  Record ob := Ob { carrier :> Type; class : class_of carrier }.

  Definition effective (X:ob) := cls_effective _ (class X).
  Definition plotkin (X:ob)   := cls_plotkin _ (class X).
  Definition ord (X:ob)       := cls_ord _ (class X).

  Canonical Structure ord.
  Canonical Structure dec (X:ob) := eff_to_ord_dec (ord X) (effective X).
  
  Record hom (A B:ob) :=
    Hom
    { hom_rel :> erel (ord A) (ord B)
    ; hom_order : forall x x' y y', x ≤ x' -> y' ≤ y ->
         (x,y) ∈ hom_rel -> (x',y') ∈ hom_rel
    ; hom_directed : directed_rel hf (ord A) (ord B) (effective A) hom_rel
    }.
  Arguments hom_rel [A] [B] h n.

  Program Definition hom_ord_mixin (A B:ob) : Preord.mixin_of (hom A B) :=
    Preord.Mixin (hom A B) (fun f g => hom_rel f ≤ hom_rel g) _ _.
  Solve Obligations of hom_ord_mixin using (intros; eauto).
  
  Canonical Structure hom_ord (A B:ob) := Preord.Pack (hom A B) (hom_ord_mixin A B).

  Definition hom_eq_mixin (A B:ob) := Preord.ord_eq (hom_ord A B).
  Canonical Structure hom_eq (A B:ob) := Eq.Pack (hom A B) (hom_eq_mixin A B).

  Definition ident (A:ob) : hom A A :=
    Hom A A 
       (ident_rel (effective A))
       (ident_ordering (ord A) (effective A))
       (ident_image_dir hf (ord A) (effective A)).

  Program Definition compose (A B C:ob) (g:hom B C) (f:hom A B) : hom A C :=
    Hom A C (compose_rel (effective B) g f) _ _.
  Next Obligation.
    intros A B C g f. 
    apply compose_ordering. apply hom_order. apply hom_order.
  Qed.
  Next Obligation.
    intros A B C g f. apply compose_directed. 
    apply hom_order. apply hom_order.
    apply hom_directed. apply hom_directed.
  Qed.

  Definition comp_mixin : Comp.mixin_of ob hom
    := Comp.Mixin ob hom ident compose.
  Canonical Structure comp : Comp.type := Comp.Pack ob hom comp_mixin.

  Lemma compose_mono (X Y Z:ob) (f f':hom X Y) (g g':hom Y Z) :
    f ≤ f' -> g ≤ g' -> g ∘ f ≤ g' ∘ f'.
  Proof.
    repeat intro; simpl in *.
    destruct a as [x z].
    apply compose_elem in H1.
    apply compose_elem.
    apply hom_order.
    destruct H1 as [y [??]].
    exists y. split.
    apply H; auto.
    apply H0; auto.
    apply hom_order.
  Qed.

  Lemma cat_axioms : Category.axioms ob hom hom_eq_mixin comp_mixin.
  Proof.
    constructor.

    intros. apply compose_ident_rel2. apply hom_order.
    intros. apply compose_ident_rel1. apply hom_order.
    intros. apply compose_assoc.
    intros. split; apply compose_mono; auto.
  Qed.

  Program Definition empty : ob :=
    Ob False
      (Class _
        (Preord.mixin emptypo)
        effective_empty
        (empty_plotkin hf)).
   
  Program Definition unit : ob :=
    Ob unit
      (Class _
        (Preord.mixin unitpo)
        effective_unit
        (unit_plotkin hf)).

  Definition prod (A B:ob) : ob :=
    Ob (carrier A * carrier B)
       (Class _ 
         (Preord.mixin (ord A × ord B))
         (effective_prod (effective A) (effective B))
         (plotkin_prod hf (ord A) (ord B) (effective A) (effective B) (plotkin A) (plotkin B))).
  Canonical Structure prod.
  
  Definition sum (A B:ob) : ob :=
    Ob (sum_preord (ord A) (ord B))
       (Class _
         (Preord.mixin (sum_preord (ord A) (ord B)))
         (effective_sum (effective A) (effective B))
         (plotkin_sum hf (ord A) (ord B) (effective A) (effective B)
             (plotkin A) (plotkin B))
         ).
  Canonical Structure sum.

  Definition exp (A B:ob) : ob :=
    Ob (joinable_relation hf (ord A) (ord B))
       (Class _
         (joinable_rel_ord_mixin hf (ord A) (ord B))
         (joinable_rel_effective hf (ord A) (ord B) (effective A) (effective B) (plotkin A))
         (joinable_rel_plt hf (ord A) (ord B) (effective A) (plotkin A) (effective B) (plotkin B))).
  Canonical Structure exp.

  Program Definition initiate A : hom empty A :=
    Hom empty A (esets.empty (prod_preord (ord empty) (ord A))) _ _.
  Next Obligation.
    intros. apply empty_elem in H1. elim H1.
  Qed.
  Next Obligation.
    intros A x. elim x.
  Qed.

  Program Definition terminate A : hom A unit :=
    Hom A unit (eprod (eff_enum _ (effective A)) (eff_enum _ (effective unit))) _ _.
  Next Obligation.
    intros.
    apply eprod_elem. split; apply eff_complete.
  Qed.
  Next Obligation.    
    intros A x. repeat intro.
    exists tt. split.
    hnf; simpl; intros. hnf; auto.
    apply erel_image_elem.
    apply eprod_elem; split; apply eff_complete.
  Qed.

  Definition iota1 A B : hom A (sum A B) :=
    Hom A (sum A B)
      (iota1_rel (ord A) (ord B) (effective A))
      (iota1_ordering (ord A) (ord B) (effective A))
      (iota1_dir (ord A) (ord B) (effective A) hf).

  Definition iota2 A B : hom B (sum A B) :=
    Hom B (sum A B)
      (iota2_rel (ord A) (ord B) (effective B))
      (iota2_ordering (ord A) (ord B) (effective B))
      (iota2_dir (ord A) (ord B) (effective B) hf).
  
  Definition sum_cases {C A B} (f:hom A C) (g:hom B C) : hom (sum A B) C :=
    Hom (sum A B) C
      (sum_cases (ord C) (ord A) (ord B) f g)
      (sum_cases_ordering (ord C) (ord A) (ord B) f g
           (hom_order _ _ f) (hom_order _ _ g))
      (sum_cases_dir (ord C) (ord A) (ord B)
          (effective A) (effective B) hf f g
          (hom_directed _ _ f) (hom_directed _ _ g)).

  Definition app {A B} : hom (prod (exp A B) A) B :=
    Hom (prod (exp A B) A) B
      (apply_rel hf (ord A) (ord B) (effective A) (effective B) (plotkin A))
      (apply_rel_ordering hf (ord A) (ord B) (effective A) (effective B) (plotkin A))
      (apply_rel_dir hf (ord A) (ord B) (effective A) (effective B) (plotkin A)).
 
  Definition curry {C A B} (f:hom (prod C A) B) : hom C (exp A B) :=
    Hom C (exp A B)
      (curry_rel hf (ord A) (ord B) (ord C)
        (effective A) (effective B) (effective C) (plotkin A) 
        f (hom_order _ _ f))
      (curry_rel_ordering hf (ord A) (ord B) (ord C)
        (effective A) (effective B) (effective C) (plotkin A) 
        f (hom_order _ _ f))
      (curry_rel_dir hf (ord A) (ord B) (ord C)
        (effective A) (effective B) (effective C) (plotkin A) 
        f (hom_order _ _ f) (hom_directed _ _ f)
        (plotkin B)).

  Definition pair {C A B} (f:hom C A) (g:hom C B) : hom C (prod A B) :=
    Hom C (prod A B) 
      (pair_rel (effective C) f g)
      (pair_rel_ordering _ _ _ (effective C) f g (hom_order _ _ f) (hom_order _ _ g))
      (pair_rel_dir _ _ _ _ (effective C) f g 
        (hom_order _ _ f) (hom_order _ _ g)
        (hom_directed _ _ f) (hom_directed _ _ g)).

  Definition pi1 {A B} : hom (prod A B) A :=
    Hom (prod A B) A 
      (pi1_rel (effective A) (effective B))
      (pi1_rel_ordering _ _ (effective A) (effective B))
      (pi1_rel_dir _ _ _ (effective A) (effective B)).

  Definition pi2 {A B} : hom (prod A B) B :=
    Hom (prod A B) B 
      (pi2_rel (effective A) (effective B))
      (pi2_rel_ordering _ _ (effective A) (effective B))
      (pi2_rel_dir _ _ _ (effective A) (effective B)).

  Definition pair_map {A B C D} (f:hom A C) (g:hom B D) : hom (prod A B) (prod C D) :=
    pair (f ∘ pi1) (g ∘ pi2).

  Program Definition pair_map' {A B C D} (f:hom A C) (g:hom B D) : hom (prod A B) (prod C D) :=
    Hom (prod A B) (prod C D) (pair_rel' f g) _ _.
  Next Obligation.
    intros A B C D f g.
    apply pair_rel_order'; auto.
    apply hom_order.
    apply hom_order.
  Qed.    
  Next Obligation.
(* FIXME, move this proof into approx_rels.v *)

    repeat intro.
    destruct (hom_directed _ _ f (fst x) (image π₁ M)).
    apply inh_image; auto.
    red; intros. apply image_axiom2 in H0. destruct H0 as [y[??]].
    apply erel_image_elem.
    apply H in H0.
    apply erel_image_elem in H0.
    destruct x; destruct y.
    apply (pair_rel_elem' _ _ _ _ f g) in H0.
    simpl. destruct H0.
    apply member_eq with (c,c1); auto.
    simpl in H1.
    destruct H1; split; split; auto.
    apply hom_order.
    apply hom_order.
    destruct (hom_directed _ _ g (snd x) (image π₂ M)).
    apply inh_image; auto.
    red; intros. apply image_axiom2 in H1. destruct H1 as [y[??]].
    apply erel_image_elem.
    apply H in H1.
    apply erel_image_elem in H1.
    destruct x; destruct y.
    apply (pair_rel_elem' _ _ _ _ f g) in H1.
    simpl. destruct H1.
    apply member_eq with (c0,c2); auto.
    simpl in H2.
    destruct H2; split; split; auto.
    apply hom_order.
    apply hom_order.
    exists (x0,x1).
    destruct H0. destruct H1.
    split.
    red; intros.
    split.
    apply H0. apply image_axiom1'.
    exists x2. split; auto.
    apply H1. apply image_axiom1'.
    exists x2. split; auto.
    apply erel_image_elem.
    apply erel_image_elem in H2.
    apply erel_image_elem in H3.
    destruct x.
    apply (pair_rel_elem' _ _ _ _ f g).
    apply hom_order. apply hom_order.
    split; auto.
  Qed.

  Lemma pair_map_eq {A B C D} (f:hom A C) (g:hom B D) :
    pair_map f g ≈ pair_map' f g.
  Proof.
    red. simpl. symmetry.
    apply pair_rel_eq.
    apply hom_order.
    apply hom_order.
  Qed.

  Canonical Structure PLT : category := Category ob hom hom_eq_mixin comp_mixin cat_axioms.

  Theorem initiate_univ A (f:hom empty A) :
    f ≈ initiate A.
  Proof.
    split; hnf; intros.
    destruct a. elim c.
    destruct a. elim c.
  Qed.

  Theorem terminate_le_univ A (f:hom A unit) :
    f ≤ terminate A.
  Proof.
    hnf; intros.
    red. simpl.
    destruct a.
    apply eprod_elem. split. apply eff_complete.
    apply single_axiom. destruct c0. auto.
  Qed.

  Theorem iota1_cases_commute C A B (f:hom A C) (g:hom B C) :
    sum_cases f g ∘ iota1 A B ≈ f.
  Proof.
    apply iota1_cases_commute.
    apply (hom_order _ _ f).
  Qed.

  Theorem iota2_cases_commute C A B (f:hom A C) (g:hom B C) :
    sum_cases f g ∘ iota2 A B ≈ g.
  Proof.
    apply iota2_cases_commute.
    apply (hom_order _ _ g).
  Qed.

  Theorem sum_cases_universal C A B (f:hom A C) (g:hom B C) (CASES:hom (sum A B) C) :
    CASES ∘ iota1 A B ≈ f -> CASES ∘ iota2 A B ≈ g -> CASES ≈ sum_cases f g.
  Proof.
    intros. symmetry.
    apply (sum_cases_univ _ _ _ (effective A) (effective B) f g); auto.
    apply (hom_order _ _ CASES).
  Qed.

  Theorem pair_universal C A B (f:hom C A) (g:hom C B) (PAIR:hom C (prod A B)) :
    pi1 ∘ PAIR ≈ f -> pi2 ∘ PAIR ≈ g -> PAIR ≈ pair f g.
  Proof.
    apply (pair_rel_universal hf).
    apply hom_order.
    apply hom_order.
    apply hom_order.
    apply hom_directed.
  Qed.

  Theorem pair_universal_le C A B (f:hom C A) (g:hom C B) (PAIR:hom C (prod A B)) :
    pi1 ∘ PAIR ≤ f -> pi2 ∘ PAIR ≤ g -> PAIR ≤ pair f g.
  Proof.
    apply pair_rel_universal_le.
    apply hom_order.
    apply hom_order.
    apply hom_order.
  Qed.

  Theorem curry_apply A B C (f:hom (prod C A) B) :
    app ∘ pair_map (curry f) id ≈ f.
  Proof.
    rewrite pair_map_eq.
    apply curry_apply. 
    apply hom_directed. 
    apply plotkin.
  Qed. 

  Theorem curry_universal A B C (f:hom (prod C A) B) (CURRY:hom C (exp A B)) :
    app ∘ pair_map CURRY id ≈ f -> CURRY ≈ curry f.
  Proof.
    intro. apply (curry_universal hf); auto.
    apply (hom_directed _ _ f).
    apply plotkin.
    apply (hom_order _ _ CURRY).
    apply (hom_directed _ _ CURRY).
    rewrite pair_map_eq in H. apply H.
  Qed.

  Definition initialized_mixin :=
    Initialized.Mixin ob hom hom_eq_mixin empty initiate initiate_univ.

  Program Definition cocartesian_mixin :=
    Cocartesian.Mixin ob hom hom_eq_mixin comp_mixin sum iota1 iota2 (@sum_cases) _.
  Next Obligation.
    constructor.
    apply iota1_cases_commute.
    apply iota2_cases_commute.
    apply sum_cases_universal.
  Qed.

  Definition cocartesian :=
    Cocartesian ob hom hom_eq_mixin comp_mixin cat_axioms initialized_mixin cocartesian_mixin.

  Section homset_cpo.
    Variables A B:ob.

    Program Definition hom_rel' : hom_ord A B → erel (ord A) (ord B) :=
      Preord.Hom (hom_ord A B) (erel (ord A) (ord B)) (@hom_rel A B) _.
    Next Obligation. simpl. auto. Qed.

    Program Definition homset_sup (M:cl_eset (directed_hf_cl hf) (hom_ord A B)) 
      : hom A B := Hom A B (∪(image hom_rel' M)) _ _.
    Next Obligation.
      intros. apply union_axiom in H1. apply union_axiom.
      destruct H1 as [X [??]].
      exists X. split; auto.
      apply image_axiom2 in H1.
      destruct H1 as [Y [??]].
      rewrite H3. simpl.
      apply hom_order with x y; auto.
      rewrite H3 in H2. auto.
    Qed.
    Next Obligation.
      intros. red. intro x.
      apply prove_directed.
      generalize (refl_equal hf).
      pattern hf at 2. case hf; intros.
      pattern hf at 1. rewrite H; auto.
      pattern hf at 1. rewrite H; auto.
      destruct M as [M HM]; simpl in *.
      destruct (HM nil) as [q [??]].
      rewrite H. hnf; auto.
      hnf; intros. apply nil_elem in H0. elim H0.
      destruct (hom_directed A B q x nil) as [z [??]].
      rewrite H. hnf. auto.
      hnf; intros. apply nil_elem in H2. elim H2.
      apply erel_image_elem in H3.
      exists z. apply erel_image_elem.
      apply union_axiom.
      exists (hom_rel q). split; auto.
      apply image_axiom1'; eauto.
      exists q. split; auto.
      
      intros y1 y2. intros.
      apply erel_image_elem in H.
      apply erel_image_elem in H0.
      apply union_axiom in H.      
      apply union_axiom in H0.
      destruct H as [X1 [??]].
      destruct H0 as [X2 [??]].
      apply image_axiom2 in H.
      destruct H as [Y1 [??]].
      apply image_axiom2 in H0.
      destruct H0 as [Y2 [??]].
      destruct M as [M HM]; simpl in *.
      destruct (HM (Y1::Y2::nil)%list) as [Y [??]].
      apply elem_inh with Y1. apply cons_elem; auto.
      hnf; intros.
      apply cons_elem in H5.
      destruct H5. rewrite H5; auto.
      apply cons_elem in H5.
      destruct H5. rewrite H5; auto.
      apply nil_elem in H5. elim H5.
      destruct (hom_directed A B Y x (y1::y2::nil)%list) as [z [??]].
      apply elem_inh with y1; auto. apply cons_elem; auto.
      hnf; intros.
      apply cons_elem in H7. destruct H7.
      rewrite H7. apply erel_image_elem.
      assert (Y1 ≤ Y). apply H5. apply cons_elem. auto.
      apply H8. rewrite <- H3. auto.
      assert (Y2 ≤ Y). apply H5. apply cons_elem. right.
      apply cons_elem. auto.
      apply cons_elem in H7. destruct H7.
      rewrite H7. apply erel_image_elem.
      apply H8. rewrite <- H4. auto.
      apply nil_elem in H7. elim H7.
      apply erel_image_elem in H8.
      exists z.
      split.
      apply H7. apply cons_elem; auto.
      split.
      apply H7. apply cons_elem; right. apply cons_elem; auto.
      apply erel_image_elem.
      apply union_axiom.
      exists (hom_rel Y). split; auto.
      apply image_axiom1'. exists Y; split; auto.
    Qed.

    Program Definition homset_cpo_mixin : 
      CPO.mixin_of (directed_hf_cl hf) (hom_ord A B)
      := CPO.Mixin _ _ homset_sup _ _.
    Next Obligation.
      repeat intro; simpl.
      apply union_axiom.
      exists (hom_rel x). split; auto.
      apply image_axiom1'. exists x. split; auto.
    Qed.
    Next Obligation.
      repeat intro.
      simpl in H0.
      apply union_axiom in H0.
      destruct H0 as [Q [??]].
      apply image_axiom2 in H0.
      destruct H0 as [y [??]].
      generalize (H y H0); intros.
      apply H3.
      rewrite H2 in H1. auto.
    Qed.

    Definition homset_cpo : CPO.type (directed_hf_cl hf) :=
      CPO.Pack _ (hom A B) (hom_ord_mixin A B) homset_cpo_mixin.
  End homset_cpo.
End PLT.
End PLT.

Notation PLT := PLT.PLT.
Canonical Structure PLT.
Canonical Structure PLT.ord.
Canonical Structure PLT.dec.
Canonical Structure PLT.hom_ord.
Canonical Structure PLT.hom_eq.
Canonical Structure PLT.comp.
Canonical Structure PLT.prod.
Canonical Structure PLT.homset_cpo.
Canonical Structure PLT.cocartesian.

Arguments PLT.hom [hf] A B.
Arguments PLT.hom_rel [hf] [A] [B] h n.
Arguments PLT.effective [hf] X.
Arguments PLT.plotkin [hf] X.
Arguments PLT.ord [hf] X.
Arguments PLT.dec [hf] X.
Arguments PLT.pi1 [hf] [A] [B].
Arguments PLT.pi2 [hf] [A] [B].
Arguments PLT.pair [hf] [C] [A] [B] f g.
Arguments PLT.iota1 [hf] [A] [B].
Arguments PLT.iota1 [hf] [A] [B].
Arguments PLT.sum_cases [hf] [C] [A] [B] f g.
Arguments PLT.prod [hf] A B.
Arguments PLT.exp [hf] A B.
Arguments PLT.app [hf] A B.
Arguments PLT.curry [hf] C A B f.

Coercion PLT.ord : PLT.ob >-> preord.
Coercion PLT.carrier : PLT.ob >-> Sortclass.

Notation TPLT := (PLT false).
Notation PPLT := (PLT true).

Module TPLT.
  Theorem pair_commute1 (C A B:ob TPLT) (f:C → A) (g:C → B) :
    PLT.pi1 ∘ PLT.pair f g ≈ f.
  Proof.
    apply pair_proj_commute1.
    apply PLT.hom_order.
    apply PLT.hom_order.
    apply PLT.hom_directed.
  Qed.

  Theorem pair_commute2 (C A B:ob TPLT) (f:C → A) (g:C → B) :
    PLT.pi2 ∘ PLT.pair f g ≈ g.
  Proof.
    apply pair_proj_commute2.
    apply PLT.hom_order.
    apply PLT.hom_order.
    apply PLT.hom_directed.
  Qed.
End TPLT.

Module PPLT.
  Theorem pair_commute1 (C A B:ob PPLT) (f:C → A) (g:C → B) :
    PLT.pi1 ∘ PLT.pair f g ≤ f.
  Proof.
    apply pair_proj_commute1_le.
    apply PLT.hom_order.
    apply PLT.hom_order.
  Qed.

  Theorem pair_commute2 (C A B:ob TPLT) (f:C → A) (g:C → B) :
    PLT.pi2 ∘ PLT.pair f g ≤ g.
  Proof.
    apply pair_proj_commute2_le.
    apply PLT.hom_order.
    apply PLT.hom_order.
  Qed.
End PPLT.

