(* Copyright (c) 2014, Robert Dockins *)

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

Delimit Scope plt_scope with plt.
Open Scope plt_scope.

(**  * Categories of profinite domains, expressed as Plotkin orders

     Here we define both the category PLT of effective Plotkin orders,
     and the category ∂PLT of partial Plotkin orders.  PLT is 
     is equivalant to the category of profinite domains via
     ideal completion, and ∂PLT is equivalant to the category of
     pointed profinite domains with strict continuous functions.

     The objects of PLT are the effective Plotkin orders, and the
     arrows are approximable relations.  The objects and characteristic
     operations are provided for the unit, empty, product, sum and
     function space.

     PLT is DCPO-enriched, which means that each homset is equipped
     with a DCPO.  In addition the composition operation is
     continuous in both arguments.
  *)

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

  Canonical Structure PLT : category :=
    Category ob hom hom_eq_mixin comp_mixin cat_axioms.

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

  Program Definition initiate A : empty → A :=
    Hom empty A (esets.empty (prod_preord (ord empty) (ord A))) _ _.
  Next Obligation.
    intros. apply empty_elem in H1. elim H1.
  Qed.
  Next Obligation.
    intros A x. elim x.
  Qed.

  Program Definition terminate A : A → unit :=
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

  Definition iota1 A B : A → (sum A B) :=
    Hom A (sum A B)
      (iota1_rel (ord A) (ord B) (effective A))
      (iota1_ordering (ord A) (ord B) (effective A))
      (iota1_dir (ord A) (ord B) (effective A) hf).

  Definition iota2 A B : B → (sum A B) :=
    Hom B (sum A B)
      (iota2_rel (ord A) (ord B) (effective B))
      (iota2_ordering (ord A) (ord B) (effective B))
      (iota2_dir (ord A) (ord B) (effective B) hf).
  
  Definition sum_cases {C A B} (f:A → C) (g:B → C) : (sum A B) → C :=
    Hom (sum A B) C
      (sum_cases (ord C) (ord A) (ord B) f g)
      (sum_cases_ordering (ord C) (ord A) (ord B) f g
           (hom_order _ _ f) (hom_order _ _ g))
      (sum_cases_dir (ord C) (ord A) (ord B)
          (effective A) (effective B) hf f g
          (hom_directed _ _ f) (hom_directed _ _ g)).

  Definition app {A B} : (prod (exp A B) A) → B :=
    Hom (prod (exp A B) A) B
      (apply_rel hf (ord A) (ord B) (effective A) (effective B) (plotkin A))
      (apply_rel_ordering hf (ord A) (ord B) (effective A) (effective B) (plotkin A))
      (apply_rel_dir hf (ord A) (ord B) (effective A) (effective B) (plotkin A)).
 
  Definition curry {C A B} (f:(prod C A) → B) : C → (exp A B) :=
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

  Definition pair {C A B} (f:C → A) (g:C → B) : C → (prod A B) :=
    Hom C (prod A B) 
      (pair_rel (effective C) f g)
      (pair_rel_ordering _ _ _ (effective C) f g (hom_order _ _ f) (hom_order _ _ g))
      (pair_rel_dir _ _ _ _ (effective C) f g 
        (hom_order _ _ f) (hom_order _ _ g)
        (hom_directed _ _ f) (hom_directed _ _ g)).

  Definition pi1 {A B} : (prod A B) → A :=
    Hom (prod A B) A 
      (pi1_rel (effective A) (effective B))
      (pi1_rel_ordering _ _ (effective A) (effective B))
      (pi1_rel_dir _ _ _ (effective A) (effective B)).

  Definition pi2 {A B} : (prod A B) → B :=
    Hom (prod A B) B 
      (pi2_rel (effective A) (effective B))
      (pi2_rel_ordering _ _ (effective A) (effective B))
      (pi2_rel_dir _ _ _ (effective A) (effective B)).

  Definition pair_map {A B C D} (f:A → C) (g:B → D) : (prod A B) → (prod C D) :=
    pair (f ∘ pi1) (g ∘ pi2).

  Program Definition pair_map' {A B C D} (f:A → C) (g:B → D) : (prod A B) → (prod C D) :=
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

  Lemma pair_map_eq {A B C D} (f:A → C) (g:B → D) :
    pair_map f g ≈ pair_map' f g.
  Proof.
    red. simpl. symmetry.
    apply pair_rel_eq.
    apply hom_order.
    apply hom_order.
  Qed.

  Theorem initiate_univ A (f:empty → A) :
    f ≈ initiate A.
  Proof.
    split; hnf; intros.
    destruct a. elim c.
    destruct a. elim c.
  Qed.

  Theorem terminate_le_univ A (f:A → unit) :
    f ≤ terminate A.
  Proof.
    hnf; intros.
    red. simpl.
    destruct a.
    apply eprod_elem. split. apply eff_complete.
    apply single_axiom. destruct c0. auto.
  Qed.

  Theorem iota1_cases_commute C A B (f:A → C) (g:B → C) :
    sum_cases f g ∘ iota1 A B ≈ f.
  Proof.
    apply iota1_cases_commute.
    apply (hom_order _ _ f).
  Qed.

  Theorem iota2_cases_commute C A B (f:A → C) (g:B → C) :
    sum_cases f g ∘ iota2 A B ≈ g.
  Proof.
    apply iota2_cases_commute.
    apply (hom_order _ _ g).
  Qed.

  Theorem sum_cases_universal C A B (f:A → C) (g:B → C) (CASES:(sum A B) → C) :
    CASES ∘ iota1 A B ≈ f -> CASES ∘ iota2 A B ≈ g -> CASES ≈ sum_cases f g.
  Proof.
    intros. symmetry.
    apply (sum_cases_univ _ _ _ (effective A) (effective B) f g); auto.
    apply (hom_order _ _ CASES).
  Qed.

  Theorem pair_universal C A B (f:C → A) (g:C → B) (PAIR:C → (prod A B)) :
    pi1 ∘ PAIR ≈ f -> pi2 ∘ PAIR ≈ g -> PAIR ≈ pair f g.
  Proof.
    apply (pair_rel_universal hf).
    apply hom_order.
    apply hom_order.
    apply hom_order.
    apply hom_directed.
  Qed.

  Theorem pair_universal_le C A B (f:C → A) (g:C → B) (PAIR:C → (prod A B)) :
    pi1 ∘ PAIR ≤ f -> pi2 ∘ PAIR ≤ g -> PAIR ≤ pair f g.
  Proof.
    apply pair_rel_universal_le.
    apply hom_order.
    apply hom_order.
    apply hom_order.
  Qed.

  Theorem pair_le_commute1 C A B (f:C → A) (g:C → B) :
    pi1 ∘ pair f g ≤ f.
  Proof.
    apply pair_proj_commute1_le.
    apply PLT.hom_order.
    apply PLT.hom_order.
  Qed.

  Theorem pair_le_commute2 C A B (f:C → A) (g:C → B) :
    pi2 ∘ pair f g ≤ g.
  Proof.
    apply pair_proj_commute2_le.
    apply PLT.hom_order.
    apply PLT.hom_order.
  Qed.

  Theorem pair_compose_commute A B C D
    (f:C → A) (g:C → B) (h:D → C) :
    PLT.pair f g ∘ h ≈ PLT.pair (f ∘ h) (g ∘ h).
  Proof.
    split.
    apply pair_universal_le.
    rewrite (cat_assoc _ _ _ _ _ pi1).
    apply compose_mono; auto.
    apply pair_le_commute1.
    rewrite (cat_assoc _ _ _ _ _ pi2).
    apply compose_mono; auto.
     apply pair_le_commute2.
    hnf; simpl; intros.
    destruct a as  [d [a b]].
    rewrite (pair_rel_elem _ _ _ (effective D) (compose_rel (effective C) f h) (compose_rel (effective C) g h) d a b) in H.
    destruct H.
    apply compose_elem.
    apply hom_order.
    apply compose_elem in H.
    2: apply hom_order.
    apply compose_elem in H0.
    2: apply hom_order.
    destruct H as [q1 [??]].
    destruct H0 as [q2 [??]].
    destruct (hom_directed _ _ h d (q1::q2::nil)%list).
    apply elem_inh with q1. apply cons_elem; auto.
    red; simpl; intros. apply erel_image_elem.
    apply cons_elem in H3. destruct H3.
    revert H. apply member_eq.
    split; split; auto.
    apply cons_elem in H3. destruct H3.
    revert H0. apply member_eq.
    split; split; auto.
    apply nil_elem in H3. elim H3.
    destruct H3.
    apply erel_image_elem in H4.
    exists x. split; auto.
    apply pair_rel_elem.
    split.
    revert H1. apply hom_order; auto.
    apply H3. apply cons_elem; auto.
    revert H2. apply hom_order; auto.
    apply H3. 
    apply cons_elem; right.
    apply cons_elem; auto.
  Qed.

  Theorem curry_apply A B C (f:(prod C A) → B) :
    app ∘ pair_map (curry f) id ≈ f.
  Proof.
    rewrite pair_map_eq.
    apply curry_apply.
    apply hom_directed. 
    apply plotkin.
  Qed.

  Theorem pair_mono (C A B:ob) (f f':C → A) (g g':C → B) :
    f ≤ f' -> g ≤ g' -> pair f g ≤ pair f' g'.
  Proof.
    repeat intro.
    destruct a as [c [a b]]. simpl in *.
    apply (pair_rel_elem _ _ _ _ f g) in H1.
    apply pair_rel_elem.
    destruct H1; split; auto.
  Qed.

  Theorem pair_eq (C A B:ob) (f f':C → A) (g g':C → B) :
    f ≈ f' -> g ≈ g' -> pair f g ≈ pair f' g'.
  Proof.
    intros. split; apply pair_mono; auto.
  Qed.

  Theorem sum_cases_mono (C A B:ob) (f f':A → C) (g g':B → C) :
    f ≤ f' -> g ≤ g' -> sum_cases f g ≤ sum_cases f' g'.
  Proof.
    repeat intro.
    destruct a as [z c]. simpl in *.
    apply (sum_cases_elem (ord C) (ord A) (ord B) (hom_rel f) (hom_rel g)) in H1.
    apply (sum_cases_elem (ord C) (ord A) (ord B) (hom_rel f') (hom_rel g')).
    destruct z; auto.
  Qed.

  Theorem sum_cases_eq (C A B:ob) (f f':A → C) (g g':B → C) :
    f ≈ f' -> g ≈ g' -> sum_cases f g ≈ sum_cases f' g'.
  Proof.
    intros. split; apply sum_cases_mono; auto.
  Qed.

  Theorem curry_mono (C A B:ob) (f f':prod C A → B) :
    f ≤ f' -> curry f ≤ curry f'.
  Proof.
    repeat intro. destruct a as [c R].
    simpl in H0.
    simpl. apply curry_rel_elem. intros.
    apply H.
    revert H0 a b H1.
    apply curry_rel_elem.
  Qed.

  Theorem curry_eq (C A B:ob) (f f':prod C A → B) :
    f ≈ f' -> curry f ≈ curry f'.
  Proof.
    intros; split; apply curry_mono; auto.
  Qed.

  Theorem pair_map_pair C X Y Z W (f1:C → X) (f2:X → Y) (g1:C → Z) (g2:Z → W) :
    pair (f2 ∘ f1) (g2 ∘ g1) ≈ pair_map f2 g2 ∘ pair f1 g1.
  Proof.
    split; hnf; simpl; intros.
    destruct a as [c [y w]].
    apply (pair_rel_elem (ord Y) (ord W) (ord C) (effective C)
         (compose_rel (effective X) f2 f1)
         (compose_rel (effective Z) g2 g1)) in H.
    destruct H.
    apply compose_elem.
    apply pair_rel_ordering; apply hom_order.
    simpl.
    apply compose_elem in H. 2: apply hom_order.
    apply compose_elem in H0. 2: apply hom_order.
    destruct H as [x [??]].
    destruct H0 as [z [??]].
    exists (x,z). split; auto.
    apply pair_rel_elem; split; auto.
    apply pair_rel_elem. split; auto.
    apply compose_elem. apply pi1_rel_ordering.
    exists x; split; auto.
    apply pi1_rel_elem. auto.
    apply compose_elem. apply pi2_rel_ordering.
    exists z. split; auto.
    apply pi2_rel_elem. auto.

    destruct a as [c [y w]].
    apply compose_elem in H; simpl in *.
    2: apply pair_rel_ordering; apply hom_order.
    destruct H as [[x z] [??]].
    apply pair_rel_elem in H.
    apply (pair_rel_elem _ _ _ _
           (compose_rel (effective X) f2
              (pi1_rel (effective X) (effective Z)))
           (compose_rel (effective Z) g2
              (pi2_rel (effective X) (effective Z)))) in H0.
    destruct H0.
    apply compose_elem in H0. 2: apply pi1_rel_ordering.
    apply compose_elem in H1. 2: apply pi2_rel_ordering.
    destruct H0 as [x' [??]].
    destruct H1 as [y' [??]].
    apply pair_rel_elem.
    split.
    apply compose_elem. apply hom_order.
    destruct H.
    exists x. split; auto.
    apply (hom_order _ _ f2) with x' y; auto.
    apply pi1_rel_elem in H0. auto.
    apply compose_elem. apply hom_order.
    destruct H.
    exists z. split; auto.
    apply (hom_order _ _ g2) with y' w; auto.
    apply pi2_rel_elem in H1. auto.
  Qed.

  Theorem curry_apply2 A B C (f:(prod C A) → B) (g:C → A) :
    app ∘ pair (curry f) g ≈ f ∘ pair id g.
  Proof.
    cut (pair (curry f) g ≈ pair_map (curry f) id ∘ pair id g).
    intros. rewrite H.
    rewrite (@cat_assoc PLT).
    rewrite curry_apply. auto.
    rewrite <- pair_map_pair.
    apply pair_eq.
    symmetry. apply cat_ident1.
    symmetry. apply cat_ident2.
  Qed.

  Theorem curry_apply3 A B C D (f:(prod D A) → B) (h:C → D) (g:C → A) :
    app ∘ pair (curry f ∘ h) g ≈ f ∘ pair h g.
  Proof.
    cut (pair (curry f ∘ h) g ≈ pair_map (curry f) id ∘ pair h g).
    intros. rewrite H.
    rewrite (@cat_assoc PLT).
    rewrite curry_apply. auto.
    rewrite <- pair_map_pair.
    apply pair_eq. auto.
    symmetry. apply cat_ident2.
  Qed.

  Theorem curry_universal A B C (f:(prod C A) → B) (CURRY:C → (exp A B)) :
    app ∘ pair_map CURRY id ≈ f -> CURRY ≈ curry f.
  Proof.
    intro. apply (curry_universal hf); auto.
    apply (hom_directed _ _ f).
    apply plotkin.
    apply (hom_order _ _ CURRY).
    apply (hom_directed _ _ CURRY).
    rewrite pair_map_eq in H. apply H.
  Qed.

  Theorem curry_compose_commute A B C D (f:(prod C A) → B) (h:D → C) :
    curry f ∘ h ≈ curry (f ∘ pair_map h id).
  Proof.
    apply curry_universal.
    unfold pair_map.
    symmetry.
    rewrite <- (curry_apply3).
    apply cat_respects. auto.
    apply pair_eq; auto.
    apply cat_assoc.
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

  Lemma compose_hom_rel : forall (A B C:PLT) (f:A → B) (g:B → C) x z,
    (x,z) ∈ PLT.hom_rel (g ∘ f) <-> 
    exists y, (x,y) ∈ PLT.hom_rel f /\ (y,z) ∈ PLT.hom_rel g.
  Proof.
    simpl; intros.
    split; intros.
    apply compose_elem in H. auto.
    apply PLT.hom_order.
    apply compose_elem. apply PLT.hom_order.
    auto.
  Qed.

  Lemma pair_hom_rel : forall (A B C:PLT) (f:C → A) (g:C → B) c a b ,
    (c,(a,b)) ∈ hom_rel (pair f g) <-> (c,a) ∈ hom_rel f /\ (c,b) ∈ hom_rel g.
  Proof.
    simpl; intros.
    rewrite pair_rel_elem. intuition.
  Qed.

  Lemma sum_cases_hom_rel : forall (A B C:PLT) (f:A → C) (g:B → C) c z,
    (z,c) ∈ hom_rel (sum_cases f g) <->
        match z with
        | inl a => (a,c) ∈ hom_rel f
        | inr b => (b,c) ∈ hom_rel g
        end.
  Proof.
    simpl; intros.
    rewrite (sum_cases_elem _ _ _ (hom_rel f) (hom_rel g) z c). intuition.
  Qed.

  Lemma curry_hom_rel : forall (A B C:PLT) (f:prod C A → B) c R,
    (c,R) ∈ hom_rel (curry f) <-> 
    (forall a b, (a,b) ∈ proj1_sig R -> ((c,a),b) ∈ hom_rel f).
  Proof.
    intros. simpl.
    rewrite (curry_rel_elem _ _ _ _ _ _ _ _ f (hom_order _ _ f) c R).
    split; auto.
  Qed.

  Lemma app_hom_rel : forall (A B:PLT) R x y,
    ((R,x),y) ∈ hom_rel (@app A B) <-> 
    exists x' y', (x',y') ∈ proj1_sig R /\ x' ≤ x /\ y ≤ y'.
  Proof.
    intros. simpl.
    rewrite (apply_rel_elem _ _ _ _ _ _ x y R). split; auto.
  Qed.

  Global Opaque compose.
  Global Opaque pair.
  Global Opaque sum_cases.
  Global Opaque curry.  
  Global Opaque app.

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

Theorem pair_commute1 (C A B:PLT false) (f:C → A) (g:C → B) :
  pi1 false ∘ pair false f g ≈ f.
Proof.
  apply pair_proj_commute1.
  apply PLT.hom_order.
  apply PLT.hom_order.
  apply PLT.hom_directed.
Qed.

Theorem pair_commute2 (C A B:PLT false) (f:C → A) (g:C → B) :
  pi2 false ∘ pair false f g ≈ g.
Proof.
  apply pair_proj_commute2.
  apply PLT.hom_order.
  apply PLT.hom_order.
  apply PLT.hom_directed.
Qed.

Program Definition terminated_mixin
  := Terminated.Mixin (ob false) (hom false) 
       (hom_eq_mixin false)
       (unit false) (terminate false) _.
Next Obligation.
  intros. split.
  apply terminate_le_univ.
  hnf; simpl; intros.
  destruct a.
  destruct (hom_directed _ _ _ f c nil). hnf; auto.
  simpl. red; intros. apply nil_elem in H0. elim H0.
  destruct H0. apply erel_image_elem in H1.
  revert H1; apply hom_order; auto.
  hnf. auto.
Qed.

Program Definition cartesian_mixin
  := Cartesian.Mixin (ob false) (hom false) 
       (hom_eq_mixin false) (comp_mixin false)
       (prod false) (@pi1 false) (@pi2 false)
       (@pair false) _.
Next Obligation.
  constructor.
  apply pair_commute1.
  apply pair_commute2.
  apply pair_universal.
Qed.

Program Definition cartesian_closed_mixin
  := CartesianClosed.Mixin (ob false) (hom false) 
       (hom_eq_mixin false) (comp_mixin false)
       (cat_axioms false)
       terminated_mixin
       cartesian_mixin 
       (exp false) (@curry false) (@app false)
       _.
Next Obligation.
  constructor.
  intros. 
  generalize (curry_apply false A B C f).
  intros. 
  etransitivity. 2: apply H.
  apply cat_respects; auto.
  unfold pair_map.
  apply pair_eq; auto.
  symmetry. apply cat_ident2.
  intros.
  apply curry_universal.
  etransitivity. 2: apply H.
  apply cat_respects; auto.
  unfold pair_map.
  apply pair_eq; auto.
  apply cat_ident2.
Qed.

Definition terminated :=
  Terminated (ob false) (hom false) 
       (hom_eq_mixin false) (comp_mixin false)
       (cat_axioms false)
       terminated_mixin.
Definition cartesian :=
  Cartesian (ob false) (hom false) 
       (hom_eq_mixin false) (comp_mixin false)
       (cat_axioms false)
       terminated_mixin
       cartesian_mixin.
Definition cartesian_closed :=
  CartesianClosed (ob false) (hom false) 
       (hom_eq_mixin false) (comp_mixin false)
       (cat_axioms false)
       cartesian_mixin
       terminated_mixin
       cartesian_closed_mixin.

End PLT.

Canonical Structure PLT.PLT.
Canonical Structure PLT.ord.
Canonical Structure PLT.dec.
Canonical Structure PLT.hom_ord.
Canonical Structure PLT.hom_eq.
Canonical Structure PLT.comp.
Canonical Structure PLT.homset_cpo.
Canonical Structure PLT.cocartesian.
Canonical Structure PLT.terminated.
Canonical Structure PLT.cartesian.
Canonical Structure PLT.cartesian_closed.

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
Arguments PLT.sum [hf] A B.
Arguments PLT.exp [hf] A B.
Arguments PLT.app [hf A B].
Arguments PLT.curry [hf C A B] f.
Arguments PLT.pair_map [hf] [A B C D] f g.

Coercion PLT.ord : PLT.ob >-> preord.
Coercion PLT.carrier : PLT.ob >-> Sortclass.

Global Close Scope category_ops_scope.

Notation PLT := (PLT.PLT false).
Notation "'∂PLT'" := (PLT.PLT true).

Notation "0" := (PLT.empty _) : plt_scope.
Notation "1" := (PLT.unit _) : plt_scope.
Notation "'Λ' f" := (PLT.curry f) : plt_scope.
Notation apply := (@PLT.app _ _ _).

Notation "〈 f , g 〉" := (@PLT.pair false _ _ _ (f)%plt (g)%plt) : plt_scope.
Notation "A × B" := (@PLT.prod false (A)%plt (B)%plt) : plt_scope.
Notation "A ⇒ B" := (@PLT.exp false (A)%plt (B)%plt) : plt_scope.
Notation "A + B" := (@PLT.sum false (A)%plt (B)%plt) : plt_scope.

Notation "《 f , g 》" := (@PLT.pair true _ _ _ (f)%plt (g)%plt) : plt_scope.
Notation "A ⊗ B" := (@PLT.prod true (A)%plt (B)%plt) : plt_scope.
Notation "A ⊸ B" := (@PLT.exp true (A)%plt (B)%plt) : plt_scope.
Notation "A ⊕ B" := (@PLT.sum true (A)%plt (B)%plt) : plt_scope.

Notation "'π₁'"  := (@PLT.pi1 _ _ _) : plt_scope.
Notation "'π₂'"  := (@PLT.pi2 _ _ _) : plt_scope.
Notation "'ι₁'"  := (@PLT.iota1 _ _ _) : plt_scope.
Notation "'ι₂'"  := (@PLT.iota2 _ _ _) : plt_scope.

Add Parametric Morphism (hf:bool) (C A B:PLT.ob hf) :
    (@PLT.pair hf C A B)
    with signature (Preord.ord_op (PLT.hom_ord hf C A)) ==>
                   (Preord.ord_op (PLT.hom_ord hf C B)) ==>
                   (Preord.ord_op (PLT.hom_ord hf C (PLT.prod A B)))
     as plt_le_pair_morphism.
Proof.
  intros. apply PLT.pair_mono; auto.
Qed.

Add Parametric Morphism (hf:bool) (C A B:PLT.ob hf) :
    (@PLT.sum_cases hf C A B)
    with signature (Preord.ord_op (PLT.hom_ord hf A C)) ==>
                   (Preord.ord_op (PLT.hom_ord hf B C)) ==>
                   (Preord.ord_op (PLT.hom_ord hf (PLT.sum A B) C))
     as plt_le_cases_morphism.
Proof.
  repeat intro.
  destruct a as [z c].
  simpl in *.
  apply (sum_cases_elem C A B (PLT.hom_rel x) (PLT.hom_rel x0)) in H1.
  apply (sum_cases_elem C A B (PLT.hom_rel y) (PLT.hom_rel y0)).
  destruct z; auto.
Qed.

Add Parametric Morphism (hf:bool) (C A B:PLT.ob hf) :
    (@PLT.pair hf C A B)
    with signature (eq_op (PLT.hom_eq hf C A)) ==>
                   (eq_op (PLT.hom_eq hf C B)) ==>
                   (eq_op (PLT.hom_eq hf C (PLT.prod A B)))
     as plt_pair_morphism.
Proof.
  intros. apply PLT.pair_eq; auto.
Qed.

Add Parametric Morphism (hf:bool) (C A B:PLT.ob hf) :
    (@PLT.sum_cases hf C A B)
    with signature (eq_op (PLT.hom_eq hf A C)) ==>
                   (eq_op (PLT.hom_eq hf B C)) ==>
                   (eq_op (PLT.hom_eq hf (PLT.sum A B) C))
     as plt_cases_morphism.
Proof.
  intros. split; apply plt_le_cases_morphism; auto.
Qed.

Add Parametric Morphism (hf:bool) (C A B:PLT.ob hf) :
    (@PLT.curry hf C A B)
    with signature (Preord.ord_op (PLT.hom_ord hf (PLT.prod C A) B)) ==>
                   (Preord.ord_op (PLT.hom_ord hf C (PLT.exp A B)))
     as plt_le_curry_morphism.
Proof.
  intros. apply PLT.curry_mono; auto.
Qed.

Add Parametric Morphism (hf:bool) (C A B:PLT.ob hf) :
    (@PLT.curry hf C A B)
    with signature (eq_op (PLT.hom_eq hf (PLT.prod C A) B)) ==>
                   (eq_op (PLT.hom_eq hf C (PLT.exp A B)))
     as plt_curry_morphism.
Proof.
  intros. apply PLT.curry_eq; auto.
Qed.


Section plt_const.
  Variable hf:bool.
  Variables A B:PLT.PLT hf.
  Variable b:B.
  
  Definition plt_const_rel :=
    eprod (eff_enum A (PLT.effective A))
                       (esubset_dec B (fun x => x ≤ b) 
                          (fun x => eff_ord_dec B (PLT.effective B) x b)
                          (eff_enum B (PLT.effective B))). 
  
  Lemma plt_const_rel_elem : forall a b',
    (a,b') ∈ plt_const_rel <-> b' ≤ b.
  Proof.
    repeat intro. unfold plt_const_rel. split; intro.
    apply eprod_elem in H. destruct H.
    apply esubset_dec_elem in H0. destruct H0; auto.
    intros. rewrite <- H1; auto.
    apply eprod_elem. split.
    apply eff_complete.
    apply esubset_dec_elem.
    intros. rewrite <- H0. auto.
    split; auto.
    apply eff_complete.
  Qed.

  Program Definition plt_const :=
    PLT.Hom hf A B plt_const_rel _ _.
  Next Obligation.
    intros.
    apply plt_const_rel_elem in H1.
    apply plt_const_rel_elem.
    eauto.
  Qed.
  Next Obligation.
    repeat intro.
    exists b; split; repeat intro.
    apply H in H0.
    apply erel_image_elem in H0.
    apply plt_const_rel_elem in H0. auto.
    apply erel_image_elem.
    apply plt_const_rel_elem. auto.
  Qed.
End plt_const.  

Theorem pair_bottom1 (C A B:ob ∂PLT) (f:C → A) :
  《 f, ⊥ : C → B 》 ≈ ⊥.
Proof.
  split. hnf; simpl; intros.
  destruct a as [c [a b]].
  apply (PLT.pair_hom_rel _ A B C) in H.
  destruct H.
  simpl in H0.
  apply union_axiom in H0.
  destruct H0 as [q [??]].
  apply image_axiom2 in H0.
  destruct H0 as [?[??]].
  apply empty_elem in H0. elim H0.
  apply bottom_least.
Qed.

Theorem pair_bottom2 (C A B:ob ∂PLT) (g:C → B) :
  《 ⊥ : C → A,  g 》 ≈ ⊥.
Proof.
  split. hnf; simpl; intros.
  destruct a as [c [a b]].
  apply (PLT.pair_hom_rel _ A B C) in H.
  destruct H. simpl in H.
  apply union_axiom in H.
  destruct H as [q [??]].
  apply image_axiom2 in H.
  destruct H as [?[??]].
  apply empty_elem in H. elim H.
  apply bottom_least.
Qed.

Theorem pi1_greatest (A B:ob ∂PLT) (proj:A⊗B → A) :
  (forall C (f:C → A) (g:C → B), proj ∘ 《f, g》 ≤ f) ->
  proj ≤ π₁.
Proof.
  repeat intro.
  destruct a as [[a b] a']. simpl in *.
  apply pi1_rel_elem.
  apply (plt_const_rel_elem true B A a b a').
  apply (H B (plt_const _ _ _ a) (id) (b,a')).
  apply PLT.compose_hom_rel.
  exists (a,b).
  split; auto.
  simpl.
  apply PLT.pair_hom_rel.
  split; auto.
  apply plt_const_rel_elem. auto.
  apply ident_elem. auto.
Qed.
  
Theorem pi2_greatest (A B:ob ∂PLT) (proj:A⊗B → B) :
  (forall C (f:C → A) (g:C → B), proj ∘ 《f, g》 ≤ g) ->
  proj ≤ π₂.
Proof.
  repeat intro.
  destruct a as [[a b] b']. simpl in *.
  apply pi2_rel_elem.
  apply (plt_const_rel_elem true A B b a b').
  apply (H A (id) (plt_const _ _ _ b) (a,b')).
  apply PLT.compose_hom_rel.
  exists (a,b).
  split; auto.
  simpl.
  apply PLT.pair_hom_rel.
  split; auto.
  apply ident_elem. auto.
  apply plt_const_rel_elem. auto.
Qed.

Definition antistrict (A B:∂PLT) (f:A → B) :=
  forall a, exists b, (a,b) ∈ PLT.hom_rel f.
Arguments antistrict [A B] f.
    
Definition nonbottom (A B:∂PLT) (f:A → B) :=
  exists x, x ∈ PLT.hom_rel f.
Arguments nonbottom [A B] f.

Lemma antistrict_nonbottom (A B C:∂PLT) (f:A → B) :
  antistrict f <-> (forall C (g:C → A), nonbottom g -> nonbottom (f ∘ g)).
Proof.
  split; intros.
  destruct H0 as [[??] ?].
  destruct (H c0) as [q ?].
  exists (c,q). apply PLT.compose_hom_rel. eauto.
  red; intros.
  destruct (H (PLT.unit true) (plt_const true _ _ a)).
  exists (tt,a). simpl. apply plt_const_rel_elem. auto.
  destruct x as [??].
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [q [??]].
  simpl in *. apply plt_const_rel_elem in H0.
  exists c0. eapply PLT.hom_order; eauto.
Qed.

Theorem antistrict_pair_commute1 (C B:∂PLT) (g:C → B) :
  antistrict g <-> forall A (f:C → A), π₁ ∘ 《f,g》 ≈ f.
Proof.
  intros.
  split; repeat intro.
  split. apply PLT.pair_le_commute1.
  hnf; intros.
  apply PLT.compose_hom_rel. simpl.
  destruct a as [c a].
  destruct (H c) as [b ?].
  exists (a,b).    
  split.
  apply PLT.pair_hom_rel. split; auto.
  apply pi1_rel_elem. auto.

  rename a into c.
  destruct (H C id).
  assert ((c,c) ∈ PLT.hom_rel (PLT.pi1 ∘ PLT.pair id g)).
  apply H1. simpl. apply ident_elem. auto.
  apply PLT.compose_hom_rel in H2.
  destruct H2 as [q [??]].
  destruct q.
  simpl in H2.
  rewrite (PLT.pair_hom_rel _ _ _ _ _ _ c c0 c1) in H2. destruct H2.
  simpl in H2.
  apply ident_elem in H2.
  exists c1; auto.
Qed.

Theorem antistrict_pair_commute2 (C A:∂PLT) (f:C → A) :
  antistrict f <-> forall B (g:C → B), π₂ ∘ 《f, g》 ≈ g.
Proof.
  split; intros.
  split. apply PLT.pair_le_commute2.
  hnf; intros.
  apply PLT.compose_hom_rel. simpl.
  destruct a as [c b].
  destruct (H c) as [a ?].
  exists (a,b).    
  split.
  apply pair_rel_elem. split; auto.
  apply pi2_rel_elem. auto.
  
  intro c. destruct (H C id).
  assert ((c,c) ∈ PLT.hom_rel (π₂ ∘ PLT.pair f id)).
  apply H1. simpl. apply ident_elem. auto.
  apply PLT.compose_hom_rel in H2.
  destruct H2 as [q [??]].
  destruct q.
  simpl in H2.
  rewrite (PLT.pair_hom_rel _ _ _ _ _ _ c c0 c1) in H2. destruct H2.
  simpl in H4. apply ident_elem in H4.
  exists c0; auto.
Qed.
