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
Require Import profinite.

Close Scope plt_scope.

Delimit Scope cplt_scope with cplt.
Open Scope cplt_scope.

(**  * Categories of continuous domains, expressed as retracts of profinite domains.

     A DCPO is a continuous domain iff is a retract of an algebraic domain.
     Furthermore, every retract can be expressed as the image of an idempotent
     continuous function.

     Thus, we can build the category of retracts of
     bifinite domains by taking the bifinite domains together with an
     idempotent hom.  Conceptually, we are constructing a new (continuous)
     domain as the image of the given idempotent continuous function.

     The homs of this new category are just homs of bifinite domains,
     but considered up to a looser notion of equality.  In addition, when
     composing homs, the retract of the intermediate domain is applied.
  *)

Module cPLT.
Section cPLT.
  Variable hf:bool.

  Record ob :=
    Ob
    { cplt_ob : PLT.PLT hf
    ; cplt_retract : PLT.hom cplt_ob cplt_ob
    ; cplt_idem : cplt_retract ∘ cplt_retract ≈ cplt_retract
    }.

  Record hom (A B:ob) :=
    Hom { cplt_hom : PLT.hom (cplt_ob A) (cplt_ob B) }.
  Arguments cplt_hom [A B] _.

  Program Definition hom_ord_mixin (A B:ob) : Preord.mixin_of (hom A B) :=
    Preord.Mixin (hom A B) 
       (fun f g => cplt_retract B ∘ cplt_hom f ∘ cplt_retract A 
                 ≤ cplt_retract B ∘ cplt_hom g ∘ cplt_retract A)
       _ _.
  Solve Obligations of hom_ord_mixin with (simpl; intros; auto).
  Next Obligation.
    simpl; intros. etransitivity; eauto.
  Qed.

  Canonical Structure hom_ord (A B:ob) := Preord.Pack (hom A B) (hom_ord_mixin A B).

  Definition hom_eq_mixin (A B:ob) := Preord.ord_eq (hom_ord A B).
  Canonical Structure hom_eq (A B:ob) := Eq.Pack (hom A B) (hom_eq_mixin A B).

  Definition ident (A:ob) := Hom A A (PLT.ident hf (cplt_ob A)).
  Definition compose (A B C:ob) (g:hom B C) (f:hom A B) := 
    Hom A C (cplt_hom g ∘ cplt_retract B ∘ cplt_hom f).
    
  Definition comp_mixin : Comp.mixin_of ob hom
    := Comp.Mixin ob hom ident compose.
  Canonical Structure comp : Comp.type := Comp.Pack ob hom comp_mixin.

  Definition ord (X:ob) := PLT.ord (cplt_ob X).
  Definition dec (X:ob) := PLT.dec (cplt_ob X).
  Definition carrier (X:ob) := PLT.carrier hf (cplt_ob X).


  Lemma compose_mono (X Y Z:ob) (f f':hom X Y) (g g':hom Y Z) :
    f ≤ f' -> g ≤ g' -> g ∘ f ≤ g' ∘ f'.
  Proof.
    simpl; intros.
    red; simpl.
    unfold compose. simpl.
    red in H; simpl in H.
    red in H0; simpl in H0.
    transitivity 
      ((cplt_retract Z ∘ cplt_hom g ∘ cplt_retract Y) ∘
       (cplt_retract Y ∘ cplt_hom f ∘ cplt_retract X)).
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono; auto.
    apply PLT.compose_mono; auto.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono; auto.
    apply PLT.compose_mono; auto.
    rewrite (cplt_idem Y). auto.
    transitivity 
      ((cplt_retract Z ∘ cplt_hom g' ∘ cplt_retract Y) ∘
       (cplt_retract Y ∘ cplt_hom f' ∘ cplt_retract X)).
    apply PLT.compose_mono; auto.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono; auto.
    apply PLT.compose_mono; auto.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono; auto.
    apply PLT.compose_mono; auto.
    rewrite (cplt_idem Y). auto.
  Qed.
  
  Lemma cplt_hom_le (A B:ob) (f g:hom A B) :
    cplt_retract B ∘ cplt_hom f ∘ cplt_retract A ≤
    cplt_retract B ∘ cplt_hom g ∘ cplt_retract A <->
    f ≤ g.
  Proof.
    intros. red; auto.
  Qed.

  Lemma cplt_hom_eq (A B:ob) (f g:hom A B) :
    cplt_retract B ∘ cplt_hom f ∘ cplt_retract A ≈
    cplt_retract B ∘ cplt_hom g ∘ cplt_retract A <->
    f ≈ g.
  Proof.
    split.
    intros; destruct H; split; apply cplt_hom_le; auto.
    intros; destruct H.
    apply cplt_hom_le in H.
    apply cplt_hom_le in H0.
    split; auto.
  Qed.

  Lemma cat_axioms : Category.axioms ob hom hom_eq_mixin comp_mixin.
  Proof.
    constructor.

    intros. rewrite <- cplt_hom_eq. simpl. 
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cat_ident1 (PLT.PLT hf)).
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem A). auto.

    intros. rewrite <- cplt_hom_eq. simpl. 
    rewrite (cat_ident2 (PLT.PLT hf)).
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem B). auto.

    intros. rewrite <- cplt_hom_eq. simpl.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    auto.

    intros. split; apply compose_mono; auto.
  Qed.

  Canonical Structure cPLT : category :=
    Category ob hom hom_eq_mixin comp_mixin cat_axioms.

  Definition empty : ob :=
    Ob (PLT.empty hf) id(PLT.empty hf) (cat_ident1 (PLT.PLT hf) _ _ id).

  Definition unit : ob :=
    Ob (PLT.unit hf) id(PLT.unit hf) (cat_ident1 (PLT.PLT hf) _ _ id).

  Program Definition prod (A B:ob) : ob :=
    Ob (PLT.prod (cplt_ob A) (cplt_ob B))
       (PLT.pair_map (cplt_retract A) (cplt_retract B))
       _.
  Next Obligation.
    simpl; intros.
    unfold PLT.pair_map at 2.
    rewrite <- (PLT.pair_map_pair hf).
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem A).
    rewrite (cplt_idem B). auto.
  Qed.
  Canonical Structure prod.

  Program Definition sum (A B:ob) : ob :=
    Ob (PLT.sum (cplt_ob A) (cplt_ob B))
       (PLT.sum_cases 
          (PLT.iota1 ∘ cplt_retract A) (PLT.iota2 ∘ cplt_retract B))
       _. 
  Next Obligation.
    intros. apply PLT.sum_cases_universal.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota1_cases_commute hf).
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota1_cases_commute hf).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem A). auto.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota2_cases_commute hf).
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota2_cases_commute hf).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem B). auto.
  Qed.
  Canonical Structure sum.

  Program Definition exp (A B:ob) : ob :=
    Ob (PLT.exp (cplt_ob A) (cplt_ob B))
       (PLT.curry (cplt_retract B ∘ PLT.app ∘ PLT.pair_map id(_) (cplt_retract A)))
       _.
  Next Obligation.
    intros.
    rewrite (PLT.curry_compose_commute hf).
    unfold PLT.pair_map at 2.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite <- (PLT.pair_map_pair hf).
    repeat rewrite (cat_ident2 (PLT.PLT hf)).
    unfold PLT.pair_map.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.curry_apply3 hf).
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem B).
    apply PLT.curry_eq.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    apply cat_respects. auto.
    etransitivity.
    symmetry. apply PLT.pair_map_pair.
    apply PLT.pair_eq; auto.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem A). auto.
  Qed.
  Canonical Structure exp.

  Definition initiate A : empty → A :=
    Hom empty A (PLT.initiate hf (cplt_ob A)).

  Definition terminate A : A → unit :=
    Hom A unit (PLT.terminate hf (cplt_ob A)).

  Definition iota1 A B : A → (sum A B) :=
    Hom A (sum A B) (PLT.iota1).

  Definition iota2 A B : B → (sum A B) :=
    Hom B (sum A B) (PLT.iota2).

  Definition sum_cases {C A B} (f:A → C) (g:B → C) : (sum A B) → C :=
    Hom (sum A B) C (PLT.sum_cases (cplt_hom f) (cplt_hom g)).

  Definition app {A B} : (prod (exp A B) A) → B :=
    Hom (prod (exp A B) A) B  (@PLT.app hf (cplt_ob A) (cplt_ob B)).

  Definition curry {C A B} (f:(prod C A) → B) : C → (exp A B) :=
    Hom C (exp A B) (PLT.curry (cplt_hom f)).

  Definition pair {C A B} (f:C → A) (g:C → B) : C → (prod A B) :=
    Hom C (prod A B) (PLT.pair (cplt_hom f) (cplt_hom g)).

  Definition pi1 {A B} : (prod A B) → A :=
    Hom (prod A B) A (PLT.pi1).

  Definition pi2 {A B} : (prod A B) → B :=
    Hom (prod A B) B (PLT.pi2).

  Definition pair_map {A B C D} (f:A → C) (g:B → D) : (prod A B) → (prod C D) :=
    pair (f ∘ pi1) (g ∘ pi2).

  Theorem initiate_univ A (f:empty → A) :
    f ≈ initiate A.
  Proof.
    rewrite <- cplt_hom_eq. simpl.
    rewrite (PLT.initiate_univ hf (cplt_ob A) (cplt_hom f)).
    auto.
  Qed.

  Theorem terminate_le_univ A (f:A → unit) :
    f ≤ terminate A.
  Proof.
    rewrite <- cplt_hom_le. simpl.
    apply PLT.compose_mono; auto.
    apply PLT.compose_mono; auto.
    apply PLT.terminate_le_univ.
  Qed.

  Theorem iota1_cases_commute C A B (f:A → C) (g:B → C) :
    sum_cases f g ∘ iota1 A B ≈ f.
  Proof.
    rewrite <- cplt_hom_eq. simpl.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    apply cat_respects. auto.
    etransitivity.
    apply cat_respects. auto.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota1_cases_commute hf).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem A). auto.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota1_cases_commute hf).
    auto.
  Qed.

  Theorem iota2_cases_commute C A B (f:A → C) (g:B → C) :
    sum_cases f g ∘ iota2 A B ≈ g.
  Proof.
    rewrite <- cplt_hom_eq. simpl.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    apply cat_respects. auto.
    etransitivity.
    apply cat_respects. auto.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota2_cases_commute hf).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem B). auto.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota2_cases_commute hf).
    auto.
  Qed.

  Theorem sum_cases_universal C A B (f:A → C) (g:B → C) (CASES:(sum A B) → C) :
    CASES ∘ iota1 A B ≈ f -> CASES ∘ iota2 A B ≈ g -> CASES ≈ sum_cases f g.
  Proof.
    intros.
    rewrite <- cplt_hom_eq. simpl.
    rewrite <- cplt_hom_eq in H. 
    rewrite <- cplt_hom_eq in H0.
    symmetry.
    transitivity
       (PLT.sum_cases (cplt_retract C ∘ cplt_hom f ∘ cplt_retract A)
                      (cplt_retract C ∘ cplt_hom g ∘ cplt_retract B)).
    apply PLT.sum_cases_universal.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota1_cases_commute hf).
    rewrite (cat_assoc (PLT.PLT hf)).
    apply cat_respects; auto.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota1_cases_commute hf).
    auto.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota2_cases_commute hf).
    rewrite (cat_assoc (PLT.PLT hf)).
    apply cat_respects; auto.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota2_cases_commute hf).
    auto.

    symmetry.
    apply PLT.sum_cases_universal.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota1_cases_commute hf).
    etransitivity. 2: apply H. simpl.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    apply cat_respects; auto.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    apply cat_respects; auto.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota1_cases_commute hf).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem A). auto.

    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota2_cases_commute hf).
    etransitivity. 2: apply H0. simpl.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    apply cat_respects; auto.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    apply cat_respects; auto.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.iota2_cases_commute hf).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem B). auto.
  Qed.

  Theorem pair_universal_le C A B (f:C → A) (g:C → B) (PAIR:C → (prod A B)) :
    pi1 ∘ PAIR ≤ f -> pi2 ∘ PAIR ≤ g -> PAIR ≤ pair f g.
  Proof.
    intros.
    rewrite <- cplt_hom_le. simpl.
    rewrite <- cplt_hom_le in H. 
    rewrite <- cplt_hom_le in H0.
    rewrite <- (PLT.pair_map_pair hf).
    unfold PLT.pair_map.
    rewrite (PLT.pair_compose_commute hf).
    rewrite (PLT.pair_compose_commute hf).
    rewrite (PLT.pair_compose_commute hf).
    rewrite <- H. rewrite <- H0. clear H H0.

    simpl. repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    set (h := cplt_hom PAIR ∘ cplt_retract C). simpl in *.
    cut (
        PLT.pair (cplt_retract A ∘ (π₁%plt ∘ h))
                 (cplt_retract B ∘ (π₂%plt ∘ h))
        ≤
     PLT.pair
       (cplt_retract A ∘
         (π₁%plt ∘
           (PLT.pair_map (cplt_retract A) (cplt_retract B) ∘
             h )))
       (cplt_retract B ∘
         (π₂%plt ∘
           (PLT.pair_map (cplt_retract A) (cplt_retract B) ∘
             h))) ).
    auto. 
    clearbody h.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    
    hnf; simpl; intros [??] ?.
    destruct p.
    apply (PLT.pair_hom_rel hf _ _ _ _ _ c c0 c1) in H. destruct H.
    apply PLT.compose_hom_rel in H.
    destruct H as [q1 [??]].
    apply PLT.compose_hom_rel in H0.
    destruct H0 as [q2 [??]].
    destruct (PLT.hom_directed hf _ _ h c (q1::q2::nil)%list) as [q3 [??]].
    apply elem_inh with q1. apply cons_elem; auto.
    red; intros.
    rewrite erel_image_elem.
    apply cons_elem in H3; destruct H3.
    eapply PLT.hom_order with c q1; auto.
    apply cons_elem in H3; destruct H3.
    eapply PLT.hom_order with c q2; auto.
    apply nil_elem in H3. elim H3.
    apply erel_image_elem in H4.
    apply PLT.compose_hom_rel in H1.
    destruct H1 as [m [??]].
    simpl in H1.
    destruct q1 as [q1 q1'].
    rewrite (pi1_rel_elem _ _ _ _ q1 q1' m) in H1.
    apply PLT.compose_hom_rel in H2.
    destruct H2 as [n [??]].
    simpl in H2.
    destruct q2 as [q2 q2'].
    rewrite (pi2_rel_elem _ _ _ _ q2 q2' n) in H2.
    apply PLT.pair_hom_rel. split.
    apply PLT.compose_hom_rel. exists q3.
    split; auto.
    destruct (cplt_idem A).
    generalize (H8 (m,c0) H5).
    intros.
    apply PLT.compose_hom_rel in H9.
    destruct H9 as [m' [??]].
    apply PLT.compose_hom_rel.
    exists (m',c1).
    split.
    unfold PLT.pair_map.
    apply PLT.pair_hom_rel.
    split.
    apply PLT.compose_hom_rel.
    exists m. split; auto.
    simpl.
    destruct q3 as [q3 q3'].
    apply pi1_rel_elem.
    transitivity q1; auto.
    assert ((q1,q1') ≤ (q3,q3')).
    apply H3. apply cons_elem; auto. destruct H11; auto.
    apply PLT.compose_hom_rel.
    exists n. split; auto.
    simpl.
    destruct q3 as [q3 q3'].
    apply pi2_rel_elem.
    transitivity q2'; auto.
    assert ((q2,q2') ≤ (q3,q3')).
    apply H3. 
    apply cons_elem; right.
    apply cons_elem; auto.
    destruct H11; auto.
    apply PLT.compose_hom_rel.
    exists m'. split; auto.
    simpl.
    apply pi1_rel_elem. auto.
    apply PLT.compose_hom_rel.
    exists q3. split; auto.
    
    destruct (cplt_idem B).
    generalize (H8 (n,c1) H6).
    intros.
    apply PLT.compose_hom_rel in H9.
    destruct H9 as [n' [??]].
    apply PLT.compose_hom_rel.
    exists (c0,n').
    split.
    unfold PLT.pair_map.
    apply PLT.pair_hom_rel.
    split.
    apply PLT.compose_hom_rel.
    exists m. split; auto.
    simpl.
    destruct q3 as [q3 q3'].
    apply pi1_rel_elem.
    transitivity q1; auto.
    assert ((q1,q1') ≤ (q3,q3')).
    apply H3. apply cons_elem; auto. destruct H11; auto.
    apply PLT.compose_hom_rel.
    exists n. split; auto.
    simpl.
    destruct q3 as [q3 q3'].
    apply pi2_rel_elem.
    transitivity q2'; auto.
    assert ((q2,q2') ≤ (q3,q3')).
    apply H3. 
    apply cons_elem; right.
    apply cons_elem; auto.
    destruct H11; auto.
    apply PLT.compose_hom_rel.
    exists n'. split; auto.
    simpl.
    apply pi2_rel_elem. auto.
  Qed.

  Theorem pair_universal C A B (f:C → A) (g:C → B) (PAIR:C → (prod A B)) :
    pi1 ∘ PAIR ≈ f -> pi2 ∘ PAIR ≈ g -> PAIR ≈ pair f g.
  Proof.
    intros. split. apply pair_universal_le; auto.
    rewrite <- cplt_hom_le. simpl.
    rewrite <- cplt_hom_eq in H. 
    rewrite <- cplt_hom_eq in H0.
    rewrite <- (PLT.pair_map_pair hf).
    unfold PLT.pair_map.
    rewrite (PLT.pair_compose_commute hf).
    rewrite (PLT.pair_compose_commute hf).
    rewrite (PLT.pair_compose_commute hf).
    rewrite <- H. rewrite <- H0. clear H H0.

    simpl.
    apply PLT.pair_mono.
    unfold PLT.pair_map.
    etransitivity.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. 2: reflexivity.
    rewrite (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. reflexivity.
    apply PLT.pair_le_commute1.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem A).
    auto.
    unfold PLT.pair_map.
    etransitivity.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. 2: reflexivity.
    rewrite (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. reflexivity.
    apply PLT.pair_le_commute2.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem B).
    auto.
  Qed.

  Theorem pair_le_commute1 C A B (f:C → A) (g:C → B) :
    pi1 ∘ pair f g ≤ f.
  Proof.
    rewrite <- cplt_hom_le. simpl.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. reflexivity.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    etransitivity.
    apply PLT.compose_mono. 2: reflexivity.
    rewrite (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. reflexivity.
    apply PLT.pair_le_commute1.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem A).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono.
    apply PLT.pair_le_commute1.
    auto.
  Qed.

  Theorem pair_le_commute2 C A B (f:C → A) (g:C → B) :
    pi2 ∘ pair f g ≤ g.
  Proof.
    rewrite <- cplt_hom_le. simpl.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. reflexivity.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    etransitivity.
    apply PLT.compose_mono. 2: reflexivity.
    rewrite (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. reflexivity.
    apply PLT.pair_le_commute2.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem B).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono.
    apply PLT.pair_le_commute2.
    auto.
  Qed.

  Theorem pair_compose_commute A B C D
    (f:C → A) (g:C → B) (h:D → C) :
    pair f g ∘ h ≈ pair (f ∘ h) (g ∘ h).
  Proof.
    rewrite <- cplt_hom_eq. simpl.
    apply cat_respects; auto.
    apply cat_respects; auto.
    rewrite (PLT.pair_compose_commute hf).
    rewrite (PLT.pair_compose_commute hf).
    auto.
  Qed.


  Theorem curry_apply A B C (f:(prod C A) → B) :
    app ∘ pair_map (curry f) id ≈ f.
  Proof.
    rewrite <- cplt_hom_eq. simpl.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    unfold PLT.pair_map at 3.
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite <- (PLT.pair_map_pair hf).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    etransitivity.
    apply cat_respects. reflexivity.
    apply cat_respects. reflexivity.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    symmetry. apply PLT.pair_map_pair.
    etransitivity.
    apply cat_respects. reflexivity.
    rewrite (PLT.curry_compose_commute hf).
    rewrite (PLT.curry_compose_commute hf).
    apply PLT.curry_apply3.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem B).
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite <- (PLT.pair_map_pair hf).
    rewrite <- (PLT.pair_map_pair hf).
    rewrite <- (PLT.pair_map_pair hf).
    rewrite (cat_ident2 (PLT.PLT hf)).
    rewrite (PLT.curry_apply3 hf).
    repeat rewrite (cat_ident2 (PLT.PLT hf)).
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem A).
    rewrite (cplt_idem A).
    rewrite (cplt_idem A).
    rewrite (cplt_idem C).
    auto.
  Qed.

  Theorem pair_mono (C A B:ob) (f f':C → A) (g g':C → B) :
    f ≤ f' -> g ≤ g' -> pair f g ≤ pair f' g'.
  Proof.
    intros. red. simpl. 
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.pair_compose_commute hf).
    rewrite <- (PLT.pair_map_pair hf).
    rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.pair_compose_commute hf).
    rewrite <- (PLT.pair_map_pair hf).
    apply PLT.pair_mono.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cat_assoc (PLT.PLT hf)).
    apply H.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cat_assoc (PLT.PLT hf)).
    apply H0.
  Qed.

  Theorem pair_eq (C A B:ob) (f f':C → A) (g g':C → B) :
    f ≈ f' -> g ≈ g' -> pair f g ≈ pair f' g'.
  Proof.
    intros. split; apply pair_mono; auto.
  Qed.

  Theorem sum_cases_mono (C A B:ob) (f f':A → C) (g g':B → C) :
    f ≤ f' -> g ≤ g' -> sum_cases f g ≤ sum_cases f' g'.
  Proof.
    intros. rewrite <- cplt_hom_le. simpl.
    rewrite <- cplt_hom_le in H.
    rewrite <- cplt_hom_le in H0.
    transitivity
      (PLT.sum_cases 
         (cplt_retract C ∘ cplt_hom f ∘ cplt_retract A)
         (cplt_retract C ∘ cplt_hom g ∘ cplt_retract B)).
    apply eq_ord.
    apply PLT.sum_cases_universal.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)). 
    rewrite (PLT.iota1_cases_commute hf).
    rewrite (cat_assoc (PLT.PLT hf) _ _ _ _ _ ι₁%plt). 
    rewrite (PLT.iota1_cases_commute hf).
    auto.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)). 
    rewrite (PLT.iota2_cases_commute hf).
    rewrite (cat_assoc (PLT.PLT hf) _ _ _ _ _ ι₂%plt). 
    rewrite (PLT.iota2_cases_commute hf).
    auto.
    
    transitivity
      (PLT.sum_cases 
         (cplt_retract C ∘ cplt_hom f' ∘ cplt_retract A)
         (cplt_retract C ∘ cplt_hom g' ∘ cplt_retract B)).
    apply PLT.sum_cases_mono; auto.

    apply eq_ord.
    symmetry. apply PLT.sum_cases_universal.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)). 
    rewrite (PLT.iota1_cases_commute hf).
    rewrite (cat_assoc (PLT.PLT hf) _ _ _ _ _ ι₁%plt). 
    rewrite (PLT.iota1_cases_commute hf).
    auto.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)). 
    rewrite (PLT.iota2_cases_commute hf).
    rewrite (cat_assoc (PLT.PLT hf) _ _ _ _ _ ι₂%plt). 
    rewrite (PLT.iota2_cases_commute hf).
    auto.
  Qed.

  Theorem sum_cases_eq (C A B:ob) (f f':A → C) (g g':B → C) :
    f ≈ f' -> g ≈ g' -> sum_cases f g ≈ sum_cases f' g'.
  Proof.
    intros. split; apply sum_cases_mono; auto.
  Qed.

  Theorem curry_mono (C A B:ob) (f f':prod C A → B) :
    f ≤ f' -> curry f ≤ curry f'.
  Proof.
    intros.
    rewrite <- cplt_hom_le. simpl.
    rewrite <- cplt_hom_le in H.
    transitivity (Λ(cplt_retract B ∘ cplt_hom f ∘ cplt_retract (prod C A)))%plt.
    apply eq_ord. apply PLT.curry_universal.
    unfold PLT.pair_map at 1.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite PLT.curry_apply3.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite <- (PLT.pair_map_pair hf).
    repeat rewrite (cat_ident2 (PLT.PLT hf)).    
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.curry_apply3 hf).
    auto.

    transitivity (Λ(cplt_retract B ∘ cplt_hom f' ∘ cplt_retract (prod C A)))%plt.
    apply PLT.curry_mono; auto.

    apply eq_ord. symmetry. apply PLT.curry_universal.
    unfold PLT.pair_map at 1.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite PLT.curry_apply3.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite <- (PLT.pair_map_pair hf).
    repeat rewrite (cat_ident2 (PLT.PLT hf)).    
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite (PLT.curry_apply3 hf).
    auto.
  Qed.

  Theorem curry_eq (C A B:ob) (f f':prod C A → B) :
    f ≈ f' -> curry f ≈ curry f'.
  Proof.
    intros; destruct H; split; apply curry_mono; trivial.
  Qed.

  Theorem pair_map_pair C X Y Z W (f1:C → X) (f2:X → Y) (g1:C → Z) (g2:Z → W) :
    pair (f2 ∘ f1) (g2 ∘ g1) ≈ pair_map f2 g2 ∘ pair f1 g1.
  Proof.
    rewrite <- cplt_hom_eq. simpl.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    apply cat_respects; auto.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    apply cat_respects; auto.
    transitivity (
      (PLT.pair_map (cplt_hom f2 ∘ cplt_retract X)
                    (cplt_hom g2 ∘ cplt_retract Z)) ∘
      (PLT.pair_map (cplt_retract X)
                    (cplt_retract Z)) ∘
      (PLT.pair (cplt_hom f1) (cplt_hom g1))).
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    rewrite <- (PLT.pair_map_pair hf).
    rewrite <- (PLT.pair_map_pair hf).
    apply PLT.pair_eq.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    apply cat_respects; auto.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem X). auto.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    apply cat_respects; auto.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem Z). auto.
    reflexivity.
  Qed.    

  Theorem curry_apply2 A B C (f:(prod C A) → B) (g:C → A) :
    app ∘ pair (curry f) g ≈ f ∘ pair id g.
  Proof.
    cut (pair (curry f) g ≈ pair_map (curry f) id ∘ pair id g).
    intros. rewrite H.
    rewrite (@cat_assoc cPLT).
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
    rewrite (@cat_assoc cPLT).
    rewrite curry_apply. auto.
    rewrite <- pair_map_pair.
    apply pair_eq. auto.
    symmetry. apply cat_ident2.
  Qed.

  Theorem curry_universal A B C (f:(prod C A) → B) (CURRY:C → (exp A B)) :
    app ∘ pair_map CURRY id ≈ f -> CURRY ≈ curry f.
  Proof.
    intros.
    rewrite <- cplt_hom_eq. simpl.
    rewrite <- cplt_hom_eq in H. simpl in H.
    repeat rewrite (PLT.curry_compose_commute hf).
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    unfold PLT.pair_map at 6.
    rewrite <- (PLT.pair_map_pair hf).
    rewrite <- (PLT.pair_map_pair hf).
    repeat rewrite (cat_ident2 (PLT.PLT hf)).
    rewrite (PLT.curry_apply3 hf).
    apply PLT.curry_eq.
    symmetry.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    rewrite <- H.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    unfold PLT.pair_map at 3.
    etransitivity.
    apply cat_respects. auto.
    apply cat_respects. auto.
    apply cat_respects. auto.
    symmetry. apply PLT.pair_map_pair.
    rewrite <- (PLT.pair_map_pair hf).
    rewrite (PLT.curry_apply3 hf).
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem B).
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    apply cat_respects. auto.
    apply cat_respects. auto.
    rewrite <- (PLT.pair_map_pair hf).
    unfold PLT.pair_map at 3.
    rewrite <- (PLT.pair_map_pair hf).
    rewrite <- (PLT.pair_map_pair hf).
    repeat rewrite (cat_ident2 (PLT.PLT hf)).
    apply PLT.pair_eq.
    apply cat_respects. auto.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem C). auto.
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem A).
    rewrite (cplt_idem A).
    rewrite (cplt_idem A).
    auto.
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

  Section homset_cpo.
    Variables A B:ob.

    Definition hom_rel' : hom_ord A B → PLT.hom_ord hf (cplt_ob A) (cplt_ob B) :=
      Preord.Hom (hom_ord A B) (PLT.hom_ord hf (cplt_ob A) (cplt_ob B)) 
         (fun f => cplt_retract B ∘ cplt_hom f ∘ cplt_retract A) (fun f g H => H).

    Program Definition homset_sup (M:cl_eset (directed_hf_cl hf) (hom_ord A B)) 
      : hom A B := Hom A B (∐(image hom_rel' M)).

    Program Definition homset_cpo_mixin : 
      CPO.mixin_of (directed_hf_cl hf) (hom_ord A B)
      := CPO.Mixin _ _ homset_sup _ _.
    Next Obligation.
      intros. red; intros.
      red; simpl.
      transitivity
        (cplt_retract B ∘ (cplt_retract B ∘ cplt_hom x ∘ cplt_retract A) ∘ cplt_retract A). 
      repeat rewrite (cat_assoc (PLT.PLT hf)).
      rewrite (cplt_idem B).
      repeat rewrite <- (cat_assoc (PLT.PLT hf)).
      rewrite (cplt_idem A).
      auto.
      apply PLT.compose_mono; auto.
      apply PLT.compose_mono; auto.
      apply CPO.sup_is_ub.
      apply (image_axiom1'). exists x. split; auto.
    Qed.
    Next Obligation.
      intros.
      red; simpl.

Require Import fixes.      

      transitivity ((∐
        (image (postcompose _ (cplt_retract B) ∘ precompose _ (cplt_retract A)) 
           (image hom_rel' X)))).
      destruct (@CPO.continuous_sup _
                            (PLT.homset_cpo hf (cplt_ob A) (cplt_ob B))
                            (PLT.homset_cpo hf (cplt_ob A) (cplt_ob B))
                            (postcompose _ (cplt_retract B) ∘ precompose _ (cplt_retract A)))
               as [? _].
      etransitivity. 2: apply H0. simpl.
      rewrite (cat_assoc (PLT.PLT hf)). auto.
      apply continuous_sequence.
      apply postcompose_continuous.
      apply precompose_continuous.
      apply CPO.sup_is_least.
      red; simpl; intros.
      apply image_axiom2 in H0.
      destruct H0 as [q [??]].
      apply image_axiom2 in H0.
      destruct H0 as [q' [??]].
      rewrite H1. simpl.
      rewrite H2. simpl.
      red in H.
      generalize (H q' H0).
      intros. red in H3. simpl in H3.
      repeat rewrite (cat_assoc (PLT.PLT hf)).
      rewrite (cplt_idem B).
      repeat rewrite <- (cat_assoc (PLT.PLT hf)).
      rewrite (cplt_idem A).
      repeat rewrite (cat_assoc (PLT.PLT hf)).
      auto.
    Qed.

    Definition homset_cpo : CPO.type (directed_hf_cl hf) :=
      CPO.Pack _ (hom A B) (hom_ord_mixin A B) homset_cpo_mixin.
  End homset_cpo.

End cPLT.

Theorem pair_commute1 (C A B:cPLT false) (f:C → A) (g:C → B) :
  pi1 false ∘ pair false f g ≈ f.
Proof.
  split. apply pair_le_commute1.
  rewrite <- (cplt_hom_le false C A). simpl.
  unfold PLT.pair_map.
  rewrite PLT.pair_commute1.
  rewrite <- (cat_assoc PLT _ _ _ _ _ π₁%plt).
  rewrite PLT.pair_commute1.
  rewrite (cat_assoc PLT).
  rewrite (cplt_idem _ A).
  auto.
Qed.

Theorem pair_commute2 (C A B:cPLT false) (f:C → A) (g:C → B) :
  pi2 false ∘ pair false f g ≈ g.
Proof.
  split. apply pair_le_commute2.
  rewrite <- (cplt_hom_le false C B). simpl.
  unfold PLT.pair_map.
  rewrite PLT.pair_commute2.
  rewrite <- (cat_assoc PLT _ _ _ _ _ π₂%plt).
  rewrite PLT.pair_commute2.
  rewrite (cat_assoc PLT).
  rewrite (cplt_idem _ B).
  auto.
Qed.

Lemma terminate_univ : forall (A:cPLT false) (f:A → unit false),
  f ≈ terminate false A.
Proof.
  intros. 
  rewrite <- (cplt_hom_eq false A (unit false)). simpl.
  do 2 rewrite (cat_ident2 PLT).
  etransitivity.
  apply PLT.terminate_univ.
  symmetry. apply PLT.terminate_univ.
Qed.

Definition terminated_mixin
  := Terminated.Mixin (ob false) (hom false) 
       (hom_eq_mixin false)
       (unit false) (terminate false) terminate_univ.

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

Global Opaque compose.
Global Opaque pair.
Global Opaque sum_cases.
Global Opaque curry.  
Global Opaque app.

End cPLT.


Canonical Structure cPLT.cPLT.
Canonical Structure cPLT.ord.
Canonical Structure cPLT.dec.
Canonical Structure cPLT.hom_ord.
Canonical Structure cPLT.hom_eq.
Canonical Structure cPLT.comp.
Canonical Structure cPLT.homset_cpo.
Canonical Structure cPLT.cocartesian.
Canonical Structure cPLT.terminated.
Canonical Structure cPLT.cartesian.
Canonical Structure cPLT.cartesian_closed.

Arguments cPLT.hom [hf] A B.
Arguments cPLT.cplt_ob [hf] _.
Arguments cPLT.cplt_retract [hf] _.
Arguments cPLT.cplt_idem [hf] _.
Arguments cPLT.cplt_hom [hf A B] h.
Arguments cPLT.ord [hf] X.
Arguments cPLT.dec [hf] X.
Arguments cPLT.carrier [hf] X.
Arguments cPLT.pi1 [hf] [A] [B].
Arguments cPLT.pi2 [hf] [A] [B].
Arguments cPLT.pair [hf] [C] [A] [B] f g.
Arguments cPLT.iota1 [hf] [A] [B].
Arguments cPLT.iota2 [hf] [A] [B].
Arguments cPLT.sum_cases [hf] [C] [A] [B] f g.
Arguments cPLT.prod [hf] A B.
Arguments cPLT.sum [hf] A B.
Arguments cPLT.exp [hf] A B.
Arguments cPLT.app [hf A B].
Arguments cPLT.curry [hf C A B] f.
Arguments cPLT.pair_map [hf] [A B C D] f g.

Coercion cPLT.ord : cPLT.ob >-> preord.
Coercion cPLT.carrier : cPLT.ob >-> Sortclass.

Global Close Scope category_ops_scope.

Notation cPLT := (cPLT.cPLT false).
Notation "'c∂PLT'" := (cPLT.cPLT true).

Notation "0" := (cPLT.empty _) : cplt_scope.
Notation "1" := (cPLT.unit _) : cplt_scope.
Notation "'Λ' f" := (cPLT.curry f) : cplt_scope.
Notation apply := (@cPLT.app _ _ _).

Notation "〈 f , g 〉" := (@cPLT.pair false _ _ _ (f)%cplt (g)%cplt) : cplt_scope.
Notation "A × B" := (@cPLT.prod false (A)%cplt (B)%cplt) : cplt_scope.
Notation "A ⇒ B" := (@cPLT.exp false (A)%cplt (B)%cplt) : cplt_scope.
Notation "A + B" := (@cPLT.sum false (A)%cplt (B)%cplt) : cplt_scope.

Notation "《 f , g 》" := (@cPLT.pair true _ _ _ (f)%cplt (g)%cplt) : cplt_scope.
Notation "A ⊗ B" := (@cPLT.prod true (A)%cplt (B)%cplt) : cplt_scope.
Notation "A ⊸ B" := (@cPLT.exp true (A)%cplt (B)%cplt) : cplt_scope.
Notation "A ⊕ B" := (@cPLT.sum true (A)%cplt (B)%cplt) : cplt_scope.

Notation "'π₁'"  := (@cPLT.pi1 _ _ _) : cplt_scope.
Notation "'π₂'"  := (@cPLT.pi2 _ _ _) : cplt_scope.
Notation "'ι₁'"  := (@cPLT.iota1 _ _ _) : cplt_scope.
Notation "'ι₂'"  := (@cPLT.iota2 _ _ _) : cplt_scope.

Add Parametric Morphism (hf:bool) (C A B:cPLT.ob hf) :
    (@cPLT.pair hf C A B)
    with signature (Preord.ord_op (cPLT.hom_ord hf C A)) ==>
                   (Preord.ord_op (cPLT.hom_ord hf C B)) ==>
                   (Preord.ord_op (cPLT.hom_ord hf C (cPLT.prod A B)))
     as cplt_le_pair_morphism.
Proof.
  intros. apply cPLT.pair_mono; auto.
Qed.

Add Parametric Morphism (hf:bool) (C A B:cPLT.ob hf) :
    (@cPLT.sum_cases hf C A B)
    with signature (Preord.ord_op (cPLT.hom_ord hf A C)) ==>
                   (Preord.ord_op (cPLT.hom_ord hf B C)) ==>
                   (Preord.ord_op (cPLT.hom_ord hf (cPLT.sum A B) C))
     as cplt_le_cases_morphism.
Proof.
  intros. apply cPLT.sum_cases_mono; auto.
Qed.

Add Parametric Morphism (hf:bool) (C A B:cPLT.ob hf) :
    (@cPLT.pair hf C A B)
    with signature (eq_op (cPLT.hom_eq hf C A)) ==>
                   (eq_op (cPLT.hom_eq hf C B)) ==>
                   (eq_op (cPLT.hom_eq hf C (cPLT.prod A B)))
     as cplt_pair_morphism.
Proof.
  intros. apply cPLT.pair_eq; auto.
Qed.

Add Parametric Morphism (hf:bool) (C A B:cPLT.ob hf) :
    (@cPLT.sum_cases hf C A B)
    with signature (eq_op (cPLT.hom_eq hf A C)) ==>
                   (eq_op (cPLT.hom_eq hf B C)) ==>
                   (eq_op (cPLT.hom_eq hf (cPLT.sum A B) C))
     as cplt_cases_morphism.
Proof.
  intros. split; apply cplt_le_cases_morphism; auto.
Qed.

Add Parametric Morphism (hf:bool) (C A B:cPLT.ob hf) :
    (@cPLT.curry hf C A B)
    with signature (Preord.ord_op (cPLT.hom_ord hf (cPLT.prod C A) B)) ==>
                   (Preord.ord_op (cPLT.hom_ord hf C (cPLT.exp A B)))
     as cplt_le_curry_morphism.
Proof.
  intros. apply cPLT.curry_mono; auto.
Qed.

Add Parametric Morphism (hf:bool) (C A B:cPLT.ob hf) :
    (@cPLT.curry hf C A B)
    with signature (eq_op (cPLT.hom_eq hf (cPLT.prod C A) B)) ==>
                   (eq_op (cPLT.hom_eq hf C (cPLT.exp A B)))
     as cplt_curry_morphism.
Proof.
  intros. apply cPLT.curry_eq; auto.
Qed.

Lemma cplt_compose_unfold hf (A B C:cPLT.ob hf) (g:B → C) (f:A → B) :
  cPLT.cplt_hom (g ∘ f) = cPLT.cplt_hom g ∘ cPLT.cplt_retract B ∘ cPLT.cplt_hom f.
Proof.
  reflexivity.
Qed.

Lemma cplt_terminate_le_cancel (hf:bool) (A B:cPLT.cPLT hf) (f g:1 → B) (a a':A) :
  (a,a') ∈ PLT.hom_rel (cPLT.cplt_retract A) ->
  f ∘ cPLT.terminate hf A ≤ g ∘ cPLT.terminate hf A ->
  f ≤ g.
Proof.
  intros.
  rewrite <- cPLT.cplt_hom_le. simpl.
  rewrite <- cPLT.cplt_hom_le in H0. simpl in H0.
  rewrite <- (cat_assoc (PLT.PLT hf)).
  rewrite <- (cat_assoc (PLT.PLT hf)).
  rewrite (cat_ident1 (PLT.PLT hf)).
  rewrite (cat_ident1 (PLT.PLT hf)).
  do 2 rewrite cplt_compose_unfold in H0. simpl in H0.
  repeat rewrite (cat_ident1 (PLT.PLT hf)) in H0.
  hnf; intros [[] b] ?.
  repeat rewrite (cat_assoc (PLT.PLT hf)) in H0.
  assert ((a,b) ∈ PLT.hom_rel (
        cPLT.cplt_retract B ∘ cPLT.cplt_hom f ∘
        PLT.terminate hf (cPLT.cplt_ob A) ∘
        cPLT.cplt_retract A)).
  apply PLT.compose_hom_rel.
  exists a'. split; auto.
  apply PLT.compose_hom_rel.
  exists tt. split; auto.
  simpl. apply eprod_elem; split.
  apply eff_complete. apply single_axiom. auto.
  generalize (H0 (a,b) H2); intros.
  apply PLT.compose_hom_rel in H3.
  destruct H3 as [a'' [??]].
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [[] [??]].
  auto.
Qed.

Lemma cplt_terminate_cancel (hf:bool) (A B:cPLT.cPLT hf) (f g:1 → B) (a a':A) :
  (a,a') ∈ PLT.hom_rel (cPLT.cplt_retract A) ->
  f ∘ cPLT.terminate hf A ≈ g ∘ cPLT.terminate hf A ->
  f ≈ g.
Proof.
  intros. destruct H0.
  split.
  eapply cplt_terminate_le_cancel. eauto. auto.
  eapply cplt_terminate_le_cancel. eauto. auto.
Qed.


Definition cplt_const hf (A B:cPLT.cPLT hf) (b:B) :=
  cPLT.Hom hf A B (plt_const hf (cPLT.cplt_ob A) (cPLT.cplt_ob B) b).

Theorem pair_bottom1 (C A B:c∂PLT) (f:C → A) :
  《 f, ⊥ : C → B 》 ≈ ⊥.
Proof.
  split. 2: apply bottom_least.
  rewrite <- cPLT.cplt_hom_le.
  apply PLT.compose_mono; auto.
  apply PLT.compose_mono; auto.
  simpl.
  apply pair_bottom1.
Qed.

Theorem pair_bottom2 (C A B:c∂PLT) (g:C → B) :
  《 ⊥ : C → A,  g 》 ≈ ⊥.
Proof.
  split. 2: apply bottom_least.
  rewrite <- cPLT.cplt_hom_le.
  apply PLT.compose_mono; auto.
  apply PLT.compose_mono; auto.
  simpl.
  apply pair_bottom2.
Qed.

Theorem pi1_greatest (A B:c∂PLT) (proj:A⊗B → A) :
  (forall C (f:C → A) (g:C → B), proj ∘ 《f, g》 ≤ f) ->
  proj ≤ π₁.
Proof.
  repeat intro.
  destruct a as [[a b] a']. simpl in *.
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [[a2 b2] [??]].
  rewrite (hom_rel_pair_map _ _ _ _ _ _ _ a b a2 b2) in H0.
  destruct H0.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [a3 [??]].
  
  assert ((b,a') ∈ PLT.hom_rel
           (cPLT.cplt_retract A ∘ cPLT.cplt_hom (cplt_const true B A a) ∘
             cPLT.cplt_retract B)).
  apply (H B (cplt_const _ _ _ a) (id) (b,a')).
  destruct (cPLT.cplt_idem B).
  generalize (H5 (b,b2) H2); clear H4 H5; intro.
  apply PLT.compose_hom_rel in H4. destruct H4 as [b3 [??]].
  apply PLT.compose_hom_rel.
  exists b3; split; auto.
  apply PLT.compose_hom_rel.
  exists a3; split; auto.
  rewrite cplt_compose_unfold.
  apply PLT.compose_hom_rel.
  exists (a,b3). split.
  apply PLT.pair_hom_rel.
  split; simpl.
  apply plt_const_rel_elem. auto.
  apply ident_elem. auto.
  apply PLT.compose_hom_rel.
  exists (a2,b2). split; auto.
  simpl.
  apply hom_rel_pair_map. split; auto.
  
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [b' [??]].
  apply PLT.compose_hom_rel in H5.
  destruct H5 as [aq [??]].
  simpl in H5. 
  rewrite plt_const_rel_elem in H5.

  destruct (cPLT.cplt_idem A).
  generalize (H8 (aq,a') H6); clear H7 H8; intro.
  apply PLT.compose_hom_rel in H7.
  destruct H7 as [aq' [??]].
  apply PLT.compose_hom_rel.
  exists (aq',b2).
  split.
  simpl.
  apply hom_rel_pair_map. split; auto.
  apply PLT.hom_order with aq aq'; auto.
  apply PLT.compose_hom_rel.
  exists aq'. split; auto.
  simpl. apply pi1_rel_elem. auto.
Qed.

Theorem pi2_greatest (A B:c∂PLT) (proj:A⊗B → B) :
  (forall C (f:C → A) (g:C → B), proj ∘ 《f, g》 ≤ g) ->
  proj ≤ π₂.
Proof.
  repeat intro.
  destruct a as [[a b] b']. simpl in *.
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [[a2 b2] [??]].
  rewrite (hom_rel_pair_map _ _ _ _ _ _ _ a b a2 b2) in H0.
  destruct H0.
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [b3 [??]].
  
  assert ((a,b') ∈ PLT.hom_rel
           (cPLT.cplt_retract B ∘ cPLT.cplt_hom (cplt_const true A B b) ∘
             cPLT.cplt_retract A)).
  apply (H A (id) (cplt_const _ _ _ b) (a,b')).
  destruct (cPLT.cplt_idem A).
  generalize (H5 (a,a2) H0); clear H4 H5; intro.
  apply PLT.compose_hom_rel in H4. destruct H4 as [a3 [??]].
  apply PLT.compose_hom_rel.
  exists a3; split; auto.
  apply PLT.compose_hom_rel.
  exists b3; split; auto.
  rewrite cplt_compose_unfold.
  apply PLT.compose_hom_rel.
  exists (a3,b). split.
  apply PLT.pair_hom_rel.
  split; simpl.
  apply ident_elem. auto.
  apply plt_const_rel_elem. auto.
  apply PLT.compose_hom_rel.
  exists (a2,b2). split; auto.
  simpl.
  apply hom_rel_pair_map. split; auto.
  
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [a' [??]].
  apply PLT.compose_hom_rel in H5.
  destruct H5 as [bq [??]].
  simpl in H5. 
  rewrite plt_const_rel_elem in H5.

  destruct (cPLT.cplt_idem B).
  generalize (H8 (bq,b') H6); clear H7 H8; intro.
  apply PLT.compose_hom_rel in H7.
  destruct H7 as [bq' [??]].
  apply PLT.compose_hom_rel.
  exists (a2,bq').
  split.
  simpl.
  apply hom_rel_pair_map. split; auto.
  apply PLT.hom_order with bq bq'; auto.
  apply PLT.compose_hom_rel.
  exists bq'. split; auto.
  simpl. apply pi2_rel_elem. auto.
Qed.


Definition antistrict (A B:c∂PLT) (f:A → B) :=
  forall a a', (a,a') ∈ PLT.hom_rel (cPLT.cplt_retract A) ->
    exists b, (a,b) ∈ PLT.hom_rel (cPLT.cplt_retract B ∘ cPLT.cplt_hom f ∘ cPLT.cplt_retract A).
Arguments antistrict [A B] f.
    
Definition nonbottom (A B:c∂PLT) (f:A → B) :=
  profinite.nonbottom (cPLT.cplt_retract B ∘ cPLT.cplt_hom f ∘ cPLT.cplt_retract A).
Arguments nonbottom [A B] f.

Lemma antistrict_nonbottom (A B:c∂PLT) (f:A → B) :
  antistrict f <-> (forall C (g:C → A), nonbottom g -> nonbottom (f ∘ g)).
Proof.
  split; intros.
  unfold antistrict in H.
  hnf in H0.

  destruct H0 as [[c a] ?].
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [c' [??]].
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [a' [??]].
  destruct (H a' a) as [b ?]; auto.
  red. rewrite cplt_compose_unfold.
  red. simpl.
  exists (c, b).
  apply PLT.compose_hom_rel.
  exists c'; split; auto.
  apply PLT.compose_hom_rel in H3.
  destruct H3 as [q1 [??]].
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [q2 [??]].
  apply PLT.compose_hom_rel.
  exists q2; split; auto.
  apply PLT.compose_hom_rel.
  exists a'; split; auto.
  apply PLT.compose_hom_rel.
  exists q1; split; auto.

  red; simpl; intros.
  destruct (H A (cplt_const true A A a)).
  red. simpl.
  exists (a,a').
  apply PLT.compose_hom_rel.
  exists a'. split; auto.
  apply PLT.compose_hom_rel.
  exists a. split; auto.
  simpl.
  apply plt_const_rel_elem. auto.
  destruct x as [m n].
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [q1 [??]].
  apply PLT.compose_hom_rel in H2.
  destruct H2 as [q2 [??]].
  rewrite cplt_compose_unfold in H2.
  apply PLT.compose_hom_rel in H2.
  destruct H2 as [q3 [??]].
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [q4 [??]].
  simpl in H2.
  apply plt_const_rel_elem in H2.
  exists n.
  apply PLT.compose_hom_rel.
  exists q4. split.
  apply PLT.hom_order with q3 q4; auto.
  apply PLT.compose_hom_rel.
  exists q2. split; auto.
Qed.

Theorem antistrict_pair_commute1 (C B:c∂PLT) (g:C → B) :
  antistrict g <-> forall A (f:C → A), π₁ ∘ 《f,g》 ≈ f.
Proof.
  intros.
  split; repeat intro.
  split. apply cPLT.pair_le_commute1.
  hnf; intros.
  destruct a as [c a].
  apply PLT.compose_hom_rel.
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [c' [??]].
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [a' [??]].
  destruct (H c c') as [b ?]; auto.
  apply PLT.compose_hom_rel in H3.
  destruct H3 as [c'' [??]].
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [b' [??]].
  destruct (PLT.hom_directed _ _ _ (cPLT.cplt_retract C) c (c'::c''::nil)%list) as [cz [??]].
  exists c'. apply cons_elem; auto.
  red; intros.
  apply erel_image_elem.
  apply cons_elem in H6. destruct H6.
  apply PLT.hom_order with c c'; auto.
  apply cons_elem in H6. destruct H6.
  apply PLT.hom_order with c c''; auto.
  apply nil_elem in H6. elim H6.
  apply erel_image_elem in H7.
  destruct (cPLT.cplt_idem A).
  generalize (H9 (a',a) H2). clear H8 H9.
  intros. apply PLT.compose_hom_rel in H8.
  destruct H8 as [a'' [??]].
  destruct (cPLT.cplt_idem B).
  generalize (H11 (b',b) H5). clear H10 H11.
  intros. apply PLT.compose_hom_rel in H10.
  destruct H10 as [b'' [??]].

  exists cz. split; auto.
  apply PLT.compose_hom_rel.
  exists a''. split; auto.
  apply PLT.compose_hom_rel.
  exists (a',b'). split.
  apply PLT.pair_hom_rel. split; auto.
  apply PLT.hom_order with c' a'; auto.
  apply H6. apply cons_elem; auto.
  apply PLT.hom_order with c'' b'; auto.
  apply H6. apply cons_elem; right. apply cons_elem; auto.
  apply PLT.compose_hom_rel. 
  exists (a'',b'').
  split.
  simpl.
  apply hom_rel_pair_map. split; auto.
  simpl. apply pi1_rel_elem. auto.
  
  destruct (H C id).
  red in H2. simpl in H2.
  rewrite (cat_ident1 (∂PLT)) in H2.
  rewrite (cPLT.cplt_idem C) in H2.
  generalize (H2 (a,a') H0). intros.
  apply PLT.compose_hom_rel in H3.
  destruct H3 as [c1 [??]].
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [c2 [??]].
  rewrite cplt_compose_unfold in H4.
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [c3 [??]].
  destruct c3.
  rewrite (PLT.pair_hom_rel true (cPLT.cplt_ob C) (cPLT.cplt_ob B) (cPLT.cplt_ob C) 
                            id(_) (cPLT.cplt_hom g) c1 c c0) in H4.
  destruct H4.
  simpl in H4. apply ident_elem in H4.
  apply PLT.compose_hom_rel in H6.
  destruct H6 as [q [??]].
  simpl in H8.
  destruct q.
  rewrite (pi1_rel_elem _ _ _ _ c3 c4 c2) in H8.
  simpl in H6.
  rewrite (hom_rel_pair_map  _ _ _ _ _ _ _ c c0 c3 c4) in H6.
  destruct H6.
  exists c4.
  apply PLT.compose_hom_rel.
  exists c1. split; auto.
  apply PLT.compose_hom_rel.
  exists c0. split; auto.
Qed.

Theorem antistrict_pair_commute2 (C A:c∂PLT) (f:C → A) :
  antistrict f <-> forall B (g:C → B), π₂ ∘ 《f, g》 ≈ g.
Proof.
  intros.
  split; repeat intro.
  split. apply cPLT.pair_le_commute2.
  hnf; intros.
  destruct a as [c b].
  apply PLT.compose_hom_rel.
  apply PLT.compose_hom_rel in H0.
  destruct H0 as [c' [??]].
  apply PLT.compose_hom_rel in H1.
  destruct H1 as [b' [??]].
  destruct (H c c') as [a ?]; auto.
  apply PLT.compose_hom_rel in H3.
  destruct H3 as [c'' [??]].
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [a' [??]].
  destruct (PLT.hom_directed _ _ _ (cPLT.cplt_retract C) c (c'::c''::nil)%list) as [cz [??]].
  exists c'. apply cons_elem; auto.
  red; intros.
  apply erel_image_elem.
  apply cons_elem in H6. destruct H6.
  apply PLT.hom_order with c c'; auto.
  apply cons_elem in H6. destruct H6.
  apply PLT.hom_order with c c''; auto.
  apply nil_elem in H6. elim H6.
  apply erel_image_elem in H7.
  destruct (cPLT.cplt_idem A).
  generalize (H9 (a',a) H5). clear H8 H9.
  intros. apply PLT.compose_hom_rel in H8.
  destruct H8 as [a'' [??]].
  destruct (cPLT.cplt_idem B).
  generalize (H11 (b',b) H2). clear H10 H11.
  intros. apply PLT.compose_hom_rel in H10.
  destruct H10 as [b'' [??]].

  exists cz. split; auto.
  apply PLT.compose_hom_rel.
  exists b''. split; auto.
  apply PLT.compose_hom_rel.
  exists (a',b'). split.
  apply PLT.pair_hom_rel. split; auto.
  apply PLT.hom_order with c'' a'; auto.
  apply H6. apply cons_elem; right. apply cons_elem; auto.
  apply PLT.hom_order with c' b'; auto.
  apply H6.
  apply cons_elem; auto.
  apply PLT.compose_hom_rel. 
  exists (a'',b'').
  split.
  simpl.
  apply hom_rel_pair_map. split; auto.
  simpl. apply pi2_rel_elem. auto.
  
  destruct (H C id).
  red in H2. simpl in H2.
  rewrite (cat_ident1 (∂PLT)) in H2.
  rewrite (cPLT.cplt_idem C) in H2.
  generalize (H2 (a,a') H0). intros.
  apply PLT.compose_hom_rel in H3.
  destruct H3 as [c1 [??]].
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [c2 [??]].
  rewrite cplt_compose_unfold in H4.
  apply PLT.compose_hom_rel in H4.
  destruct H4 as [c3 [??]].
  destruct c3.
  rewrite (PLT.pair_hom_rel true (cPLT.cplt_ob A) (cPLT.cplt_ob C) (cPLT.cplt_ob C) 
                            (cPLT.cplt_hom f) id(_)  c1 c c0) in H4.
  destruct H4.
  simpl in H7. apply ident_elem in H7.
  apply PLT.compose_hom_rel in H6.
  destruct H6 as [q [??]].
  simpl in H8.
  destruct q.
  rewrite (pi2_rel_elem _ _ _ _ c3 c4 c2) in H8.
  simpl in H6.
  rewrite (hom_rel_pair_map  _ _ _ _ _ _ _ c c0 c3 c4) in H6.
  destruct H6.
  exists c3.
  apply PLT.compose_hom_rel.
  exists c1. split; auto.
  apply PLT.compose_hom_rel.
  exists c. split; auto.
Qed.
