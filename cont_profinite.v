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

Delimit Scope cont_plt_scope with cplt.
Open Scope cont_plt_scope.

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
  Next Obligation.
    intros; auto.
  Qed.
  Next Obligation.
    intros. etransitivity; eauto.
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
          (PLT.iota1 ∘ cplt_retract A) (PLT.iota2 _ _ _ ∘ cplt_retract B))
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

  Definition terminate A : A → unit :=
    Hom A unit (PLT.terminate hf (cplt_ob A)).

  Definition initiate A : empty → A :=
    Hom empty A (PLT.initiate hf (cplt_ob A)).

  Definition app {A B} : (prod (exp A B) A) → B :=
    Hom (prod (exp A B) A) B  (@PLT.app hf (cplt_ob A) (cplt_ob B)).

  Definition curry {C A B} (f:(prod C A) → B) : C → (exp A B) :=
    Hom C (exp A B) (PLT.curry (cplt_hom f)).

  Definition pair {C A B} (f:C → A) (g:C → B) : C → (prod A B) :=
    Hom C (prod A B) (PLT.pair (cplt_hom f) (cplt_hom g)).

  Definition pi1 {A B} : (prod A B) → A :=
    Hom (prod A B) A (PLT.pi1). (* ∘ PLT.pair_map (cplt_retract A) (cplt_retract B)).*)

  Definition pi2 {A B} : (prod A B) → B :=
    Hom (prod A B) B (PLT.pi2). (* ∘ PLT.pair_map (cplt_retract A) (cplt_retract B)).*)

  Definition iota1 A B : A → (sum A B) :=
    Hom A (sum A B) (PLT.iota1).

  Definition iota2 A B : B → (sum A B) :=
    Hom B (sum A B) (PLT.iota2 _ _ _).

  Definition sum_cases {C A B} (f:A → C) (g:B → C) : (sum A B) → C :=
    Hom (sum A B) C (PLT.sum_cases (cplt_hom f) (cplt_hom g)).

  Definition pair_map {A B C D} (f:A → C) (g:B → D) : (prod A B) → (prod C D) :=
    pair (f ∘ pi1) (g ∘ pi2).

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
  Admitted.

(*
    intros.
    rewrite <- cplt_hom_le. simpl.
    rewrite <- cplt_hom_le in H. 
    rewrite <- cplt_hom_le in H0.
    rewrite <- (PLT.pair_map_pair hf).
    rewrite (PLT.pair_compose_commute hf).
    etransitivity.
    2: apply PLT.pair_mono; [ apply H | apply H0 ].
    simpl.
    unfold PLT.pair_map.
    rewrite (PLT.pair_compose_commute hf).
    rewrite (PLT.pair_compose_commute hf).
    apply PLT.pair_mono.    
    
    repeat rewrite (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. reflexivity.
    apply PLT.compose_mono. reflexivity.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    etransitivity.
    apply PLT.compose_mono. 2: reflexivity.
    apply PLT.compose_mono. reflexivity.

    rewrite (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. reflexivity.
    apply PLT.pair_le_commute1.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem A).
    auto.
    unfold PLT.pair_map.
    etransitivity.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. 2: reflexivity.
    rewrite (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. reflexivity.
    apply PLT.pair_le_commute2.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem B).
    auto.


    rewrite H. rewrite H0.
    
    apply pair_rel_universal_le.
    apply hom_order.
    apply hom_order.
    apply hom_order.
  Qed.
*)

  Theorem pair_universal C A B (f:C → A) (g:C → B) (PAIR:C → (prod A B)) :
    pi1 ∘ PAIR ≈ f -> pi2 ∘ PAIR ≈ g -> PAIR ≈ pair f g.
  Proof.
    intros.
    rewrite <- cplt_hom_eq. simpl.
    rewrite <- cplt_hom_eq in H. 
    rewrite <- cplt_hom_eq in H0.
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
        ≈
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
    
    split.
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

    apply PLT.pair_mono.
    unfold PLT.pair_map.
    etransitivity.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. 2: reflexivity.
    rewrite (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. reflexivity.
    apply PLT.pair_le_commute1.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cplt_idem A).
    auto.
    unfold PLT.pair_map.
    etransitivity.
    repeat rewrite <- (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. 2: reflexivity.
    rewrite (cat_assoc (PLT.PLT hf)).
    apply PLT.compose_mono. reflexivity.
    apply PLT.pair_le_commute2.
    rewrite (cat_assoc (PLT.PLT hf)).
    rewrite (cat_assoc (PLT.PLT hf)).
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


End cPLT.
End cPLT.
