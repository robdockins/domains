Require Import Relations.
Require Import List.

Require Import basics.
Require Import preord.
Require Import categories.

Module set.
Section mixin_def.
  Variable set : preord -> Type.
  Variable member : forall (A:preord), A -> set A -> Prop.
  Variable single : forall (A:preord), A -> set A.
  Variable image : forall (A B:preord) (f:A → B), set A -> set B.

  Let incl A X Y := forall a, member A a X -> member A a Y.

  Program Definition set_preord (A:preord) : preord :=
    Preord.Pack (set A) (Preord.Mixin _ (@incl A) _ _).
  Next Obligation.
    hnf; auto.
  Qed.
  Next Obligation.
    hnf; intros. apply H0. apply H. auto.
  Qed.

  Variable union : forall A:preord, set (set_preord A) -> set A.

  Record mixin_of :=
    Mixin
      {  member_eq : forall (A:preord) (a b:A) (X:set A),
          a ≈ b -> member A a X -> member A b X

      ; single_axiom : forall (A:preord) (a b:A),
          member A a (single A b) <-> a ≈ b

      ; union_axiom : forall (A:preord) (XS:set (set_preord A)) (a:A),
          member A a (union A XS) <->
          exists X:set A, member (set_preord A) X XS /\ member A a X

      ; image_axiom0 : forall (A B C:preord) (f:A → B) (g:B → C) (X:set A) (c:C),
          member C c (image A C (g ∘ f) X) <->
          member C c (image B C g (image A B f X))
      ; image_axiom1 : forall (A B:preord) (f:A → B) (P:set A) (x:A),
          member A x P -> member B (f#x) (image A B f P)
      ; image_axiom2 : forall (A B:preord) (f:A → B) (P:set A) (x:B),
          member B x (image A B f P) ->
            exists y, member A y P /\ x ≈ f#y
      }.
End mixin_def.

Record theory :=
  Theory
  { set : preord -> Type
  ; member : forall (A:preord), A -> set A -> Prop
  ; single : forall (A:preord), A -> set A
  ; image : forall (A B:preord) (f:A → B), set A -> set B
  ; union : forall A:preord, set (set_preord set member A) -> set A
  ; mixin :> mixin_of set member single image union
  }.
End set.
Arguments set.image [t] [A] [B] f X.
Arguments set.single [t] [A] x.
Arguments set.member [t] [A] a X : simpl never.

Definition set_preord (T:set.theory) (A:preord) :=
  set.set_preord (set.set T) (@set.member T) A.
Canonical Structure set_preord.

Notation set := set_preord.
Notation single := set.single.
Notation image := set.image.
Notation "x ∈ X" := (@set.member _ _ x X) (at level 60).
Notation "x ∉ X"  := (not (@set.member _ _ x X)) (at level 60).

Definition incl {A:preord} {XSL YSL:set.theory} (X:set XSL A) (Y:set YSL A) :=
  forall a:A, a ∈ X -> a ∈ Y.

Notation "X ⊆ Y" := (@incl _ _ _ X Y) (at level 66).

Definition union {T:set.theory} {A:preord} (XS:set T (set T A)) : set T A :=
  set.union T A XS.

Notation "∪ XS" := (@union _ _ XS) (at level 50).

Lemma member_eq : forall (T:set.theory) (A:preord) (a b:A) (X:set T A),
  a ≈ b -> a ∈ X -> b ∈ X.
Proof.
  intro T. apply (set.member_eq _ _ _ _ _ (set.mixin T)).
Qed.

Lemma single_axiom : forall (T:set.theory) (A:preord) (a b:A),
  a ∈ @set.single T A b <-> a ≈ b.
Proof.
  intro T. apply (set.single_axiom _ _ _ _ _ (set.mixin T)).
Qed.

Lemma union_axiom : forall (T:set.theory) (A:preord) (XS:set T (set T A)) (a:A),
  a ∈ ∪XS <-> exists X, X ∈ XS /\ a ∈ X.
Proof.
  intro T. apply (set.union_axiom _ _ _ _ _ (set.mixin T)).
Qed.

Lemma image_axiom0 : forall (T:set.theory)
  (A B C:preord) (f:A → B) (g:B → C) (X:set T A) (c:C),
          c ∈ image (g ∘ f) X <-> c ∈ image g (image f X).
Proof.
  intro T. apply (set.image_axiom0 _ _ _ _ _ (set.mixin T)).
Qed.

Lemma image_axiom1 : forall (T:set.theory)
  (A B:preord) (f:A → B) (P:set T A) (x:A),
  x ∈ P -> f#x ∈ image f P.
Proof.
  intro T. apply (set.image_axiom1 _ _ _ _ _ (set.mixin T)).
Qed.

Lemma image_axiom2 : forall (T:set.theory)
  (A B:preord) (f:A → B) (P:set T A) (x:B),
  x ∈ image f P -> exists y, y ∈ P /\ x ≈ f#y.
Proof.
  intro T. apply (set.image_axiom2 _ _ _ _ _ (set.mixin T)).
Qed.

Require Import Setoid.
Require Import Coq.Program.Basics.

Add Parametric Morphism (T:set.theory) (A:preord) :
  (@set.member T A)
   with signature (eq_op (Preord_Eq A)) ==>
                  (eq_op (Preord_Eq (set T A))) ==>
                  iff
    as member_morphism.
Proof.
  intros. split; intros.
  destruct H0. apply H0. eapply member_eq; eauto.
  destruct H0. apply H2. eapply member_eq. symmetry. apply H.
  auto.
Qed.  

Add Parametric Morphism (T:set.theory) (A:preord) :
  (@set.member T A)
   with signature (eq_op (Preord_Eq A)) ==>
                  (@Preord.ord_op (set T A)) ==>
                  impl
    as member_incl_morphism.
Proof.
  intros. red; intros.
  apply H0. eapply member_eq; eauto.
Qed.  

Add Parametric Morphism (T1 T2:set.theory) (A:preord) :
  (@incl A T1 T2)
   with signature (eq_op (Preord_Eq (set T1 A))) ==>
                  (eq_op (Preord_Eq (set T2 A))) ==>
                  iff
    as incl_morphism.
Proof.
  repeat intro. split; repeat intro.
  destruct H0. apply H0.
  apply H1.
  destruct H. apply H4. auto.
  destruct H0. apply H3.
  apply H1.
  destruct H. apply H. auto.
Qed.
  
Add Parametric Morphism (T1 T2:set.theory) (A:preord) :
  (@incl A T1 T2)
   with signature (Preord.ord_op (set T1 A)) -->
                  (Preord.ord_op (set T2 A)) ++>
                  impl
    as incl_ord_morphism.
Proof.
  repeat intro.
  apply H0. apply H1. apply H. auto.
Qed.

Lemma incl_refl (T:set.theory) (A:preord) (X:set T A) : X ⊆ X.
Proof.
  red; auto.
Qed.

Lemma incl_trans (T1 T2 T3:set.theory) (A:preord)
  (X:set T1 A) (Y:set T2 A) (Z:set T3 A) :
  X ⊆ Y -> Y ⊆ Z -> X ⊆ Z.
Proof.
  unfold incl. intuition.
Qed.

Add Parametric Relation (T:set.theory) (A:preord) : (set T A) (@incl A T T)
  reflexivity proved by (incl_refl T A)
  transitivity proved by (incl_trans T T T A)
  as incl_rel.

Add Parametric Morphism (T:set.theory) (A:preord) :
  (@incl A T T)
   with signature (@incl A T T) -->
                  (@incl A T T) ++>
                  impl
    as incl_incl_morphism.
Proof.
  repeat intro.
  apply H0. apply H1. apply H. auto.
Qed.

Add Parametric Morphism (T:set.theory) (A:preord) (B:preord) :
  (@image T A B)
    with signature (eq_op (Preord_Eq (hom_order A B))) ==>
                   (eq_op (Preord_Eq (set T A))) ==>
                   (eq_op (Preord_Eq (set T B)))
     as image_morphism.
Proof.
  intros. split. red. simpl; intros.
  apply image_axiom2 in H1.
  destruct H1 as [z [??]].
  rewrite H2.
  apply member_eq with ((y:hom _ A B) #z).
  destruct H. split.
  apply H3. apply H.
  apply image_axiom1.
  destruct H0. apply H0. auto.

  red. simpl; intros.
  apply image_axiom2 in H1.
  destruct H1 as [z [??]].
  rewrite H2.
  apply member_eq with ((x:hom _ A B) #z).
  destruct H. split.
  apply H. apply H3.
  apply image_axiom1.
  destruct H0. apply H3. auto.
Qed.

Add Parametric Morphism (T:set.theory) (A:preord) (B:preord) :
  (@image T A B)
    with signature (eq_op (Preord_Eq (hom_order A B))) ==>
                   (Preord.ord_op (set T A)) ==>
                   (Preord.ord_op (set T B))
     as image_ord_morphism.
Proof.
  repeat intro.
  apply image_axiom2 in H1.
  destruct H1 as [z [??]].
  rewrite H2.
  apply member_eq with ((y:hom _ A B) #z).
  destruct H; split.
  apply H3. apply H.
  apply image_axiom1.
  apply H0. auto.
Qed.

Add Parametric Morphism (T:set.theory) (A:preord) : 
  (@union T A)
    with signature (eq_op (Preord_Eq (set T (set T A)))) ==>
                   (eq_op (Preord_Eq (set T A)))
     as union_morphism.
Proof.
  intros. split; repeat intro.
  apply union_axiom in H0.
  apply union_axiom.
  destruct H0 as [X [??]].
  exists X. split; auto.
  rewrite <- H; auto.
  apply union_axiom in H0.
  apply union_axiom.
  destruct H0 as [X [??]].
  exists X. split; auto.
  rewrite H; auto.
Qed.

Add Parametric Morphism (T:set.theory) (A:preord) : 
  (@union T A)
    with signature (Preord.ord_op (set T (set T A))) ++>
                   (Preord.ord_op (set T A))
     as union_ord_morphism.
Proof.
  repeat intro.
  apply union_axiom in H0.
  apply union_axiom.
  destruct H0 as [X [??]].
  exists X. split; auto.
Qed.

Record set_dec (T:set.theory) (A:preord) :=
  Setdec
  { setdec :> forall (x:A) (X:set T A), { x ∈ X } + { x ∉ X } }.




Definition lower_set {T:set.theory} {A:preord} (X:set T A) :=
  forall (a b:A), a ≤ b -> b ∈ X -> a ∈ X.

Definition upper_set {T:set.theory} {A:preord} (X:set T A) :=
  forall (a b:A), a ≤ b -> a ∈ X -> b ∈ X.

Definition upper_bound 
  {T:set.theory} {A:preord}
  (ub:A) (X:set T A) :=
  forall x, x ∈ X -> x ≤ ub.

Definition lower_bound 
  {T:set.theory} {A:preord}
  (lb:A) (X:set T A) :=
  forall x, x ∈ X -> lb ≤ x.

Definition minimal_upper_bound
  {T:set.theory} {A:preord}
  (mub:A) (X:set T A) :=
  upper_bound mub X /\
  (forall b, upper_bound b X -> b ≤ mub -> mub ≤ b).
  
Definition maximal_lower_bound
  {T:set.theory} {A:preord}
  (mlb:A) (X:set T A) :=
  lower_bound mlb X /\
  (forall b, lower_bound b X -> mlb ≤ b -> b ≤ mlb).

Definition least_upper_bound 
  {T:set.theory} {A:preord}
  (lub:A) (X:set T A) :=
  upper_bound lub X /\
  (forall b, upper_bound b X -> lub ≤ b).

Definition greatest_lower_bound
  {T:set.theory} {A:preord}
  (glb:A) (X:set T A) :=
  lower_bound glb X /\
  (forall b, lower_bound b X -> b ≤ glb).



Record color :=
  Color
  { color_prop : forall (T:set.theory) (A:preord) (X:set T A), Prop
  ; color_eq : forall (T:set.theory) (A:preord) (X Y:set T A),
        X ≈ Y -> color_prop T A X -> color_prop T A Y
  ; color_single : forall (T:set.theory) (A:preord) (a:A),
        color_prop T A (single a)
  ; color_image : forall (T:set.theory) (A B:preord) (f:A → B) (X:set T A),
        color_prop T A X -> color_prop T B (image f X)
  ; color_union : forall (T:set.theory) (A:preord) (XS:set T (set T A)),
        color_prop T (set T A) XS ->
        (forall X:set T A, X ∈ XS -> color_prop T A X) ->
        color_prop T A (∪XS)
  }.
Arguments color_prop c [T] [A] X.

(* Doesn't follow union law??
Program Definition color_or (C1 C2:color) : color :=
  Color (fun SL A X => color_prop C1 X \/ color_prop C2 X) _ _.
Next Obligation.
  destruct H; [ left | right ]; apply color_image; auto.
Qed.
Next Obligation.
*)

Program Definition color_and (C1 C2:color) : color :=
  Color (fun SL A X => color_prop C1 X /\ color_prop C2 X) _ _ _ _.
Next Obligation.
  split; eapply color_eq; eauto.
Qed.
Next Obligation.
  split; apply color_single; auto.
Qed.
Next Obligation.
  split; apply color_image; auto.
Qed.
Next Obligation.
  split.
  apply color_union; auto.
  intros. apply H0; auto.
  apply color_union.
  auto.
  intros. apply H0; auto.
Qed.  

(* fails to satisfy the singleton axiom...
Program Definition is_empty : color :=
  Color (fun SL A X => forall x, x ∈ X -> False) _ _ _.
Next Obligation.
  apply (H0 x).
  apply H. auto.
Qed.
Next Obligation.
  apply image_axiom2 in H0. destruct H0 as [y [??]].
  apply (H y); auto.
Qed.
Next Obligation.
  apply union_axiom in H1.
  destruct H1 as [X [??]].
  apply (H X); auto.
Qed.
*)
  
Program Definition inhabited : color :=
  Color (fun SL A X => exists a:A, a ∈ X) _ _ _ _.
Next Obligation.
  exists H0. apply H; auto.
Qed.
Next Obligation.
  exists a. apply single_axiom. auto.
Qed.
Next Obligation.
  exists (Preord.map A B f H).
  apply image_axiom1; auto.
Qed.
Next Obligation.
  destruct (H0 H) as [x ?]; auto.
  exists x. apply union_axiom; auto.
  eauto.
Qed.  

Obligation Tactic := idtac.

Program Definition semidirected : color :=
  Color (fun SL A X => 
    forall a b, a ∈ X -> b ∈ X ->
      exists c, c ∈ X /\ a ≤ c /\ b ≤ c)
  _ _ _ _.
Next Obligation.
  intros.
  destruct (H0 a b) as [c [?[??]]].
  apply H; auto.
  apply H; auto.
  exists c; split; auto.
  apply H; auto.
Qed.
Next Obligation.
  intros.
  apply single_axiom in H.
  apply single_axiom in H0.
  exists a.
  split; auto.
  apply single_axiom. auto.
Qed.
Next Obligation.
  intros.
  apply image_axiom2 in H0.
  apply image_axiom2 in H1.
  destruct H0 as [x [??]].
  destruct H1 as [y [??]].
  destruct (H x y) as [z [?[??]]]; auto.
  exists (f#z).
  split.
  apply image_axiom1. auto.
  split.
  transitivity (f#x); auto.
  transitivity (f#y); auto.
Qed.
Next Obligation.
  intros.
  apply union_axiom in H1.
  apply union_axiom in H2.
  destruct H1 as [X [??]].
  destruct H2 as [Y [??]].
  destruct (H X Y) as [Z [?[??]]]; auto.
  destruct (H0 Z H5 a b) as [c [?[??]]].
  apply H6; auto.
  apply H7; auto.
  exists c. split; auto.
  apply union_axiom; eauto.
Qed.

Definition directed := color_and inhabited semidirected.

Module colored_sets.
Section colored_sets.
  Variable T:set.theory.
  Variable C:color.

  Definition cset A := { X:set T A | color_prop C X }.
  Definition csingle A a : cset A := exist _ (single a) (color_single C T A a).
  Definition cmember A a (X:cset A) := a ∈ proj1_sig X.
  Definition cimage (A B:preord) (f:A → B) (X:cset A) :=
    exist _ (image f (proj1_sig X))
            (color_image C T A B f (proj1_sig X) (proj2_sig X)).

  Program Definition forget_color (A:preord) : (set.set_preord cset cmember A → set_preord T A) :=
    Preord.Hom (set.set_preord cset cmember A) (set_preord T A) (fun X => proj1_sig X) _.
  Next Obligation.
    auto.
  Qed.    

  Section cunion.
    Variable A:preord.
    Variable XS:cset (set.set_preord cset cmember A).

    Program Definition cunion : cset A :=
      exist _ (union (image (forget_color _) XS)) _.
    Next Obligation.
      apply color_union; auto.
      apply color_image. apply proj2_sig.
      intros.
      apply image_axiom2 in H.
      destruct H as [Y [??]].
      eapply color_eq.
      symmetry; apply H0.
      simpl. apply proj2_sig.
    Qed.
  End cunion.

  Program Definition mixin :
    set.mixin_of cset cmember csingle cimage cunion :=
    set.Mixin _ _ _ _ _ _ _ _ _ _ _.
  Next Obligation.
    intros. apply member_eq with a; auto.
  Qed.
  Next Obligation.
    unfold cmember, csingle. simpl; intros.
    apply single_axiom.
  Qed.
  Next Obligation.    
    intros.
    unfold cmember.
    unfold cunion at 1. simpl.
    rewrite union_axiom.
    intuition.
    destruct H as [X [??]].
    apply image_axiom2 in H.
    destruct H as [Y [??]].
    exists Y. split; auto.
    simpl in H1.
    destruct H1. apply H1. auto.
    destruct H as [X [??]].
    exists (proj1_sig X).
    split; auto.
    apply (image_axiom1 T _ _ (forget_color _)); auto.
  Qed.
  Next Obligation.
    unfold cmember, cimage. simpl.
    intros. apply (image_axiom0 T).
  Qed.
  Next Obligation.
    unfold cmember, cimage. simpl.
    intros. apply (image_axiom1 T). auto.
  Qed.
  Next Obligation.
    unfold cmember, cimage. simpl.
    intros. apply (image_axiom2 T). auto.
  Qed.
End colored_sets.
End colored_sets.
  
Canonical Structure cset_theory (T:set.theory) (CL:color) :=
  set.Theory 
     (colored_sets.cset T CL)
     (colored_sets.cmember T CL)
     (colored_sets.csingle T CL)
     (colored_sets.cimage T CL)
     (colored_sets.cunion T CL)
     (colored_sets.mixin T CL).
