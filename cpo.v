(* Copyright (c) 2014, Robert Dockins *)

Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import directed.

Delimit Scope cpo_scope with cpo.
Open Scope cpo_scope.

Definition continuous (CL:color) (A B:preord) (f:A → B) :=
  forall lub (XS:cl_eset CL A),
    least_upper_bound lub XS ->
    least_upper_bound (f lub) (image f XS).
Arguments continuous CL [A B] f.

Lemma continuous_sequence CL (A B C:preord)
  (g:B → C) (f:A → B) :
  continuous CL g -> continuous CL f -> continuous CL (g ∘ f).
Proof.
  repeat intro. 
  cut (least_upper_bound (g (f lub)) (image g (image f XS))).
  { rewrite image_compose. auto. }
  apply H. apply H0. auto.
Qed.

Lemma continuous_equiv CL (A B:preord) (f f':A → B) :
  f ≈ f' -> continuous CL f -> continuous CL f'.
Proof.
  unfold continuous. intros.
  eapply least_upper_bound_morphism; [ | | apply H0; eauto ].
  - apply H.
  - apply image_morphism; [ | reflexivity ].
    split; intro x; destruct (H x); auto.
Qed.

Lemma continuous_pair CL (C A B:preord) (f:C → A) (g:C → B) :
  continuous CL f -> continuous CL g -> continuous CL 〈f, g〉.
Proof.
  repeat intro. simpl.
  destruct (H lub XS); auto.
  destruct (H0 lub XS); auto.
  split.
  - red; intros.
    apply image_axiom2 in H6. destruct H6 as [c [??]].
    simpl in H7. rewrite H7. split; simpl.
    + apply Preord.axiom. apply H1. auto.
    + apply Preord.axiom. apply H1. auto.
  - intros. destruct b. split; simpl.
    + apply H3. red; intros.
      apply image_axiom2 in H7. destruct H7 as [q [??]].
      rewrite H8.
      cut ((f q, g q) ≤ (c,c0)).
      { intros [??]; auto. }
      apply H6.
      apply image_axiom1'. exists q. split; auto.
    + apply H5. red; intros.
      apply image_axiom2 in H7. destruct H7 as [q [??]].
      rewrite H8.
      cut ((f q, g q) ≤ (c,c0)).
      { intros [??]; auto. }
      apply H6.
      apply image_axiom1'. exists q. split; auto.
Qed.

Lemma continuous_pi1 CL (A B:preord) :
  @continuous CL (A×B) A π₁.
Proof.
  repeat intro.
  split; repeat intro.
  - apply image_axiom2 in H0. destruct H0 as [q [??]].
    rewrite H1.
    cut (q ≤ lub).
    { intros [??]; auto. }
    apply H. auto.
  - destruct H.
    destruct (H1 (b,snd lub)); auto.
    red; intros.
    split; simpl.
    + apply H0.  
      apply image_axiom1'. exists x; auto.
    + cut (x ≤ lub).
      { intros [??]; auto. }
      apply H; auto.
Qed.

Lemma continuous_pi2 CL (A B:preord) :
  @continuous CL (A×B) B π₂.
Proof.
  repeat intro.
  split; repeat intro.
  - apply image_axiom2 in H0. destruct H0 as [q [??]].
    rewrite H1.
    cut (q ≤ lub).
    { intros [??]; auto. }
    apply H. auto.
  - destruct H.
    destruct (H1 (fst lub,b)); auto.
    red; intros.
    split; simpl.
    + cut (x ≤ lub).
      { intros [??]; auto. }
      apply H; auto.
    + apply H0.  
      apply image_axiom1'. exists x; auto.
Qed.


(**  * Complete partial orders

     Here we define the category of colored CPOs.  We will mostly
     be interested in the case where the color is one of the two
     instances of h-directedness; however much of the the theory goes
     through in the more general setting of arbitrary colors.

     A CPO is a preorder where there is a supremum operation for every
     colored set.  CPOs form a category together with the Scott-continuous
     functions, which are monotone and preserve colored suprema.
  *)
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

  Notation "∐ XS" := (@sup_op _ _ (XS)%set) : cpo_scope.


  Lemma sup_is_lub : forall CL (A:type CL) (XS:cl_eset CL (ord A)),
    least_upper_bound (∐XS) XS.
  Proof.
    intros. split. apply sup_is_ub. apply sup_is_least.
  Qed.

  Lemma continuous_sup : forall CL (A B:type CL) (f:ord A → ord B),
    continuous CL f <->
    forall (XS:cl_eset CL (ord A)), f (sup_op XS) ≤ sup_op (image f XS).
  Proof.
    intros. split; intros.
    - destruct (H (∐XS) XS (sup_is_lub CL A XS)).
      apply H1. red; intros. apply sup_is_ub; auto.

    - red; intros; split; repeat intro.
      + apply image_axiom2 in H1.
        destruct H1 as [y [??]]. rewrite H2.
        apply Preord.axiom.
        apply H0. auto.
      + transitivity (f (∐XS)).
        * apply Preord.axiom.
          apply H0. apply sup_is_ub.
        * transitivity (∐(image f XS)); [ apply H |].
          apply sup_is_least. auto.
  Qed.    

  Lemma continuous_sup' : forall CL (A B:type CL) (f:ord A → ord B),
    continuous CL f <->
    forall (XS:cl_eset CL (ord A)), f (sup_op XS) ≈ sup_op (image f XS).
  Proof.
    intros. rewrite continuous_sup.
    split; intros; [ | apply H ].
    split; [ apply H |].
    apply sup_is_least. red; intros.
    apply image_axiom2 in H0. destruct H0 as [y [??]].
    rewrite H1. apply Preord.axiom. apply sup_is_ub. auto.
  Qed.

  Record hom CL (A B:type CL) :=
    Hom
    { map :> ord A -> ord B
    ; mono : forall (a b:carrier A), 
               Preord.ord_op (ord A) a b ->
               Preord.ord_op (ord B) (map a) (map b)
    ; cont : continuous CL (Preord.Hom _ _ map mono)
    }.
  Arguments map [CL] [A] [B] h x.
  Arguments mono [CL] [A] [B] h a b _.
  Arguments cont  [CL] [A] [B] h lub XS _.
  
  Definition ord_hom {CL:color} {A B:type CL} (f:hom CL A B) : Preord.hom (ord A) (ord B) :=
    Preord.Hom _ _ (map f) (mono f).
  Coercion ord_hom : hom >-> Preord.hom.

  Program Definition build_hom {CL:color} (A B:type CL)
    (f:Preord.hom (ord A) (ord B))
    (H:continuous CL f)
    : hom CL A B
    := Hom CL A B (Preord.map _ _ f) _ _.
  Next Obligation.
    simpl; intros. apply Preord.axiom. auto.
  Qed.
  Next Obligation.
    intros. apply H.
  Qed.

  Program Definition ident {CL:color} (X:type CL) :
    hom CL X X := build_hom X X (Preord.ident (ord X)) _.
  Next Obligation.
    repeat intro.
    simpl.
    destruct H; split; repeat intro.
    - apply image_axiom2 in H1. destruct H1 as [?[??]].
      simpl in H2. rewrite H2; apply H; auto.
    - apply H0. red; intros.
      apply H1.
      apply image_axiom1'. exists x. split; auto.
  Qed.


  Program Definition compose {CL:color} {X Y Z:type CL} (g:hom CL Y Z) (f:hom CL X Y)
    := build_hom X Z (ord_hom g ∘ ord_hom f) _.
  Next Obligation.
    repeat intro. 
    cut (least_upper_bound (g (f lub)) (image g (image f XS))).
    { intros [??]; split; repeat intro.
      apply H0. apply image_axiom2 in H2.
      destruct H2 as [q [??]]. simpl in H3.
      rewrite H3.
      apply image_axiom1'. exists (f q); split; auto.
      apply image_axiom1'. exists q; split; auto.
      apply H1. repeat intro.
      apply H2.
      apply image_axiom2 in H3.
      destruct H3 as [y [??]].
      apply image_axiom2 in H3.
      destruct H3 as [y' [??]].
      apply image_axiom1'.
      exists y'. split; auto.
      simpl.
      rewrite H4.
      rewrite H5. auto.
    } 
    apply (cont g). apply (cont f). auto.
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
    transitivity (app_to CL X Y b y).
    - simpl. apply mono. auto.
    - apply sup_is_ub. apply image_axiom1. auto.
  Qed.
  Next Obligation.
    repeat intro.
    split; repeat intro.
    - apply image_axiom2 in H0. destruct H0 as [y [??]].
      simpl in H1.
      rewrite H1.
      apply sup_is_least. red; intros.
      apply image_axiom2 in H2.
      destruct H2 as [y' [??]]. simpl in H3. simpl.
      rewrite H3.
      transitivity (y' lub).
      + apply mono. apply H. auto.
      + apply sup_is_ub.
        apply image_axiom1'.
        simpl. exists y'. split; auto.

    - simpl. apply sup_is_least.
      repeat intro.
      apply image_axiom2 in H1. destruct H1 as [y [??]].
      simpl in H2. rewrite H2.
      destruct (cont y lub XS); auto.
      apply H4.
      hnf; intros.
      apply image_axiom2 in H5. destruct H5 as [q [??]].
      simpl in H6. rewrite H6.
      transitivity (sup_op (image (app_to CL X Y q) FS)).
      + apply sup_is_ub. simpl.
        apply image_axiom1'. simpl. exists y. split; auto.
      + apply H0.
        apply image_axiom1'. simpl. exists q. split; auto.
  Qed.    

  Program Definition hom_mixin CL X Y :=
    Mixin CL (hom_ord CL X Y) (hom_sup CL X Y) _ _.
  Next Obligation.
    intros CL X Y A. red. intros.
    red; intros. unfold hom_sup.
    simpl. red; simpl. intros q.
    apply sup_is_ub.
    change (app x q) with
      ((app_to CL X Y q) x).
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
    
    - repeat intro. split.
      + red; simpl; intros. red; simpl; intros. apply ord_refl.
      + repeat intro. red; simpl; intros. apply ord_refl.

    - repeat intro. split.
      + red; simpl; intros. red; simpl; intros. apply ord_refl.
      + repeat intro. red; simpl; intros. apply ord_refl.

    - repeat intro. split. 
      + red; simpl; intros. red; simpl; intros. apply ord_refl.
      + red; simpl; intros. red; simpl; intros. apply ord_refl.
    
    - repeat intro. split.
      + red; simpl; intros. red; simpl; intros.
        apply ord_trans with (app f (app g' x)).
        * unfold app.
          apply mono.
          destruct H0. apply H0.
        * destruct H. apply H.
      + red; simpl; intros.
        red; simpl; intros.
        apply ord_trans with (app f (app g' x)).
        * destruct H. apply H1.
        * unfold app; simpl.
          apply mono.
          destruct H0. apply H1.
  Qed.

  Canonical Structure CPO CL := Category (type CL) (hom CL) _ _ (cat_axioms CL).

  Lemma axiom : forall CL (A B:ob (CPO CL)) (f:A → B),
    forall X, f (∐X) ≈ ∐(image f X).
  Proof.
    intros. apply ord_antisym.
    - destruct (cont f (sup_op X) X).
      + split; [ apply sup_is_ub | apply sup_is_least ].
      + apply H0; auto.
        repeat intro.
        apply image_axiom2 in H1. destruct H1 as [q [??]].
        simpl in H2. rewrite H2.
        apply sup_is_ub. apply image_axiom1'. exists q; split; auto.

    - apply sup_is_least.
      red. intros.
      apply image_axiom2 in H.
      destruct H as [y [??]].
      transitivity (f y).
      + destruct H0; auto.
      + apply mono. apply sup_is_ub; auto.
  Qed.

  Section prod.  
    Variable CL:color.
    Variables A B:type CL.

    Program Definition prod_sup (X:cl_eset CL (prod_preord (ord A) (ord B))) : A*B :=
      (∐(image π₁ X), ∐(image π₂ X)).

    Program Definition prod_mixin : mixin_of CL (prod_preord (ord A) (ord B)) :=
      Mixin CL _ prod_sup _ _.
    Next Obligation.
      repeat intro. destruct x as [a b].
      unfold prod_sup. split; simpl.
      - apply sup_is_ub. apply image_axiom1'.
        exists (a,b); auto.
      - apply sup_is_ub. apply image_axiom1'.
        exists (a,b); auto.
    Qed.
    Next Obligation.
      repeat intro. destruct ub as [ua ub].
      unfold prod_sup; split; simpl;
        apply sup_is_least; repeat intro.
      - apply image_axiom2 in H0.
        destruct H0 as [y [??]].
        rewrite H1.
        assert (y ≤ (ua,ub)).
        { apply H; auto. }
        destruct H2; auto.
      - apply image_axiom2 in H0.
        destruct H0 as [y [??]].
        rewrite H1.
        assert (y ≤ (ua,ub)).
        { apply H; auto. }
        destruct H2; auto.
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
      red; intros.
      split; simpl; repeat intro.
      - apply image_axiom2 in H0. destruct H0 as [q [??]].
        simpl in H1. rewrite H1.
        destruct H. apply H in H0.
        destruct H0; auto.

      - destruct H.
        destruct (H1 (b,snd lub)).
        + hnf; intros.
          split; simpl; auto.
          * apply H0.
            apply image_axiom1'. simpl. exists x. split; auto.
          * apply H in H2. destruct H2; auto.
        + simpl in *. auto.
    Qed.    
    
    Program Definition pi2 : prod_cpo → B :=
      Hom CL prod_cpo B (fun x => snd x) _ _.
    Next Obligation.
      intros. destruct H; auto.
    Qed.
    Next Obligation.
      simpl; intros.
      red; intros.
      split; simpl; repeat intro.
      - apply image_axiom2 in H0. destruct H0 as [q [??]].
        simpl in H1. rewrite H1.
        destruct H. apply H in H0.
        destruct H0; auto.

      - destruct H.
        destruct (H1 (fst lub, b)).
        + hnf; intros.
          split; simpl; auto.
          * apply H in H2. destruct H2; auto.
          * apply H0.
            apply image_axiom1'. simpl. exists x. split; auto.
        + simpl in *. auto.
    Qed.    
  End prod.

  Program Definition pair CL (C A B:type CL) (f:C → A) (g:C → B) : C → prod_cpo CL A B :=
    Hom CL C (prod_cpo CL A B) (fun x => (f x, g x)) _ _.
  Next Obligation.
    repeat intro. split; simpl; apply mono; auto.
  Qed.
  Next Obligation.
    repeat intro. 
    split; hnf; intros.
    - apply image_axiom2 in H0. destruct H0 as [y [??]]. simpl in *.
      rewrite H1.
      apply H in H0.
      split; simpl.
      + apply (mono f); auto.
      + apply (mono g); auto.
    - simpl.
      split; simpl.
      + destruct (cont f lub XS); auto.
        apply H2. hnf; intros.
        apply image_axiom2 in H3. destruct H3 as [q [??]]. 
        destruct (H0 (f q, g q)).
        * apply image_axiom1'. simpl. exists q; split; auto.
        * simpl in H5. simpl in H4. rewrite H4; auto.
      + destruct (cont g lub XS); auto.
        apply H2. hnf; intros.
        apply image_axiom2 in H3. destruct H3 as [q [??]]. 
        destruct (H0 (f q, g q)).
        * apply image_axiom1'. simpl. exists q; split; auto.
        * simpl in H6. simpl in H4. rewrite H4; auto.
  Qed.    

End CPO.

(** A "dcpo" is a directed-complete partial order; that is a CPO
    with one of the the directedness color variants.
  *)
Notation dcpo hf := (CPO.type (directed_hf_cl hf)).

(** A "cpo" is a directed-complete cpo not necessarily containing
    a least element.
  *)
Notation cpo  := (CPO.type (directed_hf_cl false)).

(** A "cppo" is a directed-complete pointed partial order; that is
    certainly has a least element.
  *)
Notation cppo := (CPO.type (directed_hf_cl true)).

Notation CPO := CPO.CPO.

Notation dirset := (cl_eset (directed_hf_cl _)).

Canonical Structure CPO.
Canonical Structure CPO.ord.
Canonical Structure CPO.ord_hom.
Canonical Structure CPO.comp.
Canonical Structure CPO.hom_ord.
Canonical Structure CPO.hom_cpo.
Canonical Structure hom_eq CL X Y:=
  Eq.Pack (CPO.hom CL X Y) (Preord.ord_eq (CPO.hom_ord CL X Y)).
Coercion CPO.ord : CPO.type >-> preord.
Coercion CPO.ord_hom : CPO.hom >-> Preord.hom.

Notation "∐ XS" := (@CPO.sup_op _ _ (XS)%set) : cpo_scope.

Arguments CPO.axiom [CL A B] f X.
Arguments CPO.mono [CL A B] h a b _.
Arguments CPO.cont [CL A B] h lub XS _.

(**  Supremum is a monotone operation. *)
Lemma sup_monotone : forall CL (A:CPO.type CL) (X X':cl_eset CL A),
  X ⊆ X' -> ∐X ≤ ∐X'.
Proof.
  intros. apply CPO.sup_is_least. repeat intro.
  apply CPO.sup_is_ub. auto.
Qed.  

(**  Supremum respects equality of sets. *)
Lemma sup_equiv : forall CL (A:CPO.type CL) (X X':cl_eset CL A),
  X ≈ X' -> ∐X ≈ ∐X'.
Proof.
  intros. destruct H; split; apply sup_monotone; auto.
Qed.

Class pointed (CL:color) (X:CPO.type CL) := 
  { bottom : X 
  ; bottom_least : forall x, bottom ≤ x
  }.

Notation "⊥" := (@bottom _ _ _) : cpo_scope.

Arguments pointed [CL] X.
Hint Resolve bottom_least.

(**  Every cppo has a least element, which arises as the supremum
     of the empty set.
  *)
Section bottom.
  Variables X Y:cppo.
  
  Lemma empty_semidirected : color_prop (directed_hf_cl true) (∅:eset X).
  Proof.
    hnf; simpl; intros.
    destruct Hinh. apply H in H0.
    apply empty_elem in H0. elim H0.
  Qed.

  Definition empty_dir : dirset X := exist _ ∅ empty_semidirected.

  Definition cppo_bot : X := ∐ empty_dir.

  Lemma cppo_bot_least : forall x, cppo_bot ≤ x.
  Proof.
    intros. unfold cppo_bot.
    apply CPO.sup_is_least.
    repeat intro.
    red in H; simpl in H.
    apply empty_elem in H. elim H.
  Qed.
End bottom.

Instance cppo_pointed (X:cppo) : pointed X :=
  { bottom := cppo_bot X; bottom_least := cppo_bot_least X }.

(**  Every Scott-continuous map between cppos preserves
     the bottom element, i.e., is strict.
  *)
Lemma strict_map (X Y:cppo) (f:X → Y) : f ⊥ ≈ ⊥.
Proof.
  simpl.
  rewrite (CPO.axiom f (empty_dir X)).
  apply sup_equiv.
  split; intros a H.
  - apply image_axiom2 in H.
    destruct H as [?[??]].
    red in H; simpl in H.
    apply empty_elem in H. elim H.
  - red in H; simpl in H.
    apply empty_elem in H. elim H.
Qed.    
Arguments strict_map [X Y] f.

(**  * Chain suprema and least fixed points

     A chain is specified by a base case a monotone operation to iterate,
     where base ≤ step base.
     
     Every chain gives rise to a directed set and thus has a suprema.
     Suprema of chains have a nice induction principle.
  *)
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

Definition admissible hf (X:dcpo hf) (P:X -> Prop) (q:X) :=
  P q /\ forall XS:dirset X, q ∈ XS -> (forall x, x ∈ XS -> P x) -> P (∐XS).

Arguments admissible [hf X] P q.

Section iter_chain.
  Variable hf:bool.
  Variable X:dcpo hf.
  
  Variable base : X.
  Variable step : X -> X.

  Hypothesis step_mono : forall x y, x ≤ y -> step x ≤ step y.
  Hypothesis step_base : base ≤ step base.

  Definition iter_chain_set : eset X :=
    fun n => Some (N.iter n step base).

  Lemma iter_le : forall n1 n2,
    (n1 <= n2)%N -> N.iter n1 step base ≤ N.iter n2 step base.
  Proof.
    induction n1 using N.peano_ind; simpl; intros.
    - clear H.
      induction n2 using N.peano_ind; simpl; intros.
      + auto.    
      + transitivity (step base); auto.
        repeat rewrite Niter_succ.
        apply step_mono. auto.
    
    - induction n2 using N.peano_ind; simpl.
      + elim H. destruct n1; simpl; auto.
      + repeat rewrite Niter_succ.
        apply step_mono.
        apply IHn1.
        apply N.succ_le_mono; auto.
  Qed.    

  Lemma iter_set_directed : color_prop (directed_hf_cl hf) iter_chain_set.
  Proof.
    red. simpl. apply prove_directed; auto.
    - pattern hf at 1. case hf. auto.
      exists base. exists 0%N.
      simpl. auto.
    
    - simpl; intros.
      destruct H as [n1 ?].
      destruct H0 as [n2 ?].
      simpl in H. simpl in H0.
      destruct (N.lt_ge_cases n1 n2).
      + exists y.
        repeat split; auto.
        * rewrite H. rewrite H0.
          apply iter_le.
          hnf in H1. hnf.
          rewrite H1. discriminate.
        * exists n2. auto.
      + exists x.
        repeat split; auto.
        * rewrite H. rewrite H0.
          apply iter_le; auto.
        * exists n1. auto.
  Qed.

  Definition iter_chain : dirset X := 
    exist _ iter_chain_set iter_set_directed.

  Lemma iter_chain_base :
    base ∈ iter_chain.
  Proof.
    exists 0%N. simpl. auto.
  Qed.

  Lemma iter_chain_step : forall x,
    x ∈ iter_chain -> step x ∈ iter_chain.
  Proof.
    intros.
    destruct H as [n ?].
    exists (N.succ n).
    simpl in *. rewrite Niter_succ.
    destruct H; split; apply step_mono; auto.
  Qed.

  Definition chain_sup : X := ∐ iter_chain.

  Lemma chain_induction (P:X -> Prop) :
    admissible P base ->
    (forall x y, x ≈ y -> P x -> P y) ->
    (forall x, P x -> P (step x)) ->
    P chain_sup.
  Proof.
    intros. unfold chain_sup.
    destruct H.
    apply (H2 iter_chain); intros; auto.
    - apply iter_chain_base.
    - destruct H3 as [n ?]. simpl in *.
      symmetry in H3. apply (H0 _ _ H3). clear x H3.
      induction n using N.peano_ind; simpl; auto.
      rewrite Niter_succ.
      apply H1. auto.
  Qed.
End iter_chain.


(**  The least-fixed point of a continous function in a cpo arises as
     a particular instance of a chain suprema, and the Scott induction
     principle is an instance of chain induction.
  *)
Section lfp.
  Variable X:cpo.
  Variable f:X → X.
  Variable Hpointed : pointed X.
  
  Definition lfp := chain_sup false X ⊥ f (CPO.mono f) (bottom_least (f ⊥)).

  Lemma scott_induction (P:X -> Prop) :
    admissible P ⊥ ->
    (forall x y, x ≈ y -> P x -> P y) ->
    (forall x, P x -> P (f x)) ->
    P lfp.
  Proof.
    intros. unfold lfp. apply chain_induction; auto.
  Qed.

  Lemma lfp_least : forall x, f x ≈ x -> lfp ≤ x.
  Proof.
    apply scott_induction; intros.
    split; intros; auto.
    apply CPO.sup_is_least. repeat intro.
    apply H0; auto.
    rewrite <- H. apply H0; auto.
    rewrite <- H0.
    apply CPO.mono. apply H; auto.
  Qed.

  Lemma lfp_fixpoint : f lfp ≈ lfp.
  Proof.
    split.

    - unfold lfp, chain_sup.
      simpl.
      rewrite (CPO.axiom f (iter_chain false X ⊥ f _ _)).
      apply CPO.sup_is_least; simpl.
      hnf; simpl; intros.
      apply image_axiom2 in H. destruct H as [q [??]]. rewrite H0.
      apply CPO.sup_is_ub. simpl.
      apply iter_chain_step. auto.

    - apply scott_induction; auto.
      + split; intros; auto.
        apply CPO.sup_is_least.
        hnf; intros.
        transitivity (f x). apply H0; auto.
        apply CPO.mono. apply CPO.sup_is_ub. auto.
      + intros. rewrite <- H; auto.
  Qed.
End lfp.

Arguments lfp [X] f [Hpointed].
Arguments scott_induction [X] f [Hpointed] P _ _ _. 

(**  The least-fixed point in cpos is uniform.  This fact is somtimes
     called Plotkin's axiom.
  *)
Lemma lfp_uniform (D E:cpo)
  (HD:pointed D) (HE:pointed E) 
  (f:D → E) (d:D → D) (e:E → E) :

  f ⊥ ≈ ⊥ ->
  e ∘ f ≈ f ∘ d ->
  lfp e ≈ f (lfp d).
Proof.
  intros. split.

  - apply (scott_induction e); intros.
    + split; auto. intros.
      apply CPO.sup_is_least. repeat intro; auto.
    + rewrite <- H1; auto.
    + rewrite H1.
      rewrite <- (lfp_fixpoint D d) at 2.
      destruct H0. apply H0.

  - apply (scott_induction d); intros.
    + split; intros.
      * rewrite H. apply bottom_least.
      * rewrite (CPO.axiom f XS).
        apply CPO.sup_is_least. repeat intro.
        apply image_axiom2 in H3. destruct H3 as [y [??]].
        apply H2 in H3.
        rewrite H4. auto.
    + rewrite <- H2; auto.
    + rewrite <- (lfp_fixpoint E e).
      rewrite <- H1.
      destruct H0. apply H2.
Qed.
