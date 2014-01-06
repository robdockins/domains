(* Copyright (c) 2014, Robert Dockins *)

Require Import basics.
Require Import categories.
Require Import preord.
Require Import directed.

(** * Directed colimits and continuous functors.
 *)
Record directed_system (I:directed_preord) (C:category) :=
  DirSys
  { ds_F    : I -> ob C
  ; ds_hom : forall i j:I, i ≤ j -> ds_F i → ds_F j
  ; ds_ident : forall i (Hii:i≤i), ds_hom i i Hii ≈ id
  ; ds_compose : forall i j k (Hij:i≤j) (Hjk:j≤k) (Hik:i≤k),
                       ds_hom j k Hjk ∘ ds_hom i j Hij ≈ ds_hom i k Hik
  }.
Arguments ds_F [I] [C] _ _.
Arguments ds_hom [I] [C] _ _ _ _.
Arguments ds_ident [I] [C] _ _ _.
Arguments ds_compose [I] [C] _ _ _ _ _ _ _.

Record cocone (I:directed_preord) C (DS:directed_system I C) :=
  Cocone
  { cocone_point :> ob C
  ; cocone_spoke : forall i, ds_F DS i → cocone_point
  ; cocone_commute : forall i j (Hij:i≤j),
       cocone_spoke i ≈ cocone_spoke j ∘ ds_hom DS i j Hij
  }.
Arguments cocone [I] [C] DS.
Arguments Cocone [I] [C] DS _ _ _.
Arguments cocone_point [I] [C] [DS] _.
Arguments cocone_spoke [I] [C] [DS] _ _.
Arguments cocone_commute [I] [C] [DS] _ _ _ _.

Record directed_colimit (I:directed_preord) C (DS:directed_system I C) 
  (XC:cocone DS) :=
  DirectedColimit
  { colim_univ : forall (YC:cocone DS), XC → YC
  ; colim_commute : forall (YC:cocone DS) i,
       cocone_spoke YC i ≈ colim_univ YC ∘ cocone_spoke XC i
  ; colim_uniq : forall (YC:cocone DS) (f:XC → YC),
       (forall i, cocone_spoke YC i ≈ f ∘ cocone_spoke XC i) ->
       f ≈ colim_univ YC
  }.
Arguments directed_colimit [I] [C] DS XC.
Arguments DirectedColimit [I] [C] DS XC _ _ _.
Arguments colim_univ [I] [C] [DS] [XC] _ YC.
Arguments colim_commute [I] [C] [DS] [XC] _ _ _.
Arguments colim_uniq [I] [C] [DS] [XC] _ YC f _.

Program Definition dir_sys_app I C D
  (DS:directed_system I C) (F:functor C D)
  : directed_system I D:=

  DirSys I D
    (fun i => F (ds_F DS i))
    (fun i j Hij => F@(ds_hom DS i j Hij))
    _ _.
Next Obligation.
  intros.
  apply Functor.ident.
  apply ds_ident.
Qed.
Next Obligation.
  intros.
  rewrite <- Functor.compose.
  reflexivity.
  symmetry; apply ds_compose.
Qed.  
Arguments dir_sys_app [I] [C] [D] DS F.

Program Definition cocone_app I C D (DS:directed_system I C)
  (CC:cocone DS) (F:functor C D)
  : cocone (dir_sys_app DS F) :=

  Cocone (dir_sys_app DS F) (F CC) (fun i => F@cocone_spoke CC i) _.
Next Obligation.
  simpl; intros.
  rewrite <- (Functor.compose F). 2: reflexivity.
  rewrite <- (cocone_commute CC i j Hij).
  auto.
Qed.
Arguments cocone_app [I] [C] [D] [DS] CC F.


Definition continuous_functor (C D:category) (F:functor C D) :=
  forall I (DS:directed_system I C) (CC:cocone DS),
    directed_colimit DS CC ->
    directed_colimit (dir_sys_app DS F) (cocone_app CC F).
Arguments continuous_functor [C] [D] F.


(**  * Fixpoints of continuous functors.

     We can construct fixpoints of continuous endofunctors in
     any category that has an initial object and colimits of
     directed systems.

     This is essentially the categorical analogue of Kleene's
     fixpoint theorem for posets.
 *)

Require Import Arith.
Section fixpoint.
  Variable C:initialized.
  Variable F:functor C C.

  Variable colimit_cocone :
    forall (I:directed_preord) (DS:directed_system I C), cocone DS.

  Variable has_colimits :
    forall (I:directed_preord) (DS:directed_system I C),
            directed_colimit DS (colimit_cocone I DS).

  (** Iterated application of the functor [F]; the initial object
      provides the base case of the recursion.
    *)
  Fixpoint iterF (x:nat) : ob C :=
    match x with
    | O => ¡
    | S x' => F (iterF x')
    end.

  Lemma HSle0 j (Hij: S j <= O) : False.
  Proof.
    inversion Hij.
  Qed.

  (** Iterated action of the functor [F] on homs. The base case is
      provided by the universal hom associated to ¡.
   *)
  Fixpoint iter_hom (i:nat) : forall (j:nat) (Hij:i <= j), iterF i → iterF j :=
    match i as i' return forall (j:nat) (Hij:i' <= j), iterF i' → iterF j with
    | O => fun j Hij => initiate
    | S i' => fun j =>
        match j as j' return forall (Hij:S i' <= j'), iterF (S i') → iterF j' with
        | O => fun Hij => False_rect _ (HSle0 i' Hij) (* impossible case *)
        | S j' => fun Hij => F@(iter_hom i' j' (gt_S_le i' j' Hij))
        end
    end.

  Lemma iter_hom_proof_irr i : forall j H1 H2,
    iter_hom i j H1 ≈ iter_hom i j H2.
  Proof.
    induction i; simpl; intros; auto.
    destruct j.
    elimtype False. inversion H1.
    apply Functor.respects.
    apply IHi.
  Qed.

  (** The Kleene chain is a directed system. *)
  Program Definition kleene_chain : directed_system nat_dirord C :=
    DirSys nat_dirord C iterF iter_hom _ _.
  Next Obligation.      
    induction i; simpl; intros.
    symmetry. apply initiate_univ.
    apply Functor.ident; auto.
  Qed.
  Next Obligation.
    induction i. simpl; intros.
    apply initiate_univ.
    intros. destruct j.
    elimtype False. inversion Hij.
    destruct k.
    elimtype False. inversion Hjk.
    simpl.
    rewrite <- (Functor.compose F _ _ _ (iter_hom j k (gt_S_le j k Hjk))).
    reflexivity. auto.
  Qed.

  (** The fixpoint we desire is the point of the colimiting cocone
      corresponding to the Kleene chain.
   *)
  Definition fixpoint := cocone_point (colimit_cocone nat_dirord kleene_chain).


  (** It is mildly interesting to note that we can construct the fixpoint
      object without the continuity assumption.

      However, if we suppose [F] _is_ a continuous functor, we can demonstrate
      that [fixpoint] forms an initial algebra and thus actually is
      the least fixpoint of [F].
    *)
  Hypothesis Fcontinuous : continuous_functor F.

  (** Because [F] is continuous, the additional application of F
      to the fixpoint colimiting cocone is a colimiting cocone
      for the [n+1] Kleene chain.
   *)
  Let BL := Fcontinuous
               nat_dirord kleene_chain
               (colimit_cocone nat_dirord kleene_chain)
               (has_colimits nat_dirord kleene_chain).

  Program Definition cocone_plus1 : cocone (dir_sys_app kleene_chain F)
    := Cocone (dir_sys_app kleene_chain F) fixpoint
      (fun i => cocone_spoke (colimit_cocone nat_dirord kleene_chain) (S i)) _.
  Next Obligation.
    simpl; intros.
    assert (Hij' : S i <= S j). auto with arith.
    rewrite (cocone_commute (colimit_cocone nat_dirord kleene_chain) (S i) (S j) Hij').
    simpl. apply cat_respects; auto.
    apply Functor.respects.
    apply iter_hom_proof_irr.
  Qed.

  (** The algebra associated with the fixpoint. *)
  Definition fixpoint_alg : alg C F
    := @Alg C F fixpoint (colim_univ BL cocone_plus1).

  (** Next we define the catamorphism by iterating the action
      of a given algebra.
    *)
  Section cata.
    Variable AG : alg C F.
  
    Fixpoint cata_hom' (i:nat) : iterF i → AG :=
      match i as i' return iterF i' → AG with
      | O => initiate
      | S i' => Alg.iota AG ∘ F@(cata_hom' i')
      end.

    Lemma cata_hom_iter_hom : forall (i j:nat_ord) (Hij:i≤j),
      cata_hom' i ≈ cata_hom' j ∘ (iter_hom i j Hij).
    Proof.
      induction i; intros.
      simpl. symmetry. apply initiate_univ.
      destruct j. inversion Hij.
      simpl.
      rewrite <- (cat_assoc (Alg.iota AG)).
      apply cat_respects; auto.
      rewrite <- (Functor.compose F).
      2: reflexivity.
      rewrite IHi; eauto.
    Qed.      

    Program Definition AG_cocone : cocone kleene_chain :=
      Cocone _ _ cata_hom' cata_hom_iter_hom.
      
    Program Definition AG_cocone' :
      cocone (dir_sys_app kleene_chain F) :=
        Cocone _ _ (fun i => cata_hom' (S i)) _.
    Next Obligation.
      simpl; intros.
      rewrite (cata_hom_iter_hom i j Hij).
      rewrite Functor.compose.
      2: reflexivity.
      apply cat_assoc.
    Qed.

    Definition cata_hom : fixpoint → AG :=
      colim_univ (has_colimits nat_dirord kleene_chain) AG_cocone.

    Program Definition cata_alg_hom : Alg.alg_hom fixpoint_alg AG :=
      Alg.Alg_hom cata_hom _.
    Next Obligation.
      simpl.
      generalize (colim_uniq BL AG_cocone').
      intros.
      rewrite (H (cata_hom ∘ colim_univ BL cocone_plus1)).
      symmetry. apply H.

      intros. simpl.
      rewrite <- (cat_assoc (Alg.iota AG)).
      rewrite <- (Functor.compose F). 2: reflexivity.
      apply cat_respects; auto.
      apply Functor.respects.
      unfold cata_hom.
      apply (colim_commute (has_colimits nat_dirord kleene_chain) AG_cocone).

      intros.
      rewrite <- (cat_assoc cata_hom).
      rewrite <- (colim_commute BL cocone_plus1).
      unfold cata_hom.
      apply (colim_commute (has_colimits nat_dirord kleene_chain) AG_cocone (S i)).
    Qed.
  End cata.

  (**  Now we show that the catamorphims is universal and construct
       the initial algebra.
    *)
  Program Definition fixpoint_initial : Alg.initial_alg C F :=
    Alg.Initial_alg fixpoint_alg cata_alg_hom _.
  Next Obligation.
    simpl; intros.
    unfold cata_hom.
    apply (colim_uniq (has_colimits nat_dirord kleene_chain) (AG_cocone M)).
    intro i. simpl.
    induction i. simpl.
    symmetry. apply initiate_univ.
    simpl.
    rewrite IHi.
    rewrite Functor.compose. 2: reflexivity.
    rewrite (cat_assoc (Alg.iota M)).
    rewrite <- (Alg.hom_axiom h). simpl.
    repeat rewrite <- (@cat_assoc C).
    apply cat_respects; auto.
    symmetry.
    apply (colim_commute BL cocone_plus1).
  Qed.

  (**  With the initial algebra in hand, we immediately 
       get an isomorphism via standard facts about initial algebras.
    *)
  Definition fixpoint_iso :
    F fixpoint ↔ fixpoint :=

    Isomorphism C (F fixpoint) fixpoint 
      (colim_univ BL cocone_plus1)
      (Alg.out _ F fixpoint_initial)
      (Alg.out_in _ F fixpoint_initial)
      (Alg.in_out _ F fixpoint_initial).

End fixpoint.

(** * Standard continuous functors.

    The identity and constant functors are continuous, as is
    the composition of two continuous functors.
    
    Pairing and projection functors are also continuous.
 *)

Lemma identF_continuous (C:category) : continuous_functor id(C).
Proof.
  repeat intro.
  apply (DirectedColimit (dir_sys_app DS id(C)) (cocone_app CC id(C)) 
    (fun YC => colim_univ X (Cocone DS 
                 (cocone_point YC) (cocone_spoke YC) (cocone_commute YC)))).
  simpl; intros.
  apply (colim_commute X (Cocone DS 
                 (cocone_point YC) (cocone_spoke YC) (cocone_commute YC)) i).
  intros.
  apply (colim_uniq X (Cocone DS 
                 (cocone_point YC) (cocone_spoke YC) (cocone_commute YC))); auto.
Qed.


Lemma fconst_continuous (C D:category) (X:ob D) : continuous_functor (fconst C D X).
Proof.
  repeat intro.
  destruct (choose_ub_set I nil) as [j _].
  apply (DirectedColimit 
    (dir_sys_app DS (fconst C D X)) 
    (cocone_app CC (fconst C D X))
    (fun YC => cocone_spoke YC j)); simpl; intros.
  destruct (choose_ub I i j) as [k [??]].
  rewrite (cocone_commute YC i k H). simpl.
  rewrite (cocone_commute YC j k H0). simpl.
  rewrite (cat_ident1 (cocone_spoke YC k)).
  rewrite (cat_ident1 (cocone_spoke YC k)). auto.
  rewrite (H j). symmetry. apply cat_ident1.
Qed.


Lemma composeF_continuous (C D E:category)
  (F:functor D E) (G:functor C D) :
  continuous_functor F ->
  continuous_functor G ->
  continuous_functor (F ∘ G).
Proof.
  repeat intro.
  cut (directed_colimit
    (dir_sys_app (dir_sys_app DS G) F)
    (cocone_app (cocone_app CC G) F)).
  intros.
  apply (DirectedColimit 
    (dir_sys_app DS (F∘G)) (cocone_app CC (F∘G))
    (fun YC => colim_univ X2 (Cocone (dir_sys_app (dir_sys_app DS G) F)
                 (cocone_point YC) (cocone_spoke YC) (cocone_commute YC)))).
  simpl; intros.
  apply (colim_commute X2 (Cocone (dir_sys_app (dir_sys_app DS G) F)
                 (cocone_point YC) (cocone_spoke YC) (cocone_commute YC)) i).
  intros.
  apply (colim_uniq X2 (Cocone (dir_sys_app (dir_sys_app DS G) F)
                 (cocone_point YC) (cocone_spoke YC) (cocone_commute YC))); auto.
  apply X. apply X0. auto.
Qed.

Section pairF_continuous.
  Variables C D E:category.
  Variable F:functor C D.
  Variable G:functor C E.

  Section cocones.
    Variable I:directed_preord.
    Variable DS:directed_system I C.

    Program Definition cocone_fstF (YC:cocone (dir_sys_app DS (pairF F G)))
      : cocone (dir_sys_app DS F)
      := Cocone (dir_sys_app DS F)
                (obl (cocone_point YC)) 
                (fun i => homl (cocone_spoke YC i))
                _.
    Next Obligation.
      simpl; intros.
      destruct (cocone_commute YC i j Hij); auto.
    Qed.

    Program Definition cocone_sndF (YC:cocone (dir_sys_app DS (pairF F G)))
      : cocone (dir_sys_app DS G)
      := Cocone (dir_sys_app DS G)
                (obr (cocone_point YC)) 
                (fun i => homr (cocone_spoke YC i))
                _.
    Next Obligation.
      simpl; intros.
      destruct (cocone_commute YC i j Hij); auto.
    Qed.
  End cocones.

  Hypothesis HcontF : continuous_functor F.
  Hypothesis HcontG : continuous_functor G.

  Lemma pairF_continuous : continuous_functor (pairF F G).
  Proof.
    repeat intro.
    generalize (HcontF I DS CC X). intro.
    generalize (HcontG I DS CC X). intro.
    apply DirectedColimit with
      (fun YC => PROD.Hom D E
        (PROD.Ob D E (F (cocone_point CC)) (G (cocone_point CC)))
        (cocone_point YC)
        (colim_univ X0 (cocone_fstF I DS YC))
        (colim_univ X1 (cocone_sndF I DS YC))).
    simpl; intros. split; simpl.
    apply (colim_commute X0 (cocone_fstF I DS YC)).
    apply (colim_commute X1 (cocone_sndF I DS YC)).
    simpl; intros. split; simpl.
    apply (colim_uniq X0 (cocone_fstF I DS YC)).
    intro i; destruct (H i); auto.
    apply (colim_uniq X1 (cocone_sndF I DS YC)).
    intro i; destruct (H i); auto.
  Qed.  
End pairF_continuous.


Section fstF_continuous.
  Variables C D:category.
  Variable I:directed_preord.
  Variable DS:directed_system I (PROD C D).
  Variable CC:cocone DS.
  Variable Hcolim : directed_colimit DS CC.

  Program Definition fstF_cocone
    (CC1 : cocone (dir_sys_app DS (fstF C D))) : cocone DS
    := Cocone DS (PROD.Ob C D (cocone_point CC1) 
                                          (obr (cocone_point CC)))
                 (fun i => PROD.Hom C D _ _
                            (cocone_spoke CC1 i)
                            (homr (cocone_spoke CC i) : 
                                 obr (ds_F DS i) → obr (cocone_point CC)))

                 _.
  Next Obligation.
    intros. split; simpl.
    apply (cocone_commute CC1 i).
    apply (cocone_commute CC i).
  Qed.

  Definition fstF_univ (YC : cocone (dir_sys_app DS (fstF C D))) :
    cocone_app CC (fstF C D) → YC :=
    homl (colim_univ Hcolim (fstF_cocone YC)).
       
  Lemma fstF_continuous' :
    directed_colimit (dir_sys_app DS (fstF C D)) (cocone_app CC (fstF C D)).
  Proof.
    apply DirectedColimit with fstF_univ.
    simpl. intros.
    destruct (colim_commute Hcolim (fstF_cocone YC) i). auto.
    intros.
    destruct (colim_uniq Hcolim (fstF_cocone YC)
      (PROD.Hom C D
         (cocone_point CC)
         (PROD.Ob _ _ (cocone_point YC) (obr (cocone_point CC)))
         f id
         )); auto.
    intros. split; simpl; auto.
    apply H.
    symmetry. apply cat_ident2.
  Qed.
End fstF_continuous.

Lemma fstF_continuous C D :
  continuous_functor (fstF C D).
Proof.
  repeat intro. apply fstF_continuous'; auto.
Qed.


Section sndF_continuous.
  Variables C D:category.
  Variable I:directed_preord.
  Variable DS:directed_system I (PROD C D).
  Variable CC:cocone DS.
  Variable Hcolim : directed_colimit DS CC.

  Program Definition sndF_cocone
    (CC1 : cocone (dir_sys_app DS (sndF C D))) : cocone DS
    := Cocone DS (PROD.Ob C D (obl (cocone_point CC))
                              (cocone_point CC1))
                 (fun i => PROD.Hom C D _ _
                            (homl (cocone_spoke CC i) : 
                                 obl (ds_F DS i) → obl (cocone_point CC))
                            (cocone_spoke CC1 i))
                 _.
  Next Obligation.
    intros. split; simpl.
    apply (cocone_commute CC i).
    apply (cocone_commute CC1 i).
  Qed.

  Definition sndF_univ (YC : cocone (dir_sys_app DS (sndF C D))) :
    cocone_app CC (sndF C D) → YC :=
    homr (colim_univ Hcolim (sndF_cocone YC)).
       
  Lemma sndF_continuous' :
    directed_colimit (dir_sys_app DS (sndF C D)) (cocone_app CC (sndF C D)).
  Proof.
    apply DirectedColimit with sndF_univ.
    simpl. intros.
    destruct (colim_commute Hcolim (sndF_cocone YC) i). auto.
    intros.
    destruct (colim_uniq Hcolim (sndF_cocone YC)
      (PROD.Hom C D
         (cocone_point CC)
         (PROD.Ob _ _ (obl (cocone_point CC)) (cocone_point YC))
         id f)); auto.
    intros. split; simpl; auto.
    symmetry. apply cat_ident2.
    apply H.
  Qed.
End sndF_continuous.

Lemma sndF_continuous C D : continuous_functor (sndF C D).
Proof.
  repeat intro. apply sndF_continuous'; auto.
Qed.
