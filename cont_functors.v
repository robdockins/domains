Require Import basics.
Require Import categories.
Require Import preord.
Require Import effective.
Require Import directed.

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

