(* Copyright (c) 2014, Robert Dockins *)

Require Import List.

Require Import basics.
Require Import categories.
Require Import preord.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import plotkin.
Require Import profinite.
Require Import embed.
Require Import joinable.
Require Import directed.
Require Import cont_functors.
Require Import bilimit.

(**  * Embedding functor for exponentials.

     Here we define the function space functor in the category of embeddings
     and prove that is is continuous.
  *)

Section map_rel.
  Context {A B C D : preord}.

  Variable f:A -> B.
  Variable g:C -> D.

  Fixpoint map_rel (G:finset (A×C)%cat_ob) : finset (B×D)%cat_ob :=
    match G with
    | nil => nil
    | (a,c)::G' => (f a, g c)::map_rel G'
    end.

  Lemma map_rel_inh : forall hf G,
    inh hf G -> inh hf (map_rel G).
  Proof.
    intros.
    destruct hf; hnf; auto.
    destruct H.
    destruct H as [q [??]].
    clear x H0.
    induction G. elim H.
    hnf in H. destruct H.
    subst a.
    destruct q.
    exists (f c, g c0).
    exists (f c, g c0).
    split; simpl; auto.   
    destruct IHG as [x ?]; auto.
    exists x.
    simpl. destruct a.
    apply cons_elem; auto.
  Qed.

  Lemma unmap_rel : forall b d G,
    (b,d) ∈ map_rel G ->
    exists a c, (a,c) ∈ G /\ f a ≈ b /\ g c ≈ d.
  Proof.
    induction G; simpl; intros.
    apply nil_elem in H. elim H.
    destruct a. simpl in H.
    apply cons_elem in H. destruct H.
    exists c. exists c0.
    split; auto.
    apply cons_elem; auto.
    destruct H as [[??][??]]; split; split; auto.
    destruct IHG as [p [q [??]]]; auto.
    exists p. exists q. split; auto.
    apply cons_elem; auto.
  Qed.    

  Lemma unmap_rel_sub : forall G X,
    G ⊆ map_rel X ->
    exists G', G' ⊆ X /\ G ≈ map_rel G'.
  Proof.
    induction G; simpl; intros.
    exists nil. simpl; split; auto.
    red; intros. apply nil_elem in H0. elim H0.
    destruct (IHG X) as [G' [??]].
    hnf; intros. apply H. apply cons_elem; auto.
    assert (a ∈ map_rel X).    
    apply H. apply cons_elem. auto.
    destruct a.
    apply unmap_rel in H2.
    destruct H2 as [p [q [?[??]]]].
    exists ((p,q)::G').
    split.
    hnf; intros.
    apply cons_elem in H5. destruct H5.
    rewrite H5. auto.
    apply H0; auto.
    split; hnf; simpl; intros.
    apply cons_elem in H5.
    destruct H5. rewrite H5.
    apply cons_elem.
    left.
    destruct H3; destruct H4; split; split; auto.
    apply cons_elem. right; auto.
    rewrite <- H1; auto.
    
    apply cons_elem in H5.
    destruct H5. rewrite H5.
    apply cons_elem.
    left.
    destruct H3; destruct H4; split; split; auto.
    apply cons_elem. right; auto.
    rewrite H1; auto.
  Qed.    
End map_rel.


Section exp_functor.
  Variable hf:bool.
  Variables A B C D:ob (EMBED hf).

  Variable f:A ⇀ B.
  Variable g:C ⇀ D.

  Lemma map_rel_in : forall G a b,
    (a,b) ∈ G -> (f a, g b) ∈ map_rel f g G.
  Proof.
    induction G; simpl; intros.
    apply nil_elem in H. elim H.
    apply cons_elem in H. destruct H. destruct a.
    simpl. apply cons_elem.
    left.
    destruct H as [[??][??]].
    split; split; simpl in *; auto.
    apply embed_mono; auto.
    apply embed_mono; auto.
    apply embed_mono; auto.
    apply embed_mono; auto.
    destruct a. simpl.
    apply cons_elem. right.
    apply IHG. auto.
  Qed.

  Lemma is_joinable_unmap_rel X :
    is_joinable_relation hf (map_rel f g X) ->
    is_joinable_relation hf X.
  Proof.
    intros. destruct H; split.
    destruct hf; hnf; simpl; auto.
    destruct H as [x ?].
    destruct x.
    apply unmap_rel in H.
    destruct H as [p [q [?[??]]]].
    exists (p,q). auto.
    intros.
    destruct (mub_complete (PLT.plotkin B) 
      (image (π₁)%cat_ops (map_rel f g G)) (f x)) as [z [??]].
    apply inh_image.
    apply map_rel_inh; auto.
    hnf; intros.
    apply image_axiom2 in H3.
    destruct H3 as [[p q] [??]]. simpl in *.
    rewrite H4.
    destruct H2.
    apply unmap_rel in H3.
    destruct H3 as [p' [q' [?[??]]]].
    rewrite <- H6.
    apply embed_mono. apply H2.
    apply image_axiom1'.
    exists (p',q'). split; auto.

    destruct (H0 (map_rel f g G)) with z
      as [q [??]]; auto.
    apply map_rel_inh; auto.
    hnf; intros.
    destruct a.
    apply unmap_rel in H5.
    destruct H5 as [p [q [?[??]]]].
    apply member_eq with (f p, g q).
    destruct H6; destruct H7; split; split; simpl; auto.
    apply map_rel_in. apply H1. auto.

    apply unmap_rel in H5.
    destruct H5 as [z' [q' [?[??]]]].
    assert (z' ≈ x).
    split.
    apply (embed_reflects f).
    rewrite H7; auto.
    destruct H2.
    apply H9.
    hnf; intros.
    apply image_axiom2 in H10.
    destruct H10 as [[r s] [??]].
    rewrite H11; simpl.
    apply (embed_reflects f).
    rewrite H7.
    destruct H3.
    apply H3.
    apply image_axiom1'.
    exists (f r, g s).
    split; auto.
    apply map_rel_in. auto.
    apply (embed_reflects f).
    rewrite H7; auto.
    exists q'. split.
    apply member_eq with (z',q'); auto.
    destruct H9; split; split; auto.
    hnf; intros.
    apply image_axiom2 in H10.
    destruct H10 as [[r s] [??]]. rewrite H11. simpl.
    apply (embed_reflects g).
    rewrite H8. apply H6.
    apply image_axiom1'.
    exists (f r, g s). split; auto.
    apply map_rel_in. auto.
  Qed.

  Lemma is_joinable_map_rel X :
    is_joinable_relation hf X ->
    is_joinable_relation hf (map_rel f g X).
  Proof.
    intros. destruct H. split.

    apply map_rel_inh; auto.
    intros.
    apply unmap_rel_sub in H1.
    destruct H1 as [G' [??]].
    
    assert (exists q, upper_bound q (image (π₁)%cat_ops G') /\ f q ≤ x).
    destruct H2. clear H4.
    assert (upper_bound x (image (π₁)%cat_ops (map_rel f g G'))).
    hnf; intros.
    apply H2.
    apply image_axiom2 in H4.
    destruct H4 as [?[??]].
    rewrite <- H3 in H4.
    rewrite H5.
    apply image_axiom1. auto.
    assert (inh hf G').
    destruct hf; hnf; auto.
    destruct HGinh as [[a c] ?].
    rewrite H3 in H5.
    apply unmap_rel in H5.
    destruct H5 as [p [q [?[??]]]].
    eauto.
    
    clear H2 G HGinh H0 H H3 X H1.
    induction G'.
    destruct hf.
    hnf in H5.
    destruct H5 as [[a c] ?].
    apply nil_elem in H. elim H.
    destruct (embed_directed0 f x) as [q ?].
    exists q. split; auto.
    hnf; simpl; intros.
    apply nil_elem in H0. elim H0.
    destruct a as [a c].
    assert (f a ≤ x).
    apply H4. simpl. apply cons_elem; auto.
    case_eq G'; intros.
    exists a. split; auto.
    hnf; simpl; intros.
    apply cons_elem in H1.
    destruct H1; auto.
    apply nil_elem in H1. elim H1.
    rewrite <- H0.
    destruct IHG' as [q [??]].
    hnf; intros. apply H4.
    simpl. apply cons_elem; auto.
    rewrite H0.
    eapply elem_inh.
    apply cons_elem; eauto.
    destruct (embed_directed2 f x q a) as [z [?[??]]]; auto.
    exists z. split; auto.
    hnf; simpl; intros.
    apply cons_elem in H8.
    destruct H8. rewrite H8; auto.
    transitivity q; auto.

    destruct H4 as [q [??]].
    destruct (mub_complete (PLT.plotkin A) (image (π₁)%cat_ops G') q) as [q' [??]].
    destruct hf; hnf; auto.
    destruct HGinh.
    destruct x0.
    rewrite H3 in H6.
    apply unmap_rel in H6.
    destruct H6 as [n [m [?[??]]]].
    exists n.
    apply image_axiom1'. exists (n,m); auto.
    auto.

    assert (x ≈ f q').
    split.
    destruct H2. apply H8.
    destruct H6.
    hnf; intros.
    apply image_axiom2 in H10.
    destruct H10 as [z [??]].
    rewrite H3 in H10.
    rewrite H11.
    simpl.
    destruct z as [za zb]. simpl.
    apply unmap_rel in H10.
    destruct H10 as [za' [zb' [?[??]]]].
    rewrite <- H12.
    apply embed_mono.
    apply H6.
    apply image_axiom1'.
    exists (za',zb'). auto.
    transitivity (f q); auto.
    apply embed_mono; auto.
    transitivity (f q); auto.
    apply embed_mono; auto.

    destruct (H0 G') with q'; auto.
    destruct hf; hnf; auto.
    destruct HGinh.
    destruct x0.
    rewrite H3 in H9.
    apply unmap_rel in H9.
    destruct H9 as [n [m [?[??]]]].
    exists (n,m). auto.
    destruct H9.
    exists (g x0).
    split; auto.
    apply member_eq with (f q', g x0).
    destruct H8; split; split; simpl; auto.
    apply map_rel_in. auto.
    hnf; intros.
    apply image_axiom2 in H11. destruct H11 as [y [??]].
    rewrite H12.
    destruct y as [y1 y2]. simpl.
    simpl in H12.
    rewrite H3 in H11.
    apply unmap_rel in H11.
    destruct H11 as [y1' [y2' [?[??]]]].
    rewrite <- H14.
    apply embed_mono.
    apply H10.
    apply image_axiom1'.
    exists (y1',y2'). split; simpl; auto.
  Qed.

  Definition exp_fmap_func (X:joinable_relation hf A C) : joinable_relation hf B D :=
    match X with
    | exist G H => exist (is_joinable_relation hf) 
                         (map_rel f g G)
                         (is_joinable_map_rel G H)
    end.


  Program Definition unimage_jrel (y:finset (B×D)%cat_ob) :=
    esubset
      (fun ac =>
        exists b d, (b,d) ∈ y /\ b ≤ f (fst ac) /\ g (snd ac) ≤ d)
      _
      (eprod (eff_enum A (PLT.effective A)) (eff_enum C (PLT.effective C))).
  Next Obligation.
    intros.
    apply semidec_ex. apply PLT.effective.
    apply semidec_ex. apply PLT.effective.
    apply semidec_conj.
    apply semidec_in_finset.
    apply (OrdDec _ (eff_ord_dec _ (effective_prod (PLT.effective B) (PLT.effective D)))).
    simpl. intros.
    split; simpl.
    destruct H as [[??]?]; auto.
    destruct H as [[??]?]; auto.
    apply semidec_conj.
    apply dec_semidec; simpl; intros.
    apply (use_ord H0).
    destruct H as [[??][??]]; auto.
    destruct H2. auto.
    apply embed_mono.
    destruct H as [[??][??]]; auto.
    destruct H.
    destruct H; auto.
    apply eff_ord_dec. apply PLT.effective.
    apply dec_semidec; simpl; intros.
    apply (use_ord H0).
    apply embed_mono.
    destruct H.
    destruct H1.
    destruct H1.
    destruct H1. auto.
    destruct H.
    destruct H.
    auto.
    apply eff_ord_dec. apply PLT.effective.
  Qed.

  Lemma unimage_jrel_order (y:joinable_relation hf B D) :
    ((forall (x x' : A) (y0 y' : C),
     x ≤ x' ->
     y' ≤ y0 ->
     (x, y0) ∈ unimage_jrel (proj1_sig y) ->
     (x', y') ∈ unimage_jrel (proj1_sig y))).
  Proof.
    intros.
    apply esubset_elem in H1.
    destruct H1.
    apply esubset_elem.
    split.
    apply eprod_elem; split; apply eff_complete.
    destruct H2 as [b [d [?[??]]]].
    exists b. exists d. simpl; split; auto.
    simpl in *.
    split.
    transitivity (f x); auto.
    apply embed_mono; auto.
    transitivity (g y0); auto.
    apply embed_mono; auto.
  Qed.    

  Lemma unimage_jrel_directed (y:joinable_relation hf B D) :
    (forall a : A,
     directed hf
       (erel_image A C {| orddec := eff_ord_dec A (PLT.effective A) |}
          (unimage_jrel (proj1_sig y)) a)).
  Proof.
    intro a.
    apply prove_directed.
    generalize (refl_equal hf).
    pattern hf at 2. case hf; intros.
    pattern hf at 1. rewrite H. auto.
    pattern hf at 1. rewrite H.

    destruct y as [y [Hy1 Hy2]]. simpl in *.
    destruct (mub_complete (PLT.plotkin B) nil) with (f a) as [q [??]].
    simpl.
    pattern hf at 4. rewrite H. hnf; auto.
    hnf; intros. apply nil_elem in H0. elim H0.
    destruct (Hy2 nil) with q.
    pattern hf at 3. rewrite H. hnf; auto.
    hnf; intros. apply nil_elem in H2. elim H2.
    simpl. auto.
    destruct H2.
    generalize (embed_directed0 g x).
    pattern hf at 1. rewrite H.
    intros [x' ?].
    exists x'.
    apply erel_image_elem.
    apply esubset_elem.
    split.
    apply eprod_elem; split; apply eff_complete.
    exists q. exists x. split; simpl; auto.
    
    simpl; intros.
    apply erel_image_elem in H.
    apply erel_image_elem in H0.
    apply esubset_elem in H.
    apply esubset_elem in H0.
    destruct H as [_ ?].
    destruct H0 as [_ ?].
    destruct H as [p [q [?[??]]]].
    destruct H0 as [p' [q' [?[??]]]].
    simpl in *.
    
    destruct y as [y [Hy1 Hy2]]. simpl in *.
    destruct (mub_complete (PLT.plotkin B) (p::p'::nil)) with (f a) as [m [??]].
    apply elem_inh with p. apply cons_elem; auto.
    hnf; intros.
    apply cons_elem in H5. destruct H5. rewrite H5.
    auto.
    apply cons_elem in H5. destruct H5. rewrite H5.
    auto.
    apply nil_elem in H5. elim H5.
    destruct (Hy2 ((p,q)::(p',q')::nil)) with m as [n [??]].
    eapply elem_inh. apply cons_elem; eauto.
    hnf; simpl; intros.
    apply cons_elem in H7. destruct H7. rewrite H7.
    auto.
    apply cons_elem in H7. destruct H7. rewrite H7.
    auto.
    apply nil_elem in H7. elim H7.
    simpl. auto.
    simpl in H8.
    destruct (embed_directed2 g n x y0) as [z [?[??]]].
    transitivity q; auto.
    apply H8. apply cons_elem; auto.
    transitivity q'; auto.
    apply H8.
    apply cons_elem; right.
    apply cons_elem; auto.
    exists z. split; auto. split; auto.
    apply erel_image_elem.
    apply esubset_elem.
    split.
    apply eprod_elem; split; apply eff_complete.
    exists m. exists n. split; simpl; auto.
  Qed.

  Program Definition exp_fmap : PLT.exp A C ⇀ PLT.exp B D :=
    Embedding hf (PLT.exp A C) (PLT.exp B D) exp_fmap_func _ _ _ _.
  Next Obligation.
    simpl; intros.
    destruct a as [X HX].
    destruct a' as [Y HY]. simpl in *.
    hnf; simpl; intros.
    hnf in H; simpl in H.
    apply unmap_rel in H0.
    destruct H0 as [p [q [?[??]]]].
    destruct (H p q) as [m [n [?[??]]]]; auto.
    exists (f m). exists (g n).
    split.
    apply map_rel_in. auto.
    split.
    rewrite <- H1.
    apply embed_mono; auto.
    rewrite <- H2.
    apply embed_mono; auto.
  Qed.
  Next Obligation.
    simpl; intros.
    destruct a as [X HX].
    destruct a' as [Y HY]. simpl in *.
    hnf; simpl; intros.
    hnf in H; simpl in H.
    destruct (H (f a) (g b)) as [m [n [?[??]]]]; auto.
    apply map_rel_in. auto.
    apply unmap_rel in H1.
    destruct H1 as [p [q [?[??]]]].
    exists p. exists q.
    split; auto.
    split.
    apply (embed_reflects f).
    rewrite <- H2; auto.
    apply (embed_reflects g).
    rewrite H3. auto.
  Qed.
  Next Obligation.
    intro y.
    generalize (swell hf A C 
            (PLT.effective A) (PLT.plotkin A) 
            (PLT.effective C) (PLT.plotkin C)
            (unimage_jrel (proj1_sig y))
            (unimage_jrel_order y)
            (unimage_jrel_directed y)).
    intros; simpl in *.
    generalize (refl_equal hf).
    pattern hf at 2. case hf; intros.
    pattern hf at 1. rewrite H0. auto.
    pattern hf at 1. rewrite H0.
    destruct (H nil).
    pattern hf at 3.
    rewrite H0. hnf; auto.
    hnf; simpl; intros. apply nil_elem in H1. elim H1.
    destruct H1 as [?[??]].
    exists (exist _ x H3).
    simpl.
    hnf; simpl; intros.
    apply unmap_rel in H4.
    destruct H4 as [a' [c' [?[??]]]].
    apply H2 in H4.
    unfold unimage_jrel in H4.
    simpl in H4.
    apply esubset_elem in H4.
    destruct H4.
    destruct H7 as [p [q [?[??]]]].
    exists p. exists q.
    split; auto.
    split.
    rewrite <- H5. auto.
    rewrite <- H6. auto.
  Qed.
  Next Obligation.
    intros.
    generalize (swell hf A C 
            (PLT.effective A) (PLT.plotkin A) 
            (PLT.effective C) (PLT.plotkin C)
            (unimage_jrel (proj1_sig y))
            (unimage_jrel_order y)
            (unimage_jrel_directed y)).
    simpl in *; intros.
    destruct (H1 (proj1_sig a ++ proj1_sig b)) as [X [?[??]]].
    destruct a. destruct i.
    simpl.
    generalize i.
    clear.
    destruct hf; intros; hnf; auto.
    destruct i as [q ?].
    exists q. apply app_elem. auto.
    hnf; intros.    
    apply app_elem in H2. destruct H2.
    apply esubset_elem.
    destruct a0 as [p q].
    split. apply eprod_elem; split; apply eff_complete.
    destruct (H (f p) (g q)) as [m [n [?[??]]]].
    destruct a; simpl in *.
    apply map_rel_in. auto.
    exists m. exists n. split; auto.
    destruct a0 as [p q].
    destruct (H0 (f p) (g q)) as [m [n [?[??]]]].
    destruct b; simpl in *.
    apply map_rel_in. auto.
    apply esubset_elem.
    split.
    apply eprod_elem; split; apply eff_complete.
    exists m. exists n. split; auto.

    exists (exist _ X H4).
    split.    
    hnf; simpl; intros.
    apply unmap_rel in H5.
    destruct H5 as [a' [c' [?[??]]]].
    apply H3 in H5.
    apply esubset_elem in H5.
    destruct H5.
    destruct H8 as [m [n [?[??]]]].
    exists m. exists n. split; auto.
    simpl in *.
    split.
    rewrite H9; auto.  
    rewrite <- H10; auto.

    split; hnf; simpl; intros.
    assert ((a0,b0) ∈ X) .
    apply H2. apply app_elem. auto.
    exists a0. exists b0.
    split; auto.
    assert ((a0,b0) ∈ X) .
    apply H2. apply app_elem. auto.
    exists a0. exists b0.
    split; auto.
  Qed.
End exp_functor.

Lemma exp_fmap_ident hf (A B:ob (EMBED hf)) (f:A⇀A) (g:B⇀B) :
  f ≈ id -> g ≈ id ->
  exp_fmap hf A A B B f g ≈ id.
Proof.
  intros.
  apply embed_lift'. intro.
  simpl.
  unfold exp_fmap_func. destruct x; simpl.
  split; hnf; simpl; intros.
  apply unmap_rel in H1.
  destruct H1 as [p [q [?[??]]]].
  exists p. exists q. split; auto.
  split. rewrite <- H2.
  rewrite H. simpl. auto.
  rewrite <- H3. rewrite H0. simpl; auto.
  exists (f a). exists (g b).
  split; auto.
  apply map_rel_in; auto.
  split.
  rewrite H. simpl; auto.
  rewrite H0. simpl; auto.
Qed.

Lemma exp_fmap_compose hf (A B C D E F:ob (EMBED hf)) 
  (f1:B → E) (f2:D → F)
  (g1:A → B) (g2:C → D)
  (h1:A → E) (h2:C → F) :
  f1 ∘ g1 ≈ h1 ->
  f2 ∘ g2 ≈ h2 ->
  exp_fmap hf B E D F f1 f2 ∘ exp_fmap hf A B C D g1 g2 ≈
    exp_fmap hf A E C F h1 h2.
Proof.
  intros.
  apply embed_lift'. intro.
  simpl.
  unfold exp_fmap_func. destruct x; simpl.
  split; hnf; simpl; intros.
  apply unmap_rel in H1.
  destruct H1 as [p [q [?[??]]]].
  apply unmap_rel in H1.
  destruct H1 as [p' [q' [?[??]]]].
  exists (h1 p'). exists (h2 q').
  split.
  apply map_rel_in. auto.
  rewrite <- H. rewrite <- H0.
  split; simpl; auto.
  rewrite <- H2. rewrite <- H4. auto.
  rewrite <- H3. rewrite <- H5. auto.
  
  apply unmap_rel in H1.
  destruct H1 as [p [q [?[??]]]].
  exists (f1 (g1 p)). exists (f2 (g2 q)).
  split.
  apply map_rel_in.
  apply map_rel_in. auto.
  split.
  rewrite <- H2. rewrite <- H. simpl; auto.
  rewrite <- H3. rewrite <- H0. simpl; auto.
Qed.

Lemma exp_fmap_respects hf (A B C D:ob (EMBED hf)) 
   (f f':A → B)
   (g g':C → D) :
   f ≈ f' -> g ≈ g' ->
   exp_fmap hf A B C D f g ≈ exp_fmap hf A B C D f' g'.
Proof.
  intros.
  apply embed_lift'. intro.
  simpl.
  unfold exp_fmap_func. destruct x; simpl.
  split; hnf; simpl; intros.
  apply unmap_rel in H1.
  destruct H1 as [p [q [?[??]]]].
  exists (f' p). exists (g' q).
  split.
  apply map_rel_in. auto.
  split.
  rewrite <- H2.
  rewrite H. auto.
  rewrite <- H3. rewrite H0. auto.

  apply unmap_rel in H1.
  destruct H1 as [p [q [?[??]]]].
  exists (f p). exists (g q).
  split.
  apply map_rel_in. auto.
  split. rewrite <- H2. rewrite H; auto.
  rewrite <- H3. rewrite H0. auto.
Qed.

Program Definition expF hf : functor (PROD (EMBED hf) (EMBED hf)) (EMBED hf) :=
    Functor (PROD (EMBED hf) (EMBED hf)) (EMBED hf) 
      (fun X => (@PLT.exp hf
                   (@obl (EMBED hf) (EMBED hf) X) 
                   (@obr (EMBED hf) (EMBED hf) X)))
      (fun (X Y:ob (PROD (EMBED hf) (EMBED hf))) fg =>
        exp_fmap hf (@obl (EMBED hf) (EMBED hf) X)
                    (@obl (EMBED hf) (EMBED hf) Y)
                    (@obr (EMBED hf) (EMBED hf) X)
                    (@obr (EMBED hf) (EMBED hf) Y)
                    (@homl (EMBED hf) (EMBED hf) X Y fg) 
                    (@homr (EMBED hf) (EMBED hf) X Y fg))
      _ _ _.
Next Obligation.
  simpl; intros.
  destruct A as [A B]. destruct f as [f g]. simpl.
  destruct H. simpl in *.
  apply exp_fmap_ident; auto.
Qed.
Next Obligation.
  simpl; intros.
  destruct A as [A A']. 
  destruct B as [B B'].
  destruct C as [C C']. simpl in *.
  destruct f as [f f'].
  destruct g as [g g'].
  destruct h as [h h']. simpl in *.
  destruct H; simpl in *.
  symmetry. apply exp_fmap_compose; auto.
Qed.
Next Obligation.
  simpl; intros.
  destruct A as [A A']. 
  destruct B as [B B'].
  destruct f as [f f'].
  destruct g as [g g'].
  destruct H; simpl in *.
  apply exp_fmap_respects; auto.
Qed.


Section expF_decompose.
  Variable hf:bool.
  Variable I:directed_preord.
  Variables DS1 DS2 : directed_system I (EMBED hf).
  Variable CC1 : cocone DS1.
  Variable CC2 : cocone DS2.

  Hypothesis decompose1 : forall x:cocone_point CC1,
    { i:I & { a:ds_F DS1 i | cocone_spoke CC1 i a ≈ x }}.
  Hypothesis decompose2 : forall x:cocone_point CC2,
    { i:I & { a:ds_F DS2 i | cocone_spoke CC2 i a ≈ x }}.

  Lemma finrel_decompose
    (X:finset (PLT.ord (cocone_point CC1) × PLT.ord (cocone_point CC2))%cat_ob) :
    forall (Hinh : inh hf X),
    { k:I & { Y:finset (PLT.ord (ds_F DS1 k) × PLT.ord (ds_F DS2 k))%cat_ob |
       X ≈ map_rel (cocone_spoke CC1 k) (cocone_spoke CC2 k) Y }}.
  Proof.
    induction X; intros.
    destruct hf. hnf in Hinh.
    elimtype False. destruct Hinh. apply nil_elem in H. auto.
    destruct (choose_ub_set I nil).
    hnf. auto.
    exists x. exists nil. simpl; auto.
    case_eq X; intros.
    destruct a as [a b].
    destruct (decompose1 a) as [i [a' ?]].
    destruct (decompose2 b) as [j [b' ?]].
    destruct (choose_ub I i j) as [k [??]].
    exists k.
    exists ((ds_hom DS1 i k H0 a', ds_hom DS2 j k H1 b')::nil).
    simpl.
    apply finset_cons_eq; auto.
    cut (b ≈ cocone_spoke CC2 k (ds_hom DS2 j k H1 b')).
    cut (a ≈ cocone_spoke CC1 k (ds_hom DS1 i k H0 a')).
    intros [??] [??]; split; split; auto.    
    rewrite <- e.
    rewrite (cocone_commute CC1 i k H0). auto.
    rewrite <- e0.
    rewrite (cocone_commute CC2 j k H1). auto.
    rewrite <- H.
    destruct IHX as [k [Y ?]].
    rewrite H.
    eapply elem_inh. apply cons_elem. eauto.
    destruct a as [p q]. simpl in *.
    destruct (decompose1 p) as [i [p' ?]].
    destruct (decompose2 q) as [j [q' ?]].
    destruct (choose_ub_set I (i::j::k::nil)) as [m ?].
    assert (i≤m).
    apply u. apply cons_elem; auto.
    assert (j≤m).
    apply u. 
    apply cons_elem; right.
    apply cons_elem; auto.
    assert (k≤m).
    apply u. 
    apply cons_elem; right.
    apply cons_elem; right.
    apply cons_elem; auto.
    set (Y' := map_rel (ds_hom DS1 k m H2) (ds_hom DS2 k m H2) Y).
    exists m.
    exists ((ds_hom DS1 i m H0 p', ds_hom DS2 j m H1 q')::Y').
    simpl. 
    apply finset_cons_eq; auto.
    cut (cocone_spoke CC2 m (ds_hom DS2 j m H1 q') ≈ q).
    cut (cocone_spoke CC1 m (ds_hom DS1 i m H0 p') ≈ p).
    intros [??] [??]; split; split; auto.
    rewrite <- e0.
    rewrite (cocone_commute CC1 i m H0). auto.
    rewrite <- e1.
    rewrite (cocone_commute CC2 j m H1). auto.
    rewrite e.
    unfold Y'.
    clear. induction Y; simpl; auto.
    destruct a as [a b]. simpl.
    apply finset_cons_eq; auto.
    split; split; simpl.
    rewrite (cocone_commute CC1 k m H2). auto.
    rewrite (cocone_commute CC2 k m H2). auto.
    rewrite (cocone_commute CC1 k m H2). auto.
    rewrite (cocone_commute CC2 k m H2). auto.
  Qed.
End expF_decompose.

Lemma expF_continuous hf : continuous_functor (expF hf).
Proof.
  repeat intro.
  apply decompose_is_colimit.
  simpl. intros.
  destruct x as [x Hx].
  set (DS1 := dir_sys_app DS (fstF _ _)).
  set (DS2 := dir_sys_app DS (sndF _ _)).
  set (CC1 := cocone_app CC (fstF _ _)).
  set (CC2 := cocone_app CC (sndF _ _)).
  destruct (finrel_decompose hf I DS1 DS2 CC1 CC2) with x
    as [k [x' ?]].
  apply colimit_decompose. apply fstF_continuous. auto.
  apply colimit_decompose. apply sndF_continuous. auto.
  destruct Hx; auto.
  exists k.
  assert (is_joinable_relation hf x').
  apply (is_joinable_unmap_rel hf _ _ _ _
    (cocone_spoke CC1 k) (cocone_spoke CC2 k) x').
  split; intros.
  eapply inh_eq. apply e.
  destruct Hx; auto.
  destruct Hx.
  destruct (H2 G) with x0 as [y [??]]; auto.
  rewrite e; auto.
  exists y; split; auto.
  destruct e. apply H5; auto.
  exists (exist _ x' H).
  simpl.
  split; hnf; simpl; intros.
  destruct e. apply H2 in H0.
  exists a. exists b. auto.
  destruct e. apply H1 in H0.
  exists a. exists b. auto.
Qed.
