(* Copyright (c) 2014, Robert Dockins *)

Require Import Setoid.
Require Import List.
Require Import NArith.

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

Section cast.
  Variable hf:bool.
  Variable A:Type.
  Variable F:A -> PLT.PLT hf.

  Definition cast_rel (x y:A) (H:x = y) : erel (F x) (F y) :=
    esubset_dec
      (PLT.prod (F x) (F y))
      (fun xy => eq_rect x F (fst xy) y H ≥ snd xy)
      (fun xy => eff_ord_dec _ (PLT.effective (F y)) _ _)
      (eprod (eff_enum _ (PLT.effective (F x))) (eff_enum _ (PLT.effective (F y)))).
  
  Lemma cast_rel_elem (x y:A) (H:x = y) a b :
    (a,b) ∈ cast_rel x y H <-> eq_rect x F a y H ≥ b.
  Proof.
    unfold cast_rel. rewrite esubset_dec_elem.
    simpl. intuition.
    apply eprod_elem. split; apply eff_complete.
    intros. destruct H0 as [[??][??]].
    rewrite H4. rewrite H1.
    generalize H0.
    generalize (fst x0). generalize (fst y0).
    case H. simpl. auto.
  Qed.

  Program Definition cast (x y:A) (H:x = y) : F x → F y :=
    PLT.Hom hf (F x) (F y) (cast_rel x y H) _ _.
  Next Obligation.
    intros.
    apply cast_rel_elem in H2. apply cast_rel_elem.
    rewrite H1. rewrite H2.
    case H. simpl. auto.
  Qed.
  Next Obligation.
    repeat intro.    
    exists (eq_rect x F x0 y H). split.
    red; simpl; intros.
    apply H0 in H1.
    apply erel_image_elem in H1.
    apply cast_rel_elem in H1. auto.
    apply erel_image_elem.
    apply cast_rel_elem.
    auto.
  Qed.
    
  Lemma cast_refl x :
    cast x x (Logic.eq_refl x) ≈ id (F x).
  Proof.
    split; hnf; simpl; intros.
    destruct a.
    apply cast_rel_elem in H. simpl in H.
    apply ident_elem. auto.
    destruct a.
    apply ident_elem in H.
    apply cast_rel_elem. simpl. auto.
  Qed.

  Lemma cast_compose x y z H1 H2 :
    cast y z H2 ∘ cast x y H1 ≈ cast x z (Logic.eq_trans H1 H2).
  Proof.
    split; hnf; simpl; intros.
    destruct a. apply PLT.compose_hom_rel in H.
    destruct H as [q [??]].
    simpl in *.
    apply cast_rel_elem in H.
    apply cast_rel_elem in H0.
    apply cast_rel_elem.
    rewrite H0. revert H.
    case H2. simpl. auto.
    apply PLT.compose_hom_rel.
    destruct a. 
    apply cast_rel_elem in H.
    exists (eq_rect x F c y H1).
    split.
    apply cast_rel_elem. auto.
    apply cast_rel_elem.
    rewrite H.
    case H2. simpl. auto.
  Qed.

  Lemma cast_iso1 x y H :
    cast y x (eq_sym H) ∘ cast x y H ≈ id.
  Proof.
    rewrite cast_compose.
    case H. simpl.
    apply cast_refl.
  Qed.

  Lemma cast_iso2 x y H :
    cast x y H ∘ cast y x (eq_sym H) ≈ id.
  Proof.
    rewrite cast_compose.
    case H. simpl.
    apply cast_refl.
  Qed.

  Hypothesis Adec : forall (x y:A), {x=y}+{x<>y}.

  Lemma cast_dec_id : forall x (H:x=x), cast x x H ≈ id.
  Proof.
    intros.
    replace H with (Logic.eq_refl x).
    apply cast_refl.
    apply (Eqdep_dec.UIP_dec Adec).
  Qed.
End cast.
Arguments cast [hf] [A] F [x y] H.

Definition maybe A B (b:B) (f:A->B) (x:option A) : B :=
  match x with
  | None => b
  | Some x => f x
  end.
Arguments maybe [A B] b f x.


Module finprod.
Section finprod.
  Variable hf:bool.
  Variable I:Type.
  Variable Idec : forall (x y:I), {x=y}+{x<>y}.

  Variable A:Type.
  Variable F : A -> PLT.PLT hf.

  Fixpoint lookup (i:I) (l:list (I*A)) : option A :=
    match l with
    | nil => None
    | (i',a)::l' =>
         match Idec i i' with
         | left Hi => Some a
         | right _ => lookup i l'
         end
    end.

  Lemma lookup_app i l1 l2 :
    lookup i (l1++l2) =
    match lookup i l1 with
    | None => lookup i l2
    | Some a => Some a
    end.
  Proof.
    induction l1; simpl; auto.
    destruct a as [i' a].
    destruct (Idec i i'); auto.
  Qed.

  Definition ty (a:option A) : PLT.PLT hf
    := maybe (PLT.unit hf) F a.

  Definition finprod_elem l :=
    forall i:I, PLT.carrier _ (ty (lookup i l)). 

  Definition finprod_ord l (x y:finprod_elem l) := 
    forall i, x i ≤ y i.

  Program Definition finprod_ord_mixin l : Preord.mixin_of (finprod_elem l) :=
    Preord.Mixin (finprod_elem l) (finprod_ord l) _ _.
  Next Obligation.
    repeat intro. auto.
  Qed.
  Next Obligation.
    repeat intro. eauto.
  Qed.

  Canonical Structure ord l :=
    Preord.Pack (finprod_elem l) (finprod_ord_mixin l).

  Definition finprod_dec l (x y:finprod_elem l) : {x≤y}+{x≰y}.
  Proof.
    unfold finprod_elem in *.
    cut (forall l1 l2,
      (forall i a, lookup i l1 = Some a -> x i ≤ y i) ->
      l1++l2 = l ->
      { forall i a, lookup i l2 = Some a -> x i ≤ y i} + 
      { exists i, x i ≰ y i}).
    intros.
    destruct (X nil l); clear X; auto.
    simpl; intuition.
    discriminate.
    left. intro i'.
    generalize (o i'). clear o.
    generalize (x i'). generalize (y i').
    destruct (lookup i' l). intros.
    eapply H; eauto.
    simpl; intros.
    destruct c0. destruct c. auto.
    right. intro.
    destruct e. apply H0.
    apply H.

    intros l1 l2. revert l1. induction l2; simpl; intros.
    left. intros. discriminate.

    subst l.
    destruct a as [i a].
    destruct (eff_ord_dec _ (PLT.effective 
      (ty (lookup i (l1 ++ (i, a) :: l2))))
      (x i) (y i)).
    destruct (IHl2 (l1++(i,a)::nil)); clear IHl2.
    intros.
    destruct (Idec i i0). subst i0. auto.
    clear o.
    generalize (H i0).
    generalize (x i0). generalize (y i0).
    revert H0.
    repeat rewrite lookup_app.
    destruct (lookup i0 l1).
    intros. apply (H1 a0). auto.
    simpl; intros.
    destruct (Idec i0 i).
    elim n; auto.
    discriminate.
    rewrite app_ass. auto.
    left.
    intros.
    destruct (Idec i0 i). subst i0. auto.
    apply (o0 i0 a0); auto.
    right; auto.
    right. exists i. auto.
  Qed.

  Lemma notin_cons (X:Type) (x:X) (l:list X) (a:X) :
    a <> x ->
    ~In a l ->
    ~In a (x::l).
  Proof.
    simpl. intuition.
  Qed.

  Fixpoint enum_finprod (ls:list (I*A)) (z:N) (avoid:list I) : 
    option (forall i:I, ~In i avoid -> ty (lookup i ls)) :=

    match ls as ls' return option (forall i:I, ~In i avoid -> ty (lookup i ls')) with
    | nil => Some (fun i _ => tt)
    | (i,a)::ls' =>
       let (p,q) := pairing.unpairing z in
       match enum_finprod ls' q (i::avoid) with
       | None => None
       | Some f =>
       match In_dec Idec i avoid with
       | left Havd => Some (fun i' (Hin:~In i' avoid) =>
           match Idec i' i as Hi return
             ty (match Hi with left _ => Some a | right _ => lookup i' ls' end)
           with
           | left Heq => False_rect _
                   (Hin (eq_rect i (fun i => In i avoid) Havd i' (eq_sym Heq)))
           | right Hneq => f i' (notin_cons I i avoid i' Hneq Hin)
           end)
       | right Havd =>
       match eff_enum _ (PLT.effective (ty (lookup i ((i,a)::ls')))) p with
       | None => None
       | Some xi => Some (fun i' (Hin:~In i' avoid) =>
           match Idec i' i as Hi return 
             ty (match Hi with left _ => Some a | right _ => lookup i' ls' end)
           with
           | left Heq =>
               match Idec i i as Hi return
                  ty (match Hi with left _ => Some a | right _ => lookup i ls' end) -> F a
               with
               | left Hii => fun xi' => xi'
               | right Hn => False_rect _ (Hn (Logic.eq_refl i))
               end xi
           | right Hneq => f i' (notin_cons I i avoid i' Hneq Hin)
           end)
       end end end
    end.

  Definition f_hd i a (ls:list (I*A)) (avd:list I) Hnin
    (f:forall i':I, ~In i' avd -> ty (lookup i' ((i,a)::ls))) : F a :=
    match Idec i i as Hi return (ty (if Hi then Some a else lookup i ls)) -> F a with
    | left Hi => fun z => z
    | right Hn => False_rect _ (Hn (Logic.eq_refl i))
    end (f i Hnin).

  Definition f_tl i a (ls:list (I*A)) (avd:list I) 
    (f:forall i':I, ~In i' avd -> ty (lookup i' ((i,a)::ls)))
    (i':I) (Hnin:~In i' (i::avd)) : ty (lookup i' ls) :=
    
    match Idec i' i as Hi return (ty (if Hi then Some a else lookup i' ls)) -> ty (lookup i' ls) with
    | left Hi => False_rect _ (Hnin (or_introl (eq_sym Hi)))
    | right Hn => fun z => z
    end (f i' (fun H => Hnin (or_intror H))).

  Definition f_cons i a (ls:list (I*A)) (avd:list I)
    (h:F a)
    (f:forall i':I, ~In i' (i::avd) -> ty (lookup i' ls)) 
    (i':I) (Hnin:~In i' avd) : ty (lookup i' ((i,a)::ls)) :=

    match Idec i' i as Hi return ty (if Hi then Some a else lookup i' ls) with
    | left Hi => h
    | right Hn => f i' (notin_cons I i avd i' Hn Hnin)
    end.

  Lemma enum_finprod_complete (ls:list (I*A)) :
    forall avoid
      (f : forall x : I, ~ In x avoid -> Preord_Eq (ty (lookup x ls)))
      (Hf: forall i H1 H2, f i H1 ≈ f i H2),
      exists n, exists f',
        enum_finprod ls n avoid = Some f' /\
        forall i Hi Hi', f i Hi ≈ f' i Hi'.
  Proof.
    induction ls; simpl; intros.
    exists 0%N. exists (fun _ _ => tt); split; auto.
    destruct a as [i a]. destruct (Idec i i); simpl. 2: elim n; auto.
    set (f' (x:I) (H:~In x (i::avoid)) :=
      match Idec x i as Hxi
        return ty (if Hxi then Some a else lookup x ls) -> ty (lookup x ls)
      with
      | left Hxi => False_rect _ (H (@or_introl _ (In x avoid) (eq_sym Hxi)))
      | right Hxi => fun x => x
      end (f x (fun Hin => H (or_intror Hin)))).
    destruct (IHls (i::avoid) f') as [q [f'' [??]]].
    simpl. intros.
    unfold f'.
    generalize (Hf i0).
    generalize (f i0).
    destruct (Idec i0 i).
    elim H1. auto.
    auto.

    destruct (In_dec Idec i avoid).
    exists (pairing.pairing (0%N,q)).
    econstructor.
    rewrite pairing.unpairing_pairing.
    rewrite H.
    split. auto.
    simpl; intros.
    transitivity (
    match
       Idec i1 i as Hi0 return (ty (if Hi0 then Some a else lookup i1 ls))
     with
     | left Heq =>
       (fun Heq =>
         False_rect (F a)
           (Hi (eq_rect i (fun i2 : I => In i2 avoid) i0 i1 (eq_sym Heq)))) Heq
     | right Hneq => f' i1 (notin_cons I i avoid i1 Hneq Hi)
     end).
    unfold f'. simpl.
    generalize (Hf i1).
    generalize (f i1).
    destruct (Idec i1 i); simpl; intros.
    subst i1. elim Hi; auto. auto.
    generalize (H0 i1).
    generalize (f' i1). generalize (f'' i1). simpl.
    destruct (Idec i1 i).
    subst i1. elim Hi; auto.
    auto.
    
    destruct (eff_complete _ 
      (PLT.effective (ty (if Idec i i then Some a else lookup i ls)))
      (f i n)) as [p ?].
    case_eq (eff_enum (PLT.cls_ord hf (F a) (PLT.class hf (F a)))
       (PLT.effective (F a)) p). simpl; intros.
    exists (pairing.pairing (p,q)).
    econstructor.
    rewrite (pairing.unpairing_pairing).
    rewrite H.
    simpl; intros. rewrite H2. split. reflexivity.
    simpl. intros. 
    transitivity (
    match
       Idec i0 i as Hi0 return (ty (if Hi0 then Some a else lookup i0 ls))
     with
     | left _ => c
     | right Hneq => f' i0 (notin_cons I i avoid i0 Hneq Hi)
     end).
    pose (Idec i0 i).
    destruct s. subst i0.
    revert H1.
    unfold f'. simpl.
    generalize (Hf i).
    generalize (f i).
    destruct (Idec i i). simpl in *. intros.
    rewrite H2 in H3. rewrite <- H3.
    apply H1.
    elim n0. auto.
    unfold f'.
    generalize (Hf i0).
    generalize (f i0).
    destruct (Idec i0 i); simpl in *; intros.
    elim n0; auto.    
    auto.
    generalize (H0 i0).
    generalize (f' i0). generalize (f'' i0).
    destruct (Idec i0 i); intros; auto.
    intros. elimtype False.
    revert H1.
    generalize (f i).
    destruct (Idec i i). simpl in *. intros.
    rewrite H2 in H1. auto.
    elim n0. auto.
  Qed.

  Definition enum_finprod' (ls:list (I*A)) (z:N) : option (finprod_elem ls) :=
    match enum_finprod ls z nil with
    | None => None
    | Some f => Some (fun i => f i (fun H => H))
    end.

  Program Definition finprod_effective ls : effective_order (ord ls) :=
    EffectiveOrder (ord ls) (finprod_dec ls) (enum_finprod' ls) _.
  Next Obligation.  
    unfold enum_finprod'.
    intros.
    hnf in x.
    destruct (enum_finprod_complete ls nil (fun i _ => x i)) as [n [f' [??]]].
    auto.
    exists n. rewrite H.
    split; hnf; simpl; intros; apply H0; auto.
  Qed.    
 
  Lemma finprod_has_normals ls :
    has_normals (ord ls) (finprod_effective ls) hf.
  Admitted.

  Definition finprod_plotkin ls : plotkin_order hf (ord ls) :=
    norm_plt (ord ls) (finprod_effective ls) hf (finprod_has_normals ls).

  Canonical Structure finprod ls : PLT.PLT hf :=
    PLT.Ob hf (finprod_elem ls)
      (PLT.Class _ _
        (finprod_ord_mixin ls)
        (finprod_effective ls)
        (finprod_plotkin ls)).


  Definition empty_cxt_rel (X:PLT.PLT hf) : erel X (finprod nil) :=
    eprod (eff_enum _ (PLT.effective X)) (enum_finprod' nil).

  Program Definition empty_ctx (X:PLT.PLT hf) : X → finprod nil :=
    PLT.Hom hf X (finprod nil) (empty_cxt_rel X) _ _.
  Next Obligation.
    repeat intro. unfold empty_cxt_rel. 
    apply eprod_elem. split. apply eff_complete. apply finprod_effective_obligation_1.
  Qed.
  Next Obligation.
    repeat intro. exists (fun i => tt).
    split; repeat intro.
    destruct (x0 i). auto.
    apply erel_image_elem.
    apply eprod_elem. split. apply eff_complete. apply finprod_effective_obligation_1.
  Qed.


  Definition proj_rel ls (i:I) : erel (finprod ls) (ty (lookup i ls)) :=
    esubset_dec
      (ord ls × ty (lookup i ls))%cat_ob
      (fun fx => (fst fx) i ≥ snd fx)
      (fun x => eff_ord_dec _ (PLT.effective (ty (lookup i ls))) _ _)
      (eprod (eff_enum _ (PLT.effective (finprod ls)))
             (eff_enum _ (PLT.effective (ty (lookup i ls))))).

  Lemma proj_rel_elem ls (i:I) f x :
    (f,x) ∈ proj_rel ls i <-> f i ≥ x.
  Proof.
    unfold proj_rel. rewrite esubset_dec_elem.
    rewrite eprod_elem. simpl. intuition.
    apply finprod_effective_obligation_1.
    apply eff_complete.
    intros. 
    destruct H as [[??][??]].
    transitivity (snd x0); auto.
    transitivity (fst x0 i); auto.
  Qed.

  Program Definition proj ls i : finprod ls → ty (lookup i ls) :=
    PLT.Hom hf (finprod ls) (ty (lookup i ls)) (proj_rel ls i) _ _.
  Next Obligation.
    simpl; intros.
    apply proj_rel_elem in H1. apply proj_rel_elem.
    rewrite H0. rewrite H1. apply H.
  Qed.
  Next Obligation.
    repeat intro.
    exists (x i).
    split.
    repeat intro.
    apply H in H0. apply erel_image_elem in H0.
    apply proj_rel_elem in H0. auto.
    apply erel_image_elem.
    apply proj_rel_elem.
    auto.
  Qed.

  Program Definition bind_rel ls i a : erel (ord ls × F a)%cat_ob
                                            (ord ((i,a)::ls)) :=
    esubset_dec
      ((ord ls × F a) × ord ((i,a)::ls))%cat_ob
      (fun q => match q with
                ((f,x),f') =>
                let g i' :=
                  match Idec i' i as Hi
                    return ty (if Hi then Some a else lookup i' ls) 
                  with
                    | left _ => x
                    | right _ => f i'
                  end  in
                f' ≤ (g: ord ((i,a)::ls)) end)
        _
      (eprod (eprod (eff_enum _ (PLT.effective (finprod ls)))
                    (eff_enum _ (PLT.effective (F a))))
             (eff_enum _ (PLT.effective (finprod ((i,a)::ls))))).
  Next Obligation.
    intros. destruct x as [[f x] f'].
    simpl. apply (finprod_dec ((i,a)::ls)).
  Defined.

  Lemma bind_rel_elem ls i a f x f' :
    ((f,x),f') ∈ bind_rel ls i a <-> 
    forall i',
      f' i' ≤
      match Idec i' i as Hi
        return ty (if Hi then Some a else lookup i' ls) 
        with
        | left _ => x
        | right _ => f i'
      end.
  Proof.
    unfold bind_rel.
    rewrite esubset_dec_elem.
    rewrite eprod_elem.
    intuition.
    apply eprod_elem; split; apply eff_complete.
    apply eff_complete.
    intros.
    destruct x0 as [[??]?].
    destruct y as [[??]?].
    simpl in *.
    intro i0.
    generalize (H0 i0).
    destruct H.
    destruct H as [[??]?]. simpl in *.
    destruct H1 as [[??]?]. simpl in *.
    generalize (H3 i0). generalize (H5 i0).
    generalize (c4 i0). generalize (c1 i0).
    simpl. destruct (Idec i0 i).
    subst i0.
    intros.
    rewrite H6. rewrite H8. auto.
    intros.
    rewrite H6.
    rewrite H8. auto.
  Qed.

  Program Definition bind ls i a : (PLT.prod (finprod ls) (F a)) → finprod ((i,a)::ls) :=
    PLT.Hom hf (PLT.prod (finprod ls) (F a)) (finprod ((i,a)::ls)) (bind_rel ls i a) _ _.
  Next Obligation.
    intros.
    destruct x. destruct x'.
    rewrite (bind_rel_elem ls i a c c0 y) in H1.
    rewrite (bind_rel_elem ls i a c1 c2 y').
    intros. generalize (H1 i').
    generalize (H0 i').
    generalize (y i'). generalize (y' i').
    simpl. destruct (Idec i' i).
    intros.
    destruct H. simpl in *.
    rewrite H2. rewrite H3. auto.
    intros.
    rewrite H2. rewrite H3.
    destruct H. auto.
  Qed.
  Next Obligation.
    repeat intro.
    destruct x as [f x].
    set (g i' :=
                  match Idec i' i as Hi
                    return ty (if Hi then Some a else lookup i' ls) 
                  with
                    | left _ => x
                    | right _ => f i'
                  end).
    exists g. split.
    red; simpl; intros.
    apply H in H0.
    apply erel_image_elem in H0.
    rewrite (bind_rel_elem ls i a f x x0) in H0.
    intro i'.
    unfold g.
    generalize (H0 i').
    generalize (x0 i').
    generalize (f i'). 
    simpl. case (Idec i' i); auto.
    apply erel_image_elem.
    rewrite (bind_rel_elem ls i a f x g).
    unfold g. auto.
  Qed.

  Section proj_bind.
    Variables ls:list (I*A).
    Variable i:I.
    Variable a:A.

    Lemma lookup_eq :
      Some a = if Idec i i then Some a else lookup i ls.
    Proof.
      destruct (Idec i i). reflexivity.
      elim n. auto.
    Defined.

    Lemma lookup_neq : forall i',
      i <> i' ->
      lookup i' ls = if Idec i' i then Some a else lookup i' ls.
    Proof.
      intros.
      destruct (Idec i' i). elim H; auto.
      auto.
    Defined.

    Lemma proj_empty :
      proj nil i ≈ PLT.terminate hf (finprod nil).
    Proof.
      split; hnf; simpl; intros.
      destruct a0.
      apply eprod_elem. split.
      apply finprod_effective_obligation_1.
      apply single_axiom. destruct u. auto.
      destruct a0.
      apply (proj_rel_elem nil i).
      destruct u. destruct (f i). auto.
    Qed.

    Lemma proj_bind_neq : forall
      i' (Hneq:i <> i'),
      proj ((i,a)::ls) i' ∘ bind ls i a ≈ cast ty (lookup_neq i' Hneq) ∘ proj ls i' ∘ PLT.pi1.
    Proof.
      simpl; intros. split; hnf; simpl; intros.
      destruct a0.
      apply PLT.compose_hom_rel in H.
      destruct H as [q [??]]. simpl in *.
      destruct p.
      rewrite (bind_rel_elem ls i a f c0 q) in H.
      rewrite (proj_rel_elem ((i,a)::ls) i' q c) in H0.
      simpl in *.
      apply PLT.compose_hom_rel.
      simpl.
      exists f.
      split. apply pi1_rel_elem. auto.
      apply PLT.compose_hom_rel.
      simpl. exists (f i').
      split.
      rewrite (proj_rel_elem ls i' f (f i')). auto.
      apply cast_rel_elem.
      unfold lookup_neq.
      rewrite H0.
      generalize (H i'). 
      generalize (q i'). simpl.
      case (Idec i' i).
      intros. elim Hneq. auto.
      simpl. auto.
      
      destruct a0 as [[??]?].            
      apply PLT.compose_hom_rel in H.
      simpl in *.
      destruct H as [q [??]].
      apply (pi1_rel_elem _ _ _ _ f c q) in H.
      apply PLT.compose_hom_rel in H0.
      destruct H0 as [q' [??]]. simpl in *.
      apply cast_rel_elem in H1.
      apply PLT.compose_hom_rel.
      simpl.
      apply proj_rel_elem in H0.
      set (g i' :=
                  match Idec i' i as Hi
                    return ty (if Hi then Some a else lookup i' ls) 
                  with
                    | left _ => c
                    | right _ => f i'
                  end).
      exists g. split.
      apply bind_rel_elem.
      unfold g. auto.
      apply (proj_rel_elem ((i,a)::ls) i').
      unfold g.
      rewrite H1. unfold lookup_neq. simpl.
      case (Idec i' i). intro. elim Hneq; auto.
      simpl. intros.
      rewrite H0. apply H.
    Qed.

    Lemma proj_bind : 
      proj ((i,a)::ls) i ∘ bind ls i a ≈ cast ty lookup_eq ∘ PLT.pi2.
    Proof.
      simpl.
      split; hnf; simpl; intros.
      destruct a0.
      apply PLT.compose_hom_rel in H.
      destruct H as [y [??]].
      destruct p.
      rewrite (bind_rel_elem ls i a f c0 y) in H.
      simpl in *.
      rewrite (proj_rel_elem ((i,a)::ls) i y c) in H0.
      apply PLT.compose_hom_rel.
      simpl. exists c0.
      split.
      apply pi2_rel_elem. auto.
      rewrite (cast_rel_elem hf (option A) ty _ _ lookup_eq c0 c).
      rewrite H0.
      rewrite (H i).
      unfold lookup_eq.
      case (Idec i i). simpl; auto.
      intros. elim n; auto.
      
      destruct a0.            
      apply PLT.compose_hom_rel in H.
      apply PLT.compose_hom_rel.
      destruct H as [q [??]].            
      rewrite (cast_rel_elem hf (option A) ty _ _ lookup_eq) in H0.
      simpl in *.
      destruct p.
      apply (pi2_rel_elem _ _ _ _ f c0 q) in H.
      set (g i' :=
                  match Idec i' i as Hi
                    return ty (if Hi then Some a else lookup i' ls) 
                  with
                    | left _ => c0
                    | right _ => f i'
                  end).
      exists g. split.
      apply bind_rel_elem.
      unfold g. auto.
      rewrite (proj_rel_elem ((i,a)::ls) i g c).
      unfold g.
      revert c H0. clear g.
      unfold lookup_eq. simpl.
      case (Idec i i). simpl. intros.
      rewrite H0. auto.
      intros. elim n; auto.
    Qed.
  End proj_bind.

End finprod.
End finprod.
