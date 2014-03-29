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

Require Import atoms.
Require Import permutations.

(** * Finite products for type contexts

  *)

(**  First, a short development of cast morphisms.  These are
     useful for dealing wiht cases where we have types that
     are provably equal, but not convertable.
  *)
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


(**  The input module type for contexts.  Type [I] is the
     index type, but type [A] are proxies for object language
     types.  The functon [F] interprets the types [A] as objects
     of PLT.
  *)
Module Type FINPROD_INPUT.
  Parameter Inline A:Type.
  Parameter Inline F: A -> PLT.
End FINPROD_INPUT.

(**  This module type provides an object of contexts, which is
     the universal object for finite collections of objects.

     These are designed specifically to handle contexts of
     typed λ-calculi.
  *)
Module Type FINPROD.
  Parameter Inline A:Type.
  Parameter Inline F: A -> PLT.

  Fixpoint lookup (i:atom) (l:list (atom*A)) : option A :=
    match l with
    | nil => None
    | (i',a)::l' =>
         match string_dec i' i with
         | left Hi => Some a
         | right _ => lookup i l'
         end
    end.
  
  Lemma lookup_eq : forall i i' a ls,
    i = i' ->
    Some a = if string_dec i i' then Some a else lookup i' ls.
  Proof.
    intros.
    destruct (string_dec i i'). reflexivity.
    elim n. auto.
  Defined.
  
  Lemma lookup_neq : forall i i' a ls,
    i <> i' ->
    lookup i' ls = if string_dec i i' then Some a else lookup i' ls.
  Proof.
    intros.
    destruct (string_dec i i'). elim H; auto.
    auto.
  Defined.

  Definition ty (a:option A) : PLT := maybe 1 F a.

  Parameter finprod : list (atom*A) -> PLT.
  Parameter proj : forall ls i, finprod ls → ty (lookup i ls).
  Parameter mk_finprod : forall ls (X:PLT),
       (forall i, X → ty (lookup i ls)) -> X → finprod ls.
  
  Definition bind ls i a : finprod ls × F a → finprod ((i,a)::ls) :=
   mk_finprod ((i,a)::ls) (finprod ls × F a)
   (fun i' => 
     match string_dec i i' as Hi return
       (finprod ls × F a) → ty (if Hi then Some a else lookup i' ls)
     with
     | left _  => π₂
     | right _ => proj ls i' ∘ π₁
     end).
  
  Lemma unbind_lemma ls i i' : lookup i ls = None -> i = i' -> None = lookup i' ls.
  Proof.
    intuition; subst; auto.
  Defined.

  Definition unbind ls i a (Hi:lookup i ls = None) : 
    finprod ((i,a)::ls) → finprod ls :=

    mk_finprod ls (finprod ((i,a)::ls))
     (fun i' =>
       match string_dec i i' as Hi return
         ty (if Hi then Some a else lookup i' ls) → ty (lookup i' ls)
       with
       | left H => cast ty (unbind_lemma ls i i' Hi H) ∘ PLT.terminate _ _ 
       | right _ => id
       end ∘ proj ((i,a)::ls) i').

  Axiom finprod_proj_commute : forall ls i X f,
    proj ls i ∘ mk_finprod ls X f ≈ f i.

  Axiom finprod_universal : forall ls X f (z:X → finprod ls),
    (forall i, proj ls i ∘ z ≈ f i) -> z ≈ mk_finprod ls X f.

  Axiom bind_unbind : forall ls i a Hi,
    unbind ls i a Hi ∘ bind ls i a ≈ π₁.

  Axiom proj_bind_neq : forall i a i' ls (Hneq:i <> i'),
    proj ((i,a)::ls) i' ∘ bind ls i a 
      ≈ cast ty (lookup_neq i i' a ls Hneq) ∘ proj ls i' ∘ π₁.

  Axiom proj_bind_eq : forall i a i' ls (Heq:i = i'),
    proj ((i,a)::ls) i' ∘ bind ls i a 
      ≈ cast ty (lookup_eq i i' a ls Heq) ∘ π₂.

  Axiom proj_bind : forall i a i' ls,
    proj ((i,a)::ls) i' ∘ bind ls i a ≈
    match string_dec i i' as H return 
      finprod ls × F a → ty (if H then Some a else  lookup i' ls)
    with
    | left  Heq  => π₂
    | right Hneq => proj ls i' ∘ π₁
    end.

  Axiom mk_finprod_compose_commute : forall ls X Y f (h:X → Y),
    mk_finprod ls Y f ∘ h ≈
    mk_finprod ls X (fun i => f i ∘ h).

End FINPROD.


Module finprod (FI:FINPROD_INPUT) <: FINPROD.
  Include FI.

  Fixpoint lookup (i:atom) (l:list (atom*A)) : option A :=
    match l with
    | nil => None
    | (i',a)::l' =>
         match string_dec i' i with
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
    destruct (string_dec i' i); auto.
  Qed.

  Lemma lookup_eq : forall i i' a ls,
    i = i' ->
    Some a = if string_dec i i' then Some a else lookup i' ls.
  Proof.
    intros.
    destruct (string_dec i i'). reflexivity.
    elim n. auto.
  Defined.
  
  Lemma lookup_neq : forall i i' a ls,
    i <> i' ->
    lookup i' ls = if string_dec i i' then Some a else lookup i' ls.
  Proof.
    intros.
    destruct (string_dec i i'). elim H; auto.
    auto.
  Defined.

  Definition ty (a:option A) : PLT := maybe 1 F a.

  Module internals.

  Inductive finprod_codom (avd:list atom) z i :=
    | codom_avoid : In i avd -> finprod_codom avd z i
    | codom_elem : ~In i avd -> ty z -> finprod_codom avd z i.
  Arguments codom_avoid [avd z i] H.
  Arguments codom_elem [avd z i] H x.

  Definition finprod_elem (avd:list atom) ls := 
    forall i, finprod_codom avd (lookup i ls) i.

  Definition finprod_codom_ord avd z i (x y:finprod_codom avd z i) :=
      match x, y with
      | codom_avoid _, codom_avoid _ => True
      | codom_elem _ a, codom_elem _ b => a ≤ b
      | _, _ => False
      end.
  
  Program Definition finprod_codom_ord_mixin avd z i : 
    Preord.mixin_of (finprod_codom avd z i) :=
    Preord.Mixin (finprod_codom avd z i) (finprod_codom_ord avd z i) _ _.
  Next Obligation.
    intros. red. destruct x; auto.
  Qed.
  Next Obligation.
    intros. unfold finprod_codom_ord in *.
    destruct x; destruct y; intuition.
    destruct z0; auto.
    transitivity c0; auto.
  Qed.

  Canonical Structure codom avd z i := 
    Preord.Pack (finprod_codom avd z i) (finprod_codom_ord_mixin avd z i).

  Definition codom_enum avd z i (n:N) : option (finprod_codom avd z i) :=
    match In_dec string_dec i avd with
    | left Hin => Some (codom_avoid Hin)
    | right Hnin =>
        match eff_enum _ (PLT.effective (ty z)) n with
        | None => None
        | Some x => Some (codom_elem Hnin x)
        end
    end.

  Program Definition codom_eff avd z i : effective_order (codom avd z i)
   := EffectiveOrder (codom avd z i) _ (codom_enum avd z i) _.
  Next Obligation.
    intros. destruct x; destruct y.
    left; hnf; auto.
    right; intro H; elim H.
    right; intro H; elim H.
    destruct (eff_ord_dec _ (PLT.effective (ty z)) c c0).
    left; auto. right; auto.
  Qed.
  Next Obligation.
    intros. unfold codom_enum. destruct x. 
    exists 0%N.
    destruct (in_dec string_dec i avd). split; hnf; auto.
    contradiction.
    destruct (in_dec string_dec i avd). contradiction.
    destruct (eff_complete _ (PLT.effective (ty z)) c). exists x.
    match goal with [|- match (match ?X with _ => _ end) with _ => _ end ] => destruct X end.
    destruct H; split; auto.
    auto.
  Qed.

  Definition codom_out avd z i (Hnin:~In i avd)
    (x:codom avd z i) : ty z :=
    match x with
    | codom_avoid H => False_rect _ (Hnin H)
    | codom_elem H x => x
    end.

  Program Definition codom_out' avd z i (Hnin:~In i avd) :
    Preord.hom (codom avd z i) (ty z) 
    :=
    Preord.Hom _ _ (codom_out avd z i Hnin) _.
  Next Obligation.
    repeat intro. destruct a. contradiction.
    destruct b. contradiction.
    simpl. auto.
  Qed.

  Program Definition codom_in' avd z i (Hnin:~In i avd) :
    Preord.hom (ty z) (codom avd z i)
    := Preord.Hom _ _ (@codom_elem avd z i Hnin) _.
  Next Obligation.
    intros; auto.
  Qed.

  Lemma codom_has_normals avd z i : has_normals (codom avd z i) (codom_eff avd z i) false.
  Proof.
    repeat intro.
    destruct (In_dec string_dec i avd).
    exists (@codom_avoid avd z i i0 :: nil).
    split.
    red; intros.
    apply cons_elem. left.
    destruct a. split; hnf; auto.
    contradiction.
    split. red; auto.
    repeat intro.
    exists (@codom_avoid avd z i i0).
    split. repeat intro.
    destruct x. hnf; auto. contradiction.
    rewrite finsubset_elem. split; auto.
    apply cons_elem; auto.
    destruct z0. hnf; auto. contradiction.
    intros. rewrite <- H0. auto.

    set (Z' := mub_closure (PLT.plotkin (ty z)) (image (codom_out' avd z i n) X)).
    exists (image (codom_in' avd z i n) Z').
    split. red; intros.
    apply image_axiom1'.
    exists (codom_out' avd z i n a). split.
    simpl. unfold codom_out.
    destruct a; auto. contradiction.
    split; red; simpl; auto.
    unfold Z'.
    apply mub_clos_incl.
    apply image_axiom1'. exists a. split; auto.
    split. red; auto.
    repeat intro.
    destruct (mub_complete (PLT.plotkin (ty z)) (image (codom_out' avd z i n) M) 
      (codom_out' avd z i n z0)).
    red; auto.
    repeat intro.
    apply image_axiom2 in H0. destruct H0 as [q [??]].
    rewrite H1. apply Preord.axiom.
    apply H in H0.
    rewrite finsubset_elem in H0. destruct H0; auto.
    intros. rewrite <- H2; auto.
    destruct H0.   
    exists (codom_in' avd z i n x).
    split.
    repeat intro.
    simpl.
    destruct x0. contradiction.
    apply H0.
    apply image_axiom1'.
    exists (codom_elem n0 c). split; auto.
    rewrite finsubset_elem. split.
    apply image_axiom1. unfold Z'.
    apply mub_clos_mub with (image (codom_out' avd z i n) M); auto.
    red; intros.
    apply image_axiom2 in H2. destruct H2 as [q [??]].
    apply H in H2.    
    rewrite finsubset_elem in H2.    
    destruct H2.
    apply image_axiom2 in H2. destruct H2 as [q' [??]].
    apply member_eq with q'; auto.
    rewrite H3.
    rewrite H5.
    simpl. auto.
    intros. rewrite <- H4; auto.
    simpl. simpl in H1.
    destruct z0. contradiction.
    auto.
    intros. rewrite <- H2. auto.
  Qed.

  Definition codom_plotkin avd z i : plotkin_order false (codom avd z i)
    := norm_plt (codom avd z i) (codom_eff avd z i) false (codom_has_normals avd z i).


  Definition finprod_ord avd l (x y:finprod_elem avd l) := 
    forall i, x i ≤ y i.

  Program Definition finprod_ord_mixin avd l : Preord.mixin_of (finprod_elem avd l) :=
    Preord.Mixin (finprod_elem avd l) (finprod_ord avd l) _ _.
  Next Obligation.
    intros. red. intro; auto.
  Qed.
  Next Obligation.
    intros. red. intro; auto.
    generalize (H i) (H0 i). eauto.
  Qed.

  Canonical Structure ord avd l :=
    Preord.Pack (finprod_elem avd l) (finprod_ord_mixin avd l).

  Definition finprod_dec l avd (x y:finprod_elem avd l) : {x≤y}+{x≰y}.
  Proof.
    unfold finprod_elem in *.
    cut (forall l1 l2,
      (forall i a, lookup i l1 = Some a -> x i ≤ y i) ->
      (l1++l2)%list = l ->
      { forall i a, lookup i l2 = Some a -> x i ≤ y i} + 
      { exists i , x i ≰ y i}).
    intros.
    destruct (X nil l); clear X; auto.
    simpl; intuition.
    discriminate.
    left. intro.
    generalize (o i). clear o.
    destruct (x i); destruct (y i); intuition.
    hnf. auto.
    elim n; auto.
    elim n; auto.
    red; simpl.
    unfold Preord.ord_op in H. simpl in H.
    revert c c0 H.
    simpl.
    destruct (lookup i l). intros.
    eapply H; eauto.
    simpl; intros. hnf. auto.
    right. intro. hnf in H.
    destruct e. apply H0. apply H.

    intros l1 l2. revert l1. induction l2; simpl; intros.
    left. intros. discriminate.

    subst l.
    destruct a as [i a].
    case_eq (x i); case_eq (y i); intros.

    destruct (IHl2 (l1++(i,a)::nil)%list); auto; clear IHl2.
    intros.
    rewrite lookup_app in H2.
    generalize (H i2 a0).
    destruct (lookup i2 l1); auto.
    intros. simpl in H2.
    destruct (string_dec i i2). subst i2; auto.
    hnf. simpl. rewrite H1. rewrite H0. auto.
    discriminate.
    rewrite app_ass; auto.
    left; intros.
    destruct (string_dec i i2). subst i2.
    hnf. rewrite H1. rewrite H0. auto.
    apply o with a0; auto.

    contradiction.
    contradiction.

    destruct (eff_ord_dec _ (PLT.effective 
      (ty (lookup i (l1 ++ (i, a) :: l2))%list))
      c0 c).

    destruct (IHl2 (l1++(i,a)::nil)%list); auto; clear IHl2.
    intros.
    rewrite lookup_app in H2.
    generalize (H i0 a0).
    destruct (lookup i0 l1); auto.
    intros. simpl in H2.
    destruct (string_dec i i0). subst i0; auto.
    hnf. rewrite H1. rewrite H0. auto.
    discriminate.
    rewrite app_ass. auto.
    left. intros. 
    destruct (string_dec i i0).
    subst i0. 
    hnf. rewrite H1. rewrite H0. auto.
    apply o0 with a0; auto.

    right. exists i.
    hnf; intro.
    hnf in H2.
    rewrite H1 in H2. rewrite H0 in H2.
    contradiction.
  Qed.


  Definition f_hd i a ls avd 
    (f:finprod_elem avd ((i,a)::ls)) : finprod_codom avd (Some a) i :=
      match string_dec i i as Hi
        return finprod_codom avd (if Hi then (Some a) else lookup i ls) i ->
               finprod_codom avd (Some a) i
      with
      | left Hi => fun x => x
      | right Hn => False_rect _ (Hn (Logic.eq_refl i))
      end (f i).

  Definition f_tl i a (ls:list (atom*A)) (avd:list atom) 
    (f:finprod_elem avd ((i,a)::ls)) : finprod_elem (i::avd) ls :=
    
    fun i' =>
      match f i' with
      | codom_avoid H  => @codom_avoid (i::avd) _ i' (or_intror H)
      | codom_elem H x => 
         match string_dec i i' as Hi return
           ty (if Hi then Some a else lookup i' ls) -> 
             finprod_codom (i::avd) (lookup i' ls) i'
         with
         | left Hi => fun _ => @codom_avoid (i::avd) _ i' (or_introl Hi)
         | right Hn => fun x' => @codom_elem (i::avd) _ i' (or_ind Hn H) x'
         end x
      end.

  Definition f_cons i a (ls:list (atom*A)) (avd:list atom)
    (h:finprod_codom avd (Some a) i)
    (f:finprod_elem (i::avd) ls) : finprod_elem avd ((i,a)::ls) :=

    fun i' =>
      match in_dec string_dec i' avd with
      | left Hin => codom_avoid Hin
      | right Hnin => @codom_elem avd _ i' Hnin
         match string_dec i i' as Hi
           return ty (if Hi then Some a else lookup i' ls)
         with
         | left Hi => 
             match h with
             | codom_avoid H => False_rect _ (Hnin (eq_rect i (fun i => In i avd) H i' Hi))
             | codom_elem H x => x
             end
         | right Hn =>
             match f i' with
             | codom_avoid H => False_rect _ (or_ind Hn Hnin H)
             | codom_elem H x => x
             end
         end
      end.

  Lemma f_cons_mono i a ls avd
    hd hd' (tl tl':ord (i::avd) ls) :
    hd ≤ hd' ->
    tl ≤ tl' ->
    f_cons i a ls avd hd tl ≤ f_cons i a ls avd hd' tl'.
  Proof.
    repeat intro.
    generalize (H0 i0). clear H0.
    intro. hnf; simpl. hnf in H0.
    unfold f_cons.
    destruct (in_dec string_dec i0 avd). auto.
    simpl.    
    destruct (tl i0).
    destruct (tl' i0).
    simpl. destruct (string_dec i i0).
    subst i0.
    destruct hd. elim n; auto.
    destruct hd'. elim n; auto.
    auto.
    elim (or_ind n0 n i1). elim H0.

    destruct (tl' i0).
    elim H0.
    destruct (string_dec i i0); auto.
    subst i0. elim n1; simpl; auto.
  Qed.

  Lemma f_cons_reflects1 i a ls avd
    hd hd' (tl tl':ord (i::avd) ls) :
    f_cons i a ls avd hd tl ≤ f_cons i a ls avd hd' tl' ->
    hd ≤ hd'.
  Proof.
    intros. generalize (H i). clear H.
    intro. hnf in H. hnf.
    unfold f_cons in *. simpl in *.
    destruct (in_dec string_dec i avd).
    destruct hd. destruct hd'. auto.
    elim n; auto.
    elim n; auto.
    revert H.
    destruct (tl i).
    destruct (tl' i). simpl.
    destruct hd. contradiction.
    destruct hd'. contradiction.
    revert c c0. simpl.
    destruct (string_dec i i); simpl; auto.
    elim n2; auto.
    elim n0; simpl; auto.
    elim n0; simpl; auto.
  Qed.

  Lemma f_cons_reflects2 i a ls avd
    hd hd' (tl tl':ord (i::avd) ls) :
      f_cons i a ls avd hd tl ≤ f_cons i a ls avd hd' tl' ->
      tl ≤ tl'.
  Proof.
    repeat intro. generalize (H i0); clear H.
    intro. hnf. hnf in H. unfold f_cons in *. simpl in *.
    destruct (in_dec string_dec i0 avd).
    destruct (tl i0).
    destruct (tl' i0). auto.
    elim n; auto.
    elim n; simpl; auto.
    destruct (tl i0).
    destruct (tl' i0). auto.
    elim n0; auto.
    destruct (tl' i0).
    elim n0; auto.
    destruct (string_dec i i0). subst i0.
    elim n0; simpl; auto.
    auto.    
  Qed.

  Lemma f_cons_hd_tl i a ls avd 
    (f:ord avd ((i,a)::ls)) :
    forall (hd:codom avd (Some a) i) (tl : ord (i::avd) ls),
      hd ≈ f_hd i a ls avd f ->
      tl ≈ f_tl i a ls avd f ->
      f ≈ f_cons i a ls avd hd tl.
  Proof.
    intros.
    
    cut (forall i',
      finprod_codom_ord _ _ i' (f i') (f_cons i a ls avd hd tl i') /\
      finprod_codom_ord _ _ i' (f_cons i a ls avd hd tl i') (f i')).
    intros; split; intro; apply H1; auto.
    intro i'.
    pose (string_dec i i').
    destruct s. subst i'.

    unfold f_cons, f_tl, f_hd, finprod_codom_ord in *. simpl in *.
    revert H H0; simpl.
    destruct hd.
    destruct (f i).
    destruct (in_dec string_dec i avd). intuition.
    contradiction.
    revert c; simpl.
    destruct (string_dec i i). simpl.
    intros. destruct H. elim H.
    elim n0; auto.
    destruct (f i).
    contradiction.
    destruct (in_dec string_dec i avd). contradiction.
    simpl.
    revert c c0; simpl.
    destruct (string_dec i i).
    simpl; intros.
    destruct H0; auto.
    elim n2. auto.
    
    clear H. unfold f_tl in H0.
    destruct H0. simpl in *.
    generalize (H i') (H0 i'); clear H H0.
    unfold finprod_codom_ord, f_cons; simpl.
    destruct (in_dec string_dec i' avd).
    destruct (f i'); simpl. intros. auto.
    contradiction.
    destruct (f i'); simpl. contradiction.
    revert c; simpl.
    destruct (string_dec i i'); auto.
    elim n; auto.
    intros.
    destruct (tl i').
    destruct i0; contradiction.
    split; auto.
  Qed.

  Fixpoint enum_finprod (ls:list (atom*A)) (avd:list atom) (z:N) : 
    option (finprod_elem avd ls) :=

    match ls as ls' return option (finprod_elem avd ls') with
    | nil => Some (fun i:atom => 
          match in_dec string_dec i avd with 
            | left Hin => codom_avoid Hin 
            | right Hnin => @codom_elem avd None i Hnin tt 
          end)
    | (i,a)::ls' =>
       match in_dec string_dec i avd with
       | left IN =>
         match enum_finprod ls' (i::avd) z with
         | None => None
         | Some f => Some (f_cons i a ls' avd (codom_avoid IN) f)
         end
       | right NIN =>
         let (p,q) := pairing.unpairing z in
         match enum_finprod ls' (i::avd) q with
         | None => None
         | Some f =>
             match eff_enum _ (PLT.effective (F a)) p with
             | None => None
             | Some xi => Some (f_cons i a ls' avd (@codom_elem avd (Some a) i NIN xi) f)
             end
         end
      end
    end.

  Lemma enum_finprod_complete ls : forall avd (f:finprod_elem avd ls),
    f ∈ (enum_finprod ls avd : eset (ord avd ls)).
  Proof.
    induction ls; intros.
    exists 0%N.
    simpl.
    split; intro; hnf; simpl.
    destruct (in_dec string_dec i avd).
    destruct (f i); auto.
    destruct (f i). contradiction.
    hnf; auto.
    destruct (in_dec string_dec i avd).
    destruct (f i); auto.
    destruct (f i). contradiction.
    hnf; auto.
    
    destruct a as [i a].
    hnf. simpl.
    destruct (in_dec string_dec i avd).
    destruct (IHls (i::avd) (f_tl i a ls avd f)).
    exists x.
    simpl in *.
    destruct (enum_finprod ls (i::avd) x).
    apply f_cons_hd_tl.
    unfold f_hd. simpl.
    destruct (f i). clear.
    simpl.
    destruct (string_dec i i). split; hnf; auto.
    elim n; auto.
    contradiction.
    auto. auto.

    simpl in *.
    case_eq (f_hd i a ls avd f); intros.
    contradiction.
    destruct (eff_complete _ (PLT.effective (F a)) c) as [q ?].
    destruct (IHls (i::avd) (f_tl i a ls avd f)) as [p ?].
    exists (pairing.pairing (q,p)).    
    rewrite pairing.unpairing_pairing.
    destruct (enum_finprod ls (i::avd) p).
    match goal with [|- match (match ?X with _ => _ end) with _ => _ end ] => 
      set (X' := X); fold X' in H0
    end.
    cut (match X' with Some a' => c ≈ a' | None => False end); auto.
    destruct X'; auto.
    intros.
    apply f_cons_hd_tl; auto.
    rewrite H. auto.
    auto.
  Qed.

  Program Definition finprod_effective avd ls : effective_order (ord avd ls) :=
    EffectiveOrder (ord avd ls) (finprod_dec ls avd) (enum_finprod ls avd)
      (enum_finprod_complete ls avd).
 
  Program Definition f_cons' i a ls avd :
    Preord.hom 
     (codom avd (Some a) i × ord (i::avd) ls)%cat_ob
     (ord avd ((i,a)::ls))
    :=
    Preord.Hom _ _ (fun hf => f_cons i a ls avd (fst hf) (snd hf)) _.
  Next Obligation.
    intros. destruct H; apply f_cons_mono; auto.
  Qed.

  Program Definition f_hd' i a ls avd :
    Preord.hom (ord avd ((i,a)::ls)) (codom avd (Some a) i)
    :=
    Preord.Hom _ _ (f_hd i a ls avd) _.
  Next Obligation.
    intros. unfold f_hd.
    generalize (H i).
    destruct (a0 i).
    destruct (b i).
    simpl. destruct (string_dec i i); auto.
    elim n; auto.
    contradiction.
    destruct (b i).
    intro. elim H0.
    revert c c0; simpl.
    destruct (string_dec i i); auto.
    elim n1; auto.
  Qed.

  Program Definition f_tl' i a ls avd :
    Preord.hom (ord avd ((i,a)::ls)) (ord (i::avd) ls)
    :=
    Preord.Hom _ _ (f_tl i a ls avd) _.
  Next Obligation.
    intros. 
    unfold f_tl. intro. simpl.
    generalize (H i0).
    destruct (a0 i0).
    destruct (b i0).
    auto. contradiction.
    destruct (b i0). contradiction.
    revert c c0; simpl.
    destruct (string_dec i i0); auto.
  Qed.

  Lemma finprod_has_normals ls avd :
    has_normals (ord avd ls) (finprod_effective avd ls) false.
  Proof.
    revert avd.
    induction ls.
    hnf; simpl; intros.

    hnf. simpl; intros.
    exists ((fun i:atom => 
      match in_dec string_dec i avd with 
      | left Hin => codom_avoid Hin 
      | right Hnin => @codom_elem avd None i Hnin tt
      end)::nil).                          
    split.
    red; intros.
    apply cons_elem. left.
    split; hnf; simpl; intros.
    destruct (a i).
    destruct (in_dec string_dec i avd). auto.
    contradiction.
    destruct (in_dec string_dec i avd). 
    contradiction.
    hnf; auto.
    destruct (a i).
    destruct (in_dec string_dec i avd). auto.
    contradiction.
    destruct (in_dec string_dec i avd). 
    contradiction.
    hnf; auto.
    split. red; auto.
    repeat intro.
    exists (fun i:atom => 
      match in_dec string_dec i avd with 
      | left Hin => codom_avoid Hin 
      | right Hnin => @codom_elem avd None i Hnin tt
      end).
    split.
    repeat intro.
    destruct (x i).
    destruct (in_dec string_dec i avd).
    auto.
    contradiction.
    destruct (in_dec string_dec i avd).
    contradiction.
    hnf; auto.
    rewrite finsubset_elem. split.
    apply cons_elem; auto.
    repeat intro.
    destruct (z i); destruct (in_dec string_dec i avd); try contradiction; hnf; auto.
    intros. rewrite <- H0; auto.

    intros. hnf; simpl; intros.
    destruct a as [i a].
    set (X' := image (f_tl' i a ls avd) X).
    destruct (IHls (i::avd) X') as [Q' [??]]; auto.
    set (A := image (f_hd' i a ls avd) X).
    set (A' := mub_closure (codom_plotkin _ _ _) A).
    set (Z := image (f_cons' i a ls avd) (finprod A' Q')).
    exists Z.
    split.
    red; intros.
    unfold Z.
    apply image_axiom1'.
    exists (f_hd' i a ls avd a0, f_tl' i a ls avd a0).
    split; simpl.
    apply f_cons_hd_tl; auto.
    apply finsets.finprod_elem.
    split.
    unfold A'.
    apply mub_clos_incl. unfold A.
    apply image_axiom1'. exists a0.
    split; simpl; auto.
    apply H.
    unfold X'.
    apply image_axiom1'. exists a0.
    simpl; auto.

    split. red; auto.
    repeat intro.
    destruct H0.
    destruct (H2 (f_tl i a ls avd z) (image (f_tl' i a ls avd) M))
      as [q_tl [??]]; auto.
    red; intros.
    apply image_axiom2 in H3.
    destruct H3 as [y [??]].
    rewrite finsubset_elem.
    apply H1 in H3.
    rewrite finsubset_elem in H3.
    destruct H3.
    unfold Z in H3.
    apply image_axiom2 in H3.
    destruct H3 as [y' [??]].
    destruct y'. apply finsets.finprod_elem in H3.
    destruct H3. simpl in H6.
    assert ((f_cons i a ls avd (f_hd i a ls avd y) (f_tl i a ls avd y) : ord _ _)
        ≈ f_cons i a ls avd c c0).
    rewrite <- H6. symmetry.
    apply f_cons_hd_tl; auto.
    destruct H8.
    apply f_cons_reflects2 in H8.
    apply f_cons_reflects2 in H9.
    split. rewrite H4.
    simpl. apply member_eq with c0; auto.
    destruct H4; auto. simpl in H4.
    rewrite H4.
    apply f_tl'_obligation_1. auto.
    intros. rewrite <- H5; auto.
    intros. rewrite <- H5; auto.

    destruct (mub_complete (codom_plotkin _ _ _) 
      (image (f_hd' i a ls avd) M) (f_hd i a ls avd z))
    as [u [??]]. red; auto.
    red; simpl; intros.
    apply image_axiom2 in H5.
    destruct H5 as [u' [??]]. rewrite H6.
    simpl.
    apply f_hd'_obligation_1.
    apply H1 in H5.
    rewrite finsubset_elem in H5. destruct H5; auto.
    intros. rewrite <- H7; auto.

    exists (f_cons i a ls avd u q_tl).
    split.
    red; intros.
    transitivity (f_cons i a ls avd (f_hd i a ls avd x) (f_tl i a ls avd x)).
    apply eq_ord. apply f_cons_hd_tl; auto.
    apply f_cons_mono.
    apply H5.
    apply image_axiom1'. exists x; auto.
    apply H3. apply image_axiom1'. exists x; auto.
    rewrite finsubset_elem.
    split.
    unfold Z.
    apply image_axiom1'. exists (u,q_tl). split; auto.
    apply finsets.finprod_elem. split; auto.
    unfold A'.
    generalize (mub_clos_mub (codom_plotkin _ _ _) (image (f_hd' i a ls avd) X)).
    intros. hnf in H7. unfold A.
    refine (H7 (image (f_hd' i a ls avd) M) (Logic.I) _ u _).
    red; intros.
    apply image_axiom2 in H8.
    destruct H8 as [q [??]].
    rewrite H9.
    generalize H8; intro.
    apply H1 in H8.
    rewrite finsubset_elem in H8.
    destruct H8.
    unfold Z in H8.
    apply image_axiom2 in H8.
    destruct H8 as [q' [??]].
    destruct q'. apply finsets.finprod_elem in H8.
    destruct H8. unfold A' in H8.
    simpl in H12.
    apply member_eq with c; auto.
    simpl.
    assert (q ≈ f_cons i a ls avd (f_hd i a ls avd q) (f_tl i a ls avd q)).
    apply f_cons_hd_tl; auto.
    rewrite H14 in H12.
    destruct H12.
    apply f_cons_reflects1 in H12.
    apply f_cons_reflects1 in H15.
    split; auto.
    intros. rewrite <- H11; auto.
    auto.

    rewrite finsubset_elem in H4. destruct H4; auto.
    intros. rewrite <- H7; auto.
    transitivity (f_cons i a ls avd (f_hd i a ls avd z) (f_tl i a ls avd z)).
    apply f_cons_mono; auto.
    rewrite finsubset_elem in H4. destruct H4; auto.
    intros. rewrite <- H7; auto.
    apply eq_ord. symmetry.
    apply f_cons_hd_tl; auto.
    intros. rewrite <- H7; auto.
  Qed.


  Definition finprod_plotkin ls avd : plotkin_order false (ord avd ls) :=
    norm_plt (ord avd ls) (finprod_effective avd ls) false (finprod_has_normals ls avd).

  Canonical Structure finprod ls avd : PLT :=
    PLT.Ob false (finprod_elem avd ls)
      (PLT.Class _ _
        (finprod_ord_mixin avd ls)
        (finprod_effective avd ls)
        (finprod_plotkin ls avd)).

  Definition empty_cxt_rel (X:PLT) : erel X (finprod nil nil) :=
    eprod (eff_enum _ (PLT.effective X)) (enum_finprod nil nil).

  Program Definition empty_ctx (X:PLT) : X → finprod nil nil :=
    PLT.Hom false X (finprod nil nil) (empty_cxt_rel X) _ _.
  Next Obligation.
    repeat intro. unfold empty_cxt_rel. 
    apply eprod_elem. split. apply eff_complete. 
    apply enum_finprod_complete.
  Qed.
  Next Obligation.
    repeat intro.
    exists (fun i:atom => @codom_elem nil None i (fun H => H) tt).
    split; repeat intro.
    hnf. simpl.
    destruct (x0 i). elim i0.
    hnf; auto.

    apply erel_image_elem.
    apply eprod_elem. split. apply eff_complete. 
    apply enum_finprod_complete.
  Qed.

  Definition proj_rel ls avd (i:atom) (Hnin:~In i avd) 
    : erel (finprod ls avd) (ty (lookup i ls)) :=
    esubset_dec
      (ord avd ls × ty (lookup i ls))%cat_ob
      (fun fx => fst fx i ≥ @codom_elem avd (lookup i ls) i Hnin (snd fx))
      (fun x => eff_ord_dec _ (codom_eff avd (lookup i ls) i) _ _) 
      (eprod (eff_enum _ (PLT.effective (finprod ls avd)))
             (eff_enum _ (PLT.effective (ty (lookup i ls))))).

  Lemma proj_rel_elem ls avd (i:atom) Hnin f x :
    (f,x) ∈ proj_rel ls avd i Hnin <-> f i ≥ @codom_elem avd (lookup i ls) i Hnin x.
  Proof.
    unfold proj_rel. rewrite esubset_dec_elem.
    rewrite eprod_elem. simpl. intuition.
    apply enum_finprod_complete.
    apply eff_complete.
    intros. 
    destruct H as [[??][??]].
    destruct x0; destruct y; simpl in *.
    generalize (H i) (H2 i).
    destruct (c i). elim H0.
    destruct (c1 i). intro. elim H4.
    simpl; intros.
    red; simpl.
    transitivity c0; auto.
    transitivity c3; auto.
  Qed.

  Program Definition proj ls avd i Hnin : finprod ls avd → ty (lookup i ls) :=
    PLT.Hom false (finprod ls avd) (ty (lookup i ls)) (proj_rel ls avd i Hnin) _ _.
  Next Obligation.
    simpl; intros.
    apply proj_rel_elem in H1. apply proj_rel_elem.
    generalize (H i).
    destruct (x i). elim H1.
    destruct (x' i). intros. elim H2.
    simpl; intros.
    red; simpl.
    transitivity y; auto.
    transitivity c; auto.
  Qed.
  Next Obligation.
    repeat intro.
    case_eq (x i); intros. contradiction.
    exists c.
    split.
    repeat intro.
    apply H in H1. apply erel_image_elem in H1.
    apply proj_rel_elem in H1.
    rewrite H0 in H1. auto.
    apply erel_image_elem.
    apply proj_rel_elem.
    rewrite H0; auto.
    red; simpl; auto.
  Qed.

  Definition finprod_codom_weaken avd z i i'
    (x:finprod_codom avd z i) : finprod_codom (i'::avd) z i :=
    match x with
    | codom_avoid H => @codom_avoid (i'::avd) z i (or_intror H)
    | codom_elem H x =>
        match string_dec i' i with
        | left Hi  => @codom_avoid (i'::avd) z i (or_introl Hi)
        | right Hn => @codom_elem (i'::avd) z i (or_ind Hn H) x
        end
    end.

  Definition ord_weaken avd i a ls
    (x:ord avd ((i,a)::ls)) : ord (i::avd) ls :=
    
    fun i' =>
      match string_dec i i' as Hi return
        finprod_codom avd (if Hi then Some a else lookup i' ls) i' ->
        finprod_codom (i::avd) (lookup i' ls) i'
      with
      | left H  => fun _ => @codom_avoid (i::avd) _ i' (or_introl H)
      | right H => finprod_codom_weaken avd _ _ _
      end (x i').

  Program Definition finprod_univ_rel 
      (ls:list (atom*A))
      (avd:list atom)
      (X:PLT)
      (f:forall i, ~In i avd -> X → ty (lookup i ls))
      (Hf : forall i H1 H2, f i H1 ≈ f i H2) :=
      esubset
        (fun q : (PLT.ord X × ord avd ls)%cat_ob =>
          forall i Hnin, exists h,
               (fst q, h) ∈ PLT.hom_rel (f i Hnin) /\
               snd q i ≤ @codom_elem avd (lookup i ls) i Hnin h)
        _
        (eprod (eff_enum _ (PLT.effective X))
               (eff_enum _ (PLT.effective (finprod ls avd)))).
  Next Obligation.
    intros.
    revert avd X f Hf a.
    induction ls; intros.
    apply dec_semidec.
    left. intros. exists tt.
    split.
    destruct (PLT.hom_directed _ _ _ (f i Hnin) (fst a) nil).
    red; auto.
    red; intros. apply nil_elem in H. elim H.
    destruct H. apply erel_image_elem in H0.
    destruct x; auto.
    destruct (snd a i). contradiction.
    hnf; auto.

    destruct a as [i a].
    destruct a0 as [x g]. simpl.
    rename ls into l.
    set (f' i' (Hnin:~In i' (i::avd)) :=
        match string_dec i i' as Hi return
          X → ty (if Hi then Some a else lookup i' l) ->
          X → ty (lookup i' l)
        with
        | left H  => fun _ => False_rect _ (Hnin (or_introl H))
        | right _ => fun x => x
        end (f i' (fun H => Hnin (or_intror H)))).

    cut (semidec
        ((forall (Hnin:~In i avd), exists h,
          (x,h) ∈ PLT.hom_rel (f i Hnin) /\ g i ≤ codom_elem Hnin h)
        /\
        (forall i' (Hnin :~In i' (i::avd)),
          exists h:ty (lookup i' l),
            (x,h) ∈ PLT.hom_rel (f' i' Hnin) /\ 
            (ord_weaken _ _ _ _ g i' ≤ codom_elem Hnin h)))).
      apply semidec_iff.
      split; intros. destruct H.
      pose (string_dec i i0). destruct s.
      subst i0.
      apply H. clear H.
      generalize (H0 i0); clear H0. simpl.
      unfold f'.
      unfold ord_weaken. simpl.
      generalize (f i0). generalize (g i0). simpl.
      destruct (string_dec i i0). contradiction.
      intros. 
      destruct (H (or_ind n Hnin)) as [h' [??]].
      exists h'. split; auto.
      unfold finprod_codom_weaken in H1.
      destruct f0.
      elim H1.
      destruct (string_dec i i0). elim H1. auto.
      
    split; intros.
    apply (H i Hnin).
    generalize (H i' (fun H => Hnin (or_intror H))).
    unfold f', ord_weaken. simpl.
    unfold finprod_codom_weaken.
    generalize (f i'). generalize (g i'). simpl.
    destruct (string_dec i i').
    subst i'. elim Hnin; simpl; auto.
    intros.
    destruct H0 as [h' [??]]. exists h'. split; auto.
    destruct f0; simpl. elim H1. auto.
    apply semidec_conj.
    
    cut (forall (Hnin:~In i avd),
        semidec 
         (exists h : ty (lookup i ((i, a) :: l)),
          (x, h) ∈ PLT.hom_rel (f i Hnin) /\ g i ≤ codom_elem Hnin h)).

        intros.
        destruct (In_dec string_dec i avd).
        apply semidec_iff with True.
        split; intros. contradiction. auto.
        apply semidec_true.     

        apply (Semidec _ (decset _ (X0 n))).
        split; intro. apply decset_correct in H.
        intro. destruct H as [h [??]]; exists h; split; auto.
        destruct (Hf i n Hnin). apply H1; auto.
        apply decset_correct.
        destruct (H n) as [h [??]]. exists h; split; auto.

    intro.
    apply (semidec_ex _ _
        (fun (_:unit) h =>
          (x, h) ∈ PLT.hom_rel (f i Hnin) /\ g i ≤ codom_elem Hnin h)).
    intros. destruct H0; split; auto.
    apply member_eq with (x,b); auto.
    destruct H; split; split; auto.
    rewrite H1.
    destruct H; auto.
    apply PLT.effective.
    intros [??]. simpl.
    apply semidec_conj.
    apply semidec_in.
    constructor. apply eff_ord_dec.
    apply effective_prod; apply PLT.effective.
    apply dec_semidec. 
    apply eff_ord_dec.
    apply codom_eff. exact tt.
    
    refine (IHls (i::avd) X f' _ (x,ord_weaken avd i a l g)).
    unfold f'; simpl; intros.
    generalize (Hf i0).
    generalize (f i0).
    simpl. destruct (string_dec i i0); simpl; auto.
    elim H1; simpl; auto.
  Qed.

  Section finprod_univ_rel.
    Variable ls:list (atom*A).
    Variable avd:list atom.
    Variable X:PLT.
    Variable f:forall i, ~In i avd -> X → ty (lookup i ls).
    Variable Hf : forall i H1 H2, f i H1 ≈ f i H2.

    Let finprod_univ_rel := finprod_univ_rel ls avd X f Hf.

    Lemma finprod_univ_rel_elem : forall x g,
      (x,g) ∈ finprod_univ_rel <->
      forall i Hnin, exists h, (x,h) ∈ PLT.hom_rel (f i Hnin) /\
        g i ≤ @codom_elem avd (lookup i ls) i Hnin h.
    Proof.
      intros. unfold finprod_univ_rel.
      unfold internals.finprod_univ_rel.
      rewrite esubset_elem.
      split; intros.
      destruct H. auto.
      split; auto.
      apply eprod_elem; split; apply eff_complete.
      intros. destruct (H0 i Hnin) as [h [??]].
      exists h; split; auto.
      apply member_eq with (fst a, h); auto.
      destruct H as [[??][??]]; split; split; auto.
      rewrite <- H2.
      destruct H as [[??][??]]; auto.
    Qed.

    Program Definition finprod_univ : X → finprod ls avd
      := PLT.Hom false X (finprod ls avd) finprod_univ_rel _ _.
    Next Obligation.
      intros.
      rewrite finprod_univ_rel_elem in H1.
      rewrite finprod_univ_rel_elem. intros.
      destruct (H1 i Hnin) as [h [??]].
      exists h. split; auto.
      revert H2. apply PLT.hom_order; auto.
      rewrite (H0 i); auto.
    Qed.
    Next Obligation.      
      intro. red; intros.
      assert (Hdec : forall i (Hi:~In i avd) x0,
            {(forall m : finprod ls avd, m ∈ M -> m i ≤ codom_elem Hi x0)} +
            {~ (forall m : finprod ls avd, m ∈ M -> m i ≤ codom_elem Hi x0)}).
        intros.
        destruct (finset_find_dec' _ (fun m:finprod ls avd => m i ≤ codom_elem Hi x0)) with M.
        intros. destruct H0. rewrite (H2 i). auto.
        intros. apply eff_ord_dec. apply codom_eff.
        destruct s. right. intro.
        destruct a. apply H2; auto.
        auto.
       
      assert (forall i (H:~In i avd),
        einhabited
          (esubset_dec _ 
            (fun r => forall m, m ∈ M -> m i ≤ codom_elem H r)
            (Hdec i H)
          (erel_image X (ty (lookup i ls))
           (OrdDec _ (eff_ord_dec X (PLT.effective X)))
           (PLT.hom_rel (f i H)) x))).

      intros. apply member_inhabited.
      set (q (m:finprod ls avd) := codom_out avd (lookup i ls) i H0 (m i)).
      destruct (PLT.hom_directed _ _ _ (f i H0) x (map q M)) as [a [??]]. red; auto.
      red; intros. 
      destruct H1 as [a' [??]]. rewrite H2.
      apply in_map_iff in H1.
      destruct H1 as [a'' [??]]. subst a'.
      unfold q.
      apply erel_image_elem.
      assert (a'' ∈ M).
      exists a''; split; auto.
      apply H in H1. apply erel_image_elem in H1.
      rewrite finprod_univ_rel_elem in H1.
      destruct (H1 i H0) as [h [??]].
      revert H4. apply PLT.hom_order; auto.
      destruct (a'' i). elim H5.
      simpl. auto.
      exists a.
      apply esubset_dec_elem.
      intros. generalize (H4 m H5).
      destruct H3.
      destruct (m i); auto.
      simpl; intros.
      red; simpl. transitivity x0; auto.
      split; auto.
      intros.
      destruct H3 as [?[??]].
      destruct H4.
      rewrite (H4 i).
      assert (q x0 ≤ a).
      apply H1.
      exists (q x0). split; auto.
      apply in_map. auto.
      unfold q in H6.
      destruct (x0 i). contradiction.
      auto.

      set (g i :=
        match In_dec string_dec i avd with
        | left Hin => @codom_avoid avd _ i Hin
        | right Hnin => @codom_elem avd _ i Hnin (choose _ _ (H0 i Hnin))
        end).
      exists g.
      split.
      hnf; intros.
      unfold g. intro i'.
      generalize H1; intros.
      apply H in H1.
      apply erel_image_elem in H1.
      rewrite finprod_univ_rel_elem in H1.
      destruct (in_dec string_dec i' avd).
      destruct (x0 i'). hnf; auto.
      contradiction.
      unfold choose.
      match goal with [ |- context[ (find_inhabitant ?A ?B ?C) ] ] =>
        destruct (find_inhabitant A B C)
      end; simpl.
      destruct s as [?[??]].
      assert (x1 ∈ 
        (esubset_dec (ty (lookup i' ls))
         (fun r : ty (lookup i' ls) =>
          forall m : finprod ls avd, m ∈ M -> m i' ≤ codom_elem n r)
         (Hdec i' n)
         (erel_image X (ty (lookup i' ls))
            {| orddec := eff_ord_dec X (PLT.effective X) |}
            (PLT.hom_rel (f i' n)) x))).
      exists x2. rewrite H3. auto.
      rewrite esubset_dec_elem in H5.
      destruct H5. apply erel_image_elem in H5.
      apply H6. auto.
      intros. generalize (H7 m H8).
      destruct H6.
      destruct (m i'); auto.
      intros. red; simpl. transitivity x3; auto.

      apply erel_image_elem.
      rewrite finprod_univ_rel_elem.
      intros. unfold g.
      destruct (in_dec string_dec i avd). contradiction.
      exists (choose _ _ (H0 i n)).
      split.
      2: red; simpl; auto.
      unfold choose.
      destruct (find_inhabitant  _ _ (H0 i n)); simpl.
      destruct s as [?[??]].
      assert (x0 ∈ 
        (esubset_dec (ty (lookup i ls))
         (fun r : ty (lookup i ls) =>
          forall m : finprod ls avd, m ∈ M -> m i ≤ codom_elem n r)
         (Hdec i n)
         (erel_image X (ty (lookup i ls))
            {| orddec := eff_ord_dec X (PLT.effective X) |}
            (PLT.hom_rel (f i n)) x))).
      exists x1. rewrite H1. auto.
      rewrite esubset_dec_elem in H3.
      destruct H3. apply erel_image_elem in H3.
      destruct (Hf i n Hnin). apply H5; auto.
      intros. generalize (H5 m H6).
      destruct H4.
      destruct (m i); auto.
      intros. red; simpl.
      transitivity x2; auto.
    Qed.

    Lemma finprod_univ_commute : forall i Hnin,
      proj ls avd i Hnin ∘ finprod_univ ≈ f i Hnin.
    Proof.
      intro. split; hnf; simpl; intros.
      destruct a.
      apply PLT.compose_hom_rel in H.
      destruct H as [q [??]].
      simpl in H. rewrite finprod_univ_rel_elem in H.
      destruct (H i Hnin) as [h [??]].
      simpl in H0.
      apply proj_rel_elem in H0.
      revert H1. apply PLT.hom_order; auto.
      rewrite <- H0 in H2. auto.

      destruct a.
      apply PLT.compose_hom_rel.

      assert (exists g:finprod_elem avd ls, g i = @codom_elem avd (lookup i ls) i Hnin c0
        /\ forall i' Hnin', (c,codom_out avd _ i' Hnin' (g i')) ∈ PLT.hom_rel (f i' Hnin')).

        assert (exists g':finprod_elem avd ls,
          forall i' Hnin', (c,codom_out avd _ i' Hnin' (g' i')) ∈ PLT.hom_rel (f i' Hnin')).

          assert (forall i' (Hnin':~In i' avd),
            einhabited (erel_image X (ty (lookup i' ls))
              {| orddec := eff_ord_dec X (PLT.effective X) |}
              (PLT.hom_rel (f i' Hnin')) c)).
          intros. apply member_inhabited.
          destruct (PLT.hom_directed _ _ _ (f i' Hnin') c nil) as [q [??]]; auto.
          red; auto.
          red; intros. apply nil_elem in H0. elim H0.
          exists q; auto.

          set (g i :=
            match In_dec string_dec i avd with
              | left Hin => @codom_avoid avd _ i Hin
              | right Hnin => @codom_elem avd _ i Hnin (choose _ _ (H0 i Hnin))
            end).
          exists g. unfold g; simpl; intros.
          destruct (in_dec string_dec i' avd). contradiction.
          simpl. 
          generalize (choose_elem _ _ (H0 i' n)).
          intros. apply erel_image_elem in H1.
          destruct (Hf i' n Hnin').
          apply H2; auto.

        destruct H0 as [g' ?].
        exists (fun i' =>
          match string_dec i i' with
          | left H => 
               eq_rect i (fun i => finprod_codom avd (lookup i ls) i) (codom_elem Hnin c0) i' H
          | right _ => g' i'
          end).
        split.
        destruct (string_dec i i).
        replace e with (Logic.eq_refl i). simpl. auto.
        apply (Eqdep_dec.UIP_dec string_dec). elim n; auto.
        intros.
        destruct (string_dec i i'); auto.
        subst i'. simpl.
        destruct (Hf i Hnin Hnin'); auto.

      destruct H0 as [g [??]]. exists g.
      split; simpl.
      rewrite finprod_univ_rel_elem.
      intros i' Hi'. 
      exists (codom_out avd _ i' Hi' (g i')).
      split. apply H1.
      destruct (g i'); simpl. contradiction. red; simpl; auto.
      rewrite proj_rel_elem. rewrite <- H0. auto.
    Qed.

    Lemma finprod_univ_axiom : forall (z: X → finprod ls avd),
      (forall i Hi, proj ls avd i Hi ∘ z ≈ f i Hi) -> z ≈ finprod_univ.
    Proof.
      intros. split; repeat intro; destruct a.
      simpl. rewrite finprod_univ_rel_elem.
      intros i Hi. exists (codom_out avd _ i Hi (c0 i)). split.
      destruct (H i Hi). apply H1.
      apply PLT.compose_hom_rel. exists c0.
      split; auto. simpl.
      rewrite proj_rel_elem.
      destruct (c0 i); simpl; auto. contradiction.
      red; simpl; auto.
      destruct (c0 i); simpl; auto. contradiction.
      red; simpl; auto.

      simpl in H0. rewrite finprod_univ_rel_elem in H0.
      assert (forall i (Hi:~In i avd), exists q,
        (c,q) ∈ PLT.hom_rel z /\ c0 i ≤ q i).
      intros.
      destruct (H0 i Hi) as [h [??]].
      destruct (H i Hi). apply H4 in H1.
      apply PLT.compose_hom_rel in H1.
      destruct H1 as [q [??]].
      exists q. split; auto.
      simpl in H5. apply proj_rel_elem in H5.
      rewrite H2. auto.

      clear H H0.

      cut (forall (ls':list (atom*A)), exists h,
        (c,h) ∈ PLT.hom_rel z /\
        forall i x, ~In i avd -> lookup i ls' = Some x -> c0 i ≤ h i).
      intros. destruct (H ls) as [h [??]].
      revert H0. apply PLT.hom_order; auto.
      intro.
      generalize (H2 i).
      destruct (c0 i).
      destruct (h i).
      intro. hnf; auto.
      contradiction.
      destruct (h i).
      contradiction.
      revert c1 c2.
      case (lookup i ls); intros.
      apply (H0 a); auto.
      hnf. auto.

      induction ls'.
      simpl.
      destruct (PLT.hom_directed false _ _ z c nil) as [h0 [??]].
      red; auto.
      red; intros. apply nil_elem in H. elim H.
      apply erel_image_elem in H0.
      exists h0. split; auto.
      intros. discriminate.
      destruct IHls' as [h [??]].
      destruct a. simpl.
      destruct (in_dec string_dec c1 avd).
      exists h. split; auto.
      intros.
      destruct (string_dec c1 i0). subst i0. contradiction.
      apply H0 with x; auto.

      destruct (H1 c1 n) as [q [??]].
      destruct (PLT.hom_directed false _ _ z c (h::q::nil)) as [h' [??]].
      red; auto.
      red; intros.
      apply cons_elem in H4.
      destruct H4. rewrite H4.
      apply erel_image_elem. auto.
      apply cons_elem in H4.
      destruct H4. rewrite H4.
      apply erel_image_elem. auto.
      apply nil_elem in H4. elim H4.

      apply erel_image_elem in H5.
      exists h'. split; auto.
      simpl; intros.
      destruct (string_dec c1 i). subst i.
      inversion H7; subst.
      transitivity (q c1); auto.
      cut (q ≤ h'). intros. apply H8.
      apply H4.
      apply cons_elem. right. apply cons_elem; auto.
      transitivity (h i).
      apply (H0 i x); auto.
      cut (h ≤ h'). intros. apply H8.
      apply H4.
      apply cons_elem; auto.
   Qed.        

  End finprod_univ_rel.
  End internals.

  Definition finprod ls := internals.finprod ls nil.
  Definition proj ls i := internals.proj ls nil i (fun H => H).
  Definition mk_finprod ls X (f:forall i, X → ty (lookup i ls)) : X → finprod ls := 
    internals.finprod_univ ls nil X (fun i _ => f i) (fun i H1 H2 => eq_refl _ _).

  Definition empty_cxt_inh : finprod nil :=
    fun i => @internals.codom_elem nil None i (fun H =>H) tt.

  Lemma empty_cxt_le : forall a b : finprod nil, a ≤ b.
  Proof.
    repeat intro.
    hnf. destruct (a i). destruct (b i). auto. contradiction.
    destruct (b i). contradiction. hnf. auto.
  Qed.
    
  Lemma empty_cxt_uniq : forall a b : finprod nil, a ≈ b.
  Proof.
    intros. split; apply empty_cxt_le.
  Qed.

  Lemma finprod_proj_commute : forall ls i X f,
    proj ls i ∘ mk_finprod ls X f ≈ f i.
  Proof.
    intros. apply internals.finprod_univ_commute.
  Qed.

  Lemma finprod_universal : forall ls X f (z:X → finprod ls),
    (forall i, proj ls i ∘ z ≈ f i) -> z ≈ mk_finprod ls X f.
  Proof.
    intros. apply internals.finprod_univ_axiom.
    intros. rewrite <- (H i).
    apply cat_respects; auto.
    split; simpl.
    hnf; intros.
    destruct a. simpl in H0.
    rewrite internals.proj_rel_elem in H0.
    simpl.
    rewrite internals.proj_rel_elem.
    destruct (c i); auto.
    hnf; intros.
    destruct a. simpl in H0.
    rewrite internals.proj_rel_elem in H0.
    simpl.
    rewrite internals.proj_rel_elem.
    destruct (c i); auto.
  Qed.    

  Definition bind ls i a : finprod ls × F a → finprod ((i,a)::ls) :=
   mk_finprod ((i,a)::ls) (finprod ls × F a)
   (fun i' => 
     match string_dec i i' as Hi return
       (finprod ls × F a) → ty (if Hi then Some a else lookup i' ls)
     with
     | left _  => π₂
     | right _ => proj ls i' ∘ π₁
     end).
  
  Lemma unbind_lemma ls i i' : lookup i ls = None -> i = i' -> None = lookup i' ls.
  Proof.
    intuition; subst; auto.
  Defined.

  Definition unbind ls i a (Hi:lookup i ls = None) : 
    finprod ((i,a)::ls) → finprod ls :=

    mk_finprod ls (finprod ((i,a)::ls))
     (fun i' =>
       match string_dec i i' as Hi return
         ty (if Hi then Some a else lookup i' ls) → ty (lookup i' ls)
       with
       | left H => cast ty (unbind_lemma ls i i' Hi H) ∘ PLT.terminate _ _ 
       | right _ => id
       end ∘ proj ((i,a)::ls) i').

  Lemma bind_unbind ls i a Hi :
    unbind ls i a Hi ∘ bind ls i a ≈ π₁.
  Proof.
    transitivity (mk_finprod ls (PLT.prod (finprod ls) (F a))
      (fun i' => proj ls i' ∘ π₁)).
    apply finprod_universal.
    intros. rewrite (cat_assoc PLT).
    unfold unbind.
    rewrite (finprod_proj_commute ls i0).
    rewrite <- cat_assoc.
    unfold bind.
    rewrite (finprod_proj_commute ((i,a)::ls) i0).
    destruct (string_dec i i0).
    subst i0.
    unfold unbind_lemma; simpl.
    unfold eq_ind_r. simpl.
    cut (cast ty Hi ∘ cast ty (eq_sym Hi) ∘ PLT.terminate false (F a) ∘ π₂ 
      ≈ cast ty Hi ∘ proj ls i ∘ π₁).
    intros.
    rewrite (cast_iso2 _ _ ty _ _ Hi) in H.
    rewrite (cat_ident2 PLT) in H; auto.    
    rewrite <- (cat_assoc PLT). rewrite H.
    rewrite (cat_assoc PLT).
    rewrite (cat_assoc PLT).
    rewrite (cast_iso1 _ _ ty _ _ Hi).
    rewrite (cat_ident2 PLT); auto.
    etransitivity.

    apply plt_terminate_univ.
    symmetry. apply plt_terminate_univ.

    rewrite (cat_ident2 PLT). auto.

    symmetry. apply finprod_universal.
    intros. auto.
  Qed.

  Lemma proj_bind_neq i a i' ls (Hneq:i <> i') :
    proj ((i,a)::ls) i' ∘ bind ls i a 
      ≈ cast ty (lookup_neq i i' a ls Hneq) ∘ proj ls i' ∘ π₁.
  Proof.
    unfold bind.
    rewrite finprod_proj_commute.
    unfold lookup_neq. simpl.
    destruct (string_dec i i').
    contradiction.
    rewrite cast_refl. rewrite (cat_ident2 PLT).
    auto.
  Qed.

  Lemma proj_bind_eq i a i' ls (Heq:i = i') :
    proj ((i,a)::ls) i' ∘ bind ls i a 
      ≈ cast ty (lookup_eq i i' a ls Heq) ∘ π₂.
  Proof.
    unfold bind.
    rewrite finprod_proj_commute.
    unfold lookup_eq. simpl.
    destruct (string_dec i i').
    rewrite cast_refl. rewrite (cat_ident2 PLT). auto.
    contradiction.
  Qed.

  Lemma proj_bind : forall i a i' ls,
    proj ((i,a)::ls) i' ∘ bind ls i a ≈
    match string_dec i i' as H return 
      finprod ls × F a → ty (if H then Some a else  lookup i' ls)
    with
    | left  Heq  => π₂
    | right Hneq => proj ls i' ∘ π₁
    end.
  Proof.
    intros.
    unfold bind.
    rewrite finprod_proj_commute. auto.
  Qed.

  Lemma mk_finprod_compose_commute ls X Y f (h:X → Y) :
    mk_finprod ls Y f ∘ h ≈
    mk_finprod ls X (fun i => f i ∘ h).
  Proof.
    apply finprod_universal. intros.
    rewrite (cat_assoc PLT).
    rewrite (finprod_proj_commute ls). auto.
  Qed.

  Definition inenv (Γ:list (string*A)) (x:string) (σ:A) :=
    lookup x Γ = Some σ.

  Definition env_incl (Γ₁ Γ₂:list (atom*A)):=
    forall x τ, inenv Γ₁ x τ -> inenv Γ₂ x τ.

  Definition env := list (atom*A).

  Definition env_supp (Γ:env) := map (@fst atom A) Γ.

  Canonical Structure env_supported :=
    Supported env env_supp.

  Lemma env_incl_wk (Γ₁ Γ₂:env) y σ :
    env_incl Γ₁ Γ₂ ->
    env_incl ((y,σ)::Γ₁) ((y,σ)::Γ₂).
  Proof.
    unfold env_incl. unfold inenv.
    simpl; repeat intro.
    destruct (string_dec y x); auto.
  Qed.

  Lemma weaken_fresh
    (Γ Γ' : env) (σ: A) x' :
    x' ∉ ‖Γ'‖ -> 
    forall (x : atom) (τ : A),
      inenv Γ' x τ -> inenv ((x', σ) :: Γ') x τ.
  Proof.
    intros.
    unfold inenv. simpl. intros.
    destruct (string_dec x' x).
    assert (x' ∈ (‖Γ'‖)).
    rewrite e.
    revert H0. clear e. 
    induction Γ'; simpl in *; intuition.
    discriminate.
    destruct a. 
    hnf in H0. simpl in H0.
    destruct (string_dec s x).
    apply cons_elem; simpl; auto. left. subst s; auto.
    apply cons_elem; right; auto.
    apply IHΓ'.
    intro.
    apply H.
    apply cons_elem. right; auto.
    auto.
    elim H; auto.
    auto.
  Defined.

Notation cxt := finprod.
Notation castty := (cast ty).

  Definition weaken_denote (Γ Γ':env) (Hwk:env_incl Γ Γ') : cxt Γ' → cxt Γ
      := mk_finprod Γ (cxt Γ')
        (fun i => match lookup i Γ as a return 
                  lookup i Γ = a -> ty (lookup i Γ') → ty a
                with
                | None => fun H => PLT.terminate _ _
                | Some a => fun H => castty (Hwk i a H)
                end refl_equal ∘ proj Γ' i).

  Section varmap.
    Variable tm : env -> A -> Type.
    Variable tm_weaken : 
      forall Γ₁ Γ₂ τ, env_incl Γ₁ Γ₂ -> tm Γ₁ τ -> tm Γ₂ τ.
    Variable tm_var : forall Γ a τ (H:inenv Γ a τ), tm Γ τ.

    Definition varmap  (Γ₁ Γ₂:env) :=
      forall a τ, inenv Γ₁ a τ -> tm Γ₂ τ.

    Definition extend_map Γ Γ' 
      (VAR:varmap Γ Γ') x σ (m:tm Γ' σ) : varmap ((x,σ)::Γ) Γ'.
    Proof.
      red. unfold inenv. simpl; intros.
      destruct (string_dec x a). subst a.
      injection H. intro. subst σ. exact m.
      exact (VAR a τ H).
    Defined.

    Definition weaken_map Γ Γ'
      (VAR:varmap Γ Γ')
      x' σ (Hx:x' ∉ ‖Γ'‖) :
      varmap Γ ((x',σ)::Γ')
      
      := fun a τ H => 
        tm_weaken Γ' ((x', σ) :: Γ') τ (weaken_fresh Γ Γ' σ x' Hx) (VAR a τ H).

    Program Definition newestvar Γ x σ : tm ((x,σ)::Γ) σ := tm_var _ x σ _.
    Next Obligation.
      intros. hnf; simpl.
      destruct (string_dec x x); auto. elim n; auto.
    Defined.

    Definition shift_vars Γ Γ' x x' σ
      (Hx:x' ∉ ‖Γ'‖)
      (VAR:varmap Γ Γ')
      : varmap ((x,σ)::Γ) ((x',σ)::Γ')

    := extend_map Γ ((x', σ) :: Γ')
        (weaken_map Γ Γ' VAR x' σ Hx) 
         x σ (newestvar Γ' x' σ).

    Lemma shift_vars' : forall Γ Γ' x σ,
      let x' := fresh[ Γ' ] in
        varmap Γ Γ' ->
        varmap ((x,σ)::Γ) ((x',σ)::Γ').
    Proof.
      intros.
      refine (shift_vars Γ Γ' x x' σ _ X).

      apply fresh_atom_is_fresh'.
      simpl. red; intros.
      apply app_elem. auto.
    Defined.
  End varmap.

  Class termmodel :=
    TermModel
    { tm : list (atom*A) -> A -> Type
    ; tm_weaken : forall Γ₁ Γ₂ τ, env_incl Γ₁ Γ₂  -> tm Γ₁ τ -> tm Γ₂ τ
    ; tm_subst  : forall Γ₁ Γ₂ τ, varmap tm Γ₁ Γ₂ -> tm Γ₁ τ -> tm Γ₂ τ
    ; tm_var : forall Γ a τ (H:inenv Γ a τ), tm Γ τ
    ; tm_denote : forall Γ τ, tm Γ τ -> finprod Γ → F τ
    ; tm_denote_var : forall Γ i (a : A) (H : inenv Γ i a),
         tm_denote Γ a (tm_var Γ i a H) ≈ castty H ∘ proj Γ i
    }.

  Section varmap2.
    Context {Htm : termmodel}.

    Definition varmap_denote (Γ Γ':env) (VAR:varmap tm Γ Γ') : cxt Γ' → cxt Γ
      := mk_finprod Γ (cxt Γ') 
      (fun i => match lookup i Γ as a return
                  lookup i Γ = a -> cxt Γ' → ty a
                with
                | None => fun H => PLT.terminate _ _
                | Some a => fun H => tm_denote _ _ (VAR i a H)
                end refl_equal).

    Lemma varmap_extend_bind Γ Γ' 
 (VAR:varmap tm Γ Γ') x σ (m:tm Γ' σ) :

  varmap_denote _ _ (extend_map tm Γ Γ' VAR x σ m) ≈
  bind Γ x σ ∘ 〈 varmap_denote _ _ VAR, tm_denote _ _ m〉.
Proof.
  symmetry. unfold varmap_denote at 2.
  apply finprod_universal. intros.
  rewrite (cat_assoc PLT).
  pose (string_dec x i). destruct s.
  subst i.
  rewrite (proj_bind_eq x σ x Γ refl_equal).
  simpl. unfold lookup_eq.
  simpl.
  unfold extend_map. simpl.
  destruct (string_dec x x). simpl.
  unfold eq_rect_r. simpl.
  rewrite cast_refl.
  rewrite (cat_ident2 PLT).
  rewrite PLT.pair_commute2. auto.
  elim n; auto.
  rewrite (proj_bind_neq x σ i Γ n).
  unfold lookup_neq. simpl.
  unfold extend_map; simpl.
  destruct (string_dec x i).
  contradiction.
  rewrite cast_refl.
  rewrite (cat_ident2 PLT).
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  unfold varmap_denote.
  rewrite finprod_proj_commute.
  auto.
Qed.

Lemma varmap_var_id Γ :
  varmap_denote Γ Γ (tm_var Γ) ≈ id.
Proof.
  symmetry. unfold varmap_denote.
  apply finprod_universal.
  intros.
  rewrite (cat_ident1 PLT). simpl.
  cut (forall a H, tm_denote Γ a (tm_var Γ i a H) ≈ castty H ∘ proj Γ i).
  generalize (proj Γ i).
  unfold inenv.
  generalize (tm_var Γ i).
  unfold inenv.
  pattern (lookup i Γ).
  destruct (lookup i Γ); intros.
  rewrite (H a (refl_equal _)).
  rewrite cast_refl. rewrite (cat_ident2 PLT); auto.
  apply plt_terminate_univ.
  apply tm_denote_var.
Qed.

Section varmap_compose.
  Variables Γ₁ Γ₂ Γ₃:env.
  Variable g:varmap tm Γ₂ Γ₃.
  Variable f:varmap tm Γ₁ Γ₂.  

  Program Definition varmap_compose : varmap tm Γ₁ Γ₃ :=
    fun a τ (IN:inenv Γ₁ a τ) => tm_subst Γ₂ Γ₃ τ g (f a τ IN).
End varmap_compose.

Lemma varmap_compose_denote Γ₁ Γ₂ Γ₃ f g :
  (forall i a e,
   tm_denote Γ₃ a (tm_subst Γ₂ Γ₃ a f (g i a e))
   ≈ tm_denote Γ₂ a (g i a e) ∘ varmap_denote Γ₂ Γ₃ f)
  ->
  varmap_denote _ _  (varmap_compose Γ₁ Γ₂ Γ₃ f g) ≈
  varmap_denote _ _ g ∘ varmap_denote _ _ f.
Proof.
  symmetry. apply finprod_universal.
  intros.
  rewrite (cat_assoc PLT).
  unfold varmap_denote at 1.
  rewrite (finprod_proj_commute Γ₁).
  match goal with [ |- _ ≈ _ ?X ] => generalize X end.
  pattern (lookup i Γ₁) at 2 3 4 5 9.
  case (lookup i Γ₁); intros.
  2: apply plt_terminate_univ.
  unfold varmap_compose.
  symmetry. 
  apply H.
Qed.
    
Program Definition subst (Γ:env) (τ₁ τ₂:A) (a:atom)
  (m:tm ((a,τ₂)::Γ) τ₁) (z:tm Γ τ₂) : tm Γ τ₁ :=

  tm_subst ((a,τ₂)::Γ) Γ τ₁ (extend_map tm Γ Γ (tm_var Γ) a τ₂ z) m.

Lemma subst_soundness Γ x σ₁ σ₂ n₁ n₂ :
  (forall Γ τ m Γ' (VAR:varmap tm Γ Γ'),
    tm_denote _ _ (tm_subst Γ Γ' τ VAR m) ≈ 
    tm_denote _ _ m ∘ varmap_denote Γ Γ' VAR) ->

   tm_denote _ _ n₁ ∘ bind Γ x σ₁ ∘ 〈id, tm_denote _ _ n₂ 〉 ≈ 
   tm_denote _ _ (subst Γ σ₂ σ₁ x n₁ n₂).
Proof.
  intro.
  unfold subst.
  rewrite H.
  rewrite <- (cat_assoc PLT).
  apply cat_respects; auto.
  rewrite varmap_extend_bind.
  rewrite varmap_var_id. auto.
Qed.

Lemma weaken_map_denote Γ Γ'
  (VAR:varmap tm Γ Γ')
  x' σ (Hx:x' ∉ ‖Γ'‖) Hx' :

  (forall Γ a m Γ' H,
    tm_denote _ _ m ∘ weaken_denote Γ Γ' H ≈ tm_denote _ _ (tm_weaken Γ Γ' a H m)) ->

  varmap_denote _ _ (weaken_map tm tm_weaken Γ Γ' VAR x' σ Hx)
  ≈
  varmap_denote _ _ VAR ∘ unbind Γ' x' σ Hx'.
Proof.
  symmetry. apply finprod_universal. intros.
  rewrite (cat_assoc PLT).
  unfold varmap_denote.
  rewrite (finprod_proj_commute Γ).
  unfold weaken_map; simpl.
  match goal with [ |- _ ≈ _ ?X ] => generalize X end.

  simpl. 
  pattern (lookup i Γ) at 2 3 4 5 9.
  case (lookup i Γ); intros.
  2: apply plt_terminate_univ.
  rewrite <- H.
  apply cat_respects. auto.
  apply finprod_universal.
  intros. 

  unfold unbind.  
  rewrite (finprod_proj_commute Γ').
  symmetry.
  match goal with [ |- _ ≈ _ ∘ ?X ] => set (p := X) end.
  simpl in *.
  set (p' := proj ((x',σ)::Γ') i0). 
  change p' with p. clear p'.
  generalize p; clear p.
  simpl.
  unfold unbind_lemma. simpl.
  unfold eq_ind_r. simpl.
  unfold weaken_fresh. 
  pattern (string_dec x' i0).
  destruct (string_dec x' i0). subst i0.
  intro.
  apply cat_respects; auto.
  cut (forall e HASDF,
   match
     lookup x' Γ' as a0
     return (lookup x' Γ' = a0 -> PLT.hom (ty (Some σ)) (ty a0))
   with
   | Some a0 =>
       fun H0 : lookup x' Γ' = Some a0 => HASDF a0 H0
   | None =>fun _ : lookup x' Γ' = None => PLT.terminate false (ty (Some σ))
   end e
   ≈ castty
       (eq_ind x'
          (fun y : string => lookup y Γ' = None -> None = lookup x' Γ')
          (fun H0 : lookup x' Γ' = None => eq_sym H0) x'
          (eq_sym Logic.eq_refl) Hx') ∘
      PLT.terminate false (F σ)).
  intro. apply H0.
  generalize (
    castty
       (eq_ind x'
          (fun y : string => lookup y Γ' = None -> None = lookup x' Γ')
          (fun H0 : lookup x' Γ' = None => eq_sym H0) x'
          (eq_sym Logic.eq_refl) Hx') ∘
      PLT.terminate false (F σ)).
  pattern (lookup x' Γ') at 1 3 5 6.
  rewrite Hx'.
  intros.
  symmetry. apply plt_terminate_univ.

  destruct (lookup i0 Γ'); intros.
  rewrite cast_refl. auto.
  apply cat_respects; auto.
  symmetry. apply plt_terminate_univ.
Qed.

Hypothesis Adec : forall x y:A, {x=y}+{x<>y}.

Lemma varmap_denote_proj Γ Γ' (VAR:varmap tm Γ Γ') x σ (i1 i2:inenv Γ x σ) :
  tm_denote _ _ (VAR x σ i2) ≈ castty i1 ∘ proj Γ x ∘ varmap_denote Γ Γ' VAR.
Proof.
  intros.
  unfold varmap_denote.
  rewrite <- (cat_assoc PLT).
  rewrite finprod_proj_commute.
  match goal with [ |- _ ≈ _ ∘  _ ?X ] => generalize X end.
  revert i2.
  red in i1. rewrite i1.
  intros.
  rewrite cast_refl.
  rewrite (cat_ident2 PLT).
  replace i2 with e; auto.
  apply Eqdep_dec.UIP_dec. decide equality.
  
Qed.



Lemma bind_weaken Γ Γ' x σ H :
   bind Γ x σ ∘ PLT.pair_map (weaken_denote Γ Γ' H) id
   ≈ weaken_denote ((x, σ) :: Γ) ((x, σ) :: Γ')
       (env_incl_wk Γ Γ' x σ H) ∘ bind Γ' x σ.
Proof.
  symmetry.
  unfold weaken_denote at 1.
  rewrite mk_finprod_compose_commute.
  symmetry. apply finprod_universal.
  intros.
  rewrite (cat_assoc PLT).
  unfold bind.
  rewrite (finprod_proj_commute ((x,σ)::Γ)).
  symmetry.
  rewrite <- (cat_assoc PLT).
  rewrite finprod_proj_commute. simpl.
  generalize (env_incl_wk Γ Γ' x σ H i).
  unfold env_incl. simpl. unfold inenv. simpl.
  destruct (string_dec x i).
  intros.
  unfold PLT.pair_map.
  rewrite (cat_ident2 PLT).
  symmetry. etransitivity. apply PLT.pair_commute2.
  replace (i0 σ Logic.eq_refl) with (refl_equal (Some σ)).
  rewrite cast_refl. rewrite (cat_ident2 PLT); auto.
  apply Eqdep_dec.UIP_dec. decide equality.

  symmetry.
  unfold PLT.pair_map.
  rewrite <- (cat_assoc PLT).
  rewrite PLT.pair_commute1.
  rewrite (cat_assoc PLT).
  unfold weaken_denote.
  rewrite (finprod_proj_commute Γ).
  rewrite <- (cat_assoc PLT).
  apply cat_respects; auto.
  match goal with [ |- _ ?X ≈ _ ] => generalize X end.
  pattern (lookup i Γ) at 2 3 4 8.
  case (lookup i Γ); auto.
  intros.
  generalize (H i a e) (i0 a e).
  unfold inenv.
  case (lookup i Γ'); intros.
  inversion i1. subst a0.
  replace i1 with (refl_equal (Some a)).
  replace e0 with (refl_equal (Some a)).
  auto.
  apply Eqdep_dec.UIP_dec. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality.
  discriminate.  
Qed.

Lemma proj_weaken Γ Γ' x σ H i :
   castty i ∘ proj Γ x ∘ weaken_denote Γ Γ' H
   ≈ castty (H x σ i) ∘ proj Γ' x.
Proof.
  unfold weaken_denote.
  rewrite <- (cat_assoc PLT).
  rewrite finprod_proj_commute.
  match goal with [ |- _ ∘ (_ ?X ∘ _) ≈ _ ] => generalize X end.
  generalize (H x σ i).
  revert i. unfold inenv.
  pattern (lookup x Γ) at 1 3 4 5 6 7 .
  case (lookup x Γ); intros.
  inversion i. subst a.
  rewrite (cat_assoc PLT). apply cat_respects; auto.
  replace i with (refl_equal (Some σ)).
  rewrite cast_refl. rewrite (cat_ident2 PLT).
  generalize (H x σ e). generalize i0.
  unfold inenv. rewrite i0.
  intros. 
  replace i2 with (refl_equal (Some σ)).
  replace i1 with (refl_equal (Some σ)). auto.
  apply Eqdep_dec.UIP_dec. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality.
  apply Eqdep_dec.UIP_dec. decide equality.
  discriminate.
Qed.

Lemma varmap_shift_bind (Γ Γ':env) x σ VAR :
  (forall Γ₁ Γ₂ a m H, 
    tm_denote Γ₁ a m ∘ weaken_denote Γ₁ Γ₂ H
   ≈ tm_denote Γ₂ a (tm_weaken Γ₁ Γ₂ a H m)) ->

  let x' := fresh[ Γ' ] in
   varmap_denote ((x, σ) :: Γ) ((x', σ) :: Γ')
     (shift_vars' tm tm_weaken tm_var Γ Γ' x σ VAR) ∘
    bind Γ' x' σ
   ≈ bind Γ x σ ∘ PLT.pair_map (varmap_denote Γ Γ' VAR) id.
Proof.
  intro.
  simpl.
  unfold shift_vars'.
  unfold shift_vars.
  simpl.

  rewrite (varmap_extend_bind Γ ((fresh[Γ'],σ)::Γ')
    (weaken_map tm tm_weaken Γ Γ' VAR (fresh_atom (‖Γ'‖ ++ nil)%list) σ
           (fresh_atom_is_fresh' (‖Γ'‖) (‖Γ'‖ ++ nil)%list
              (fun (a : string) (H : a ∈ ‖Γ'‖) =>
               match app_elem atom (‖Γ'‖) nil a with
               | conj _ H1 => H1
               end (or_introl H))))).
  rewrite <- (cat_assoc PLT).
  apply cat_respects; auto.
  rewrite (PLT.pair_compose_commute false).
  unfold PLT.pair_map.
  apply PLT.pair_eq.

  rewrite (weaken_map_denote Γ Γ' VAR).
  rewrite <- (cat_assoc PLT).
  rewrite bind_unbind. auto.
  intros.
  simpl. apply H.

  simpl.
  unfold newestvar. simpl.
  rewrite tm_denote_var.
  rewrite <- (cat_assoc PLT).
  generalize (proj_bind_eq
    (fresh_atom (‖Γ'‖++nil)%list) σ (fresh_atom (‖Γ'‖++nil)%list) Γ' Logic.refl_equal).
  simpl. intros. 
  etransitivity. apply cat_respects. reflexivity.
  apply H0.
  rewrite (cat_assoc PLT).
  match goal with 
    [ |- castty ?H1 ∘ castty ?H2 ∘ π₂ ≈ _ ] =>
    generalize H1 H2
  end.
  intros.
  etransitivity. apply cat_respects. 
  red in i.
  apply (cast_compose false _ ty _ _ _ e i).
  reflexivity.
  etransitivity. apply cat_respects. 
  refine (cast_dec_id false _ ty _
    (Some σ) (Logic.eq_trans e i)).
  decide equality. 
  reflexivity.
  auto.
Grab Existential Variables.
  simpl.
  set (q := fresh [Γ']). simpl in q. fold q.
  cut (q ∉ ‖Γ'‖).
  clearbody q. clear. induction Γ'; simpl; intros; auto.
  destruct a. simpl in *.
  destruct (string_dec c q). subst q.
  elim H. apply cons_elem. simpl; auto.
  apply IHΓ'. intro. apply H. apply cons_elem; auto.
  unfold q. apply fresh_atom_is_fresh'.
  red; intros. apply app_elem. auto.
Qed.
  End varmap2.
  
End finprod.
