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

Definition maybe A B (b:B) (f:A->B) (x:option A) : B :=
  match x with
  | None => b
  | Some x => f x
  end.
Arguments maybe [A B] b f x.

(*
  Variable Idec : forall x y:I, {x=y}+{x<>y}.
*)

Module finprod.
Section finprod.
  Variable I:Type.
  Variable Idec : forall (x y:I), {x=y}+{x<>y}.

  Variable A:Type.
  Variable F : A -> PLT.

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

  Definition ty (a:option A) : PLT
    := maybe (PLT.unit false) F a.

  Definition finprod_elem l := forall i:I, PLT.carrier _ (ty (lookup i l)). 
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
      { forall i a, lookup i l2 = Some a -> x i ≤ y i } + 
      { exists i, x i ≰ y i }).
    intros.
    destruct (X nil l); clear X; auto.
    simpl; intuition.
    discriminate.
    left. intro i'.
    generalize (o i'). clear o.
    generalize (x i'). generalize (y i').
    destruct (lookup i' l). intros.
    apply (H a); auto. 
    simpl; intros. destruct c0. destruct c. auto.
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
    case_eq (eff_enum (PLT.cls_ord false (F a) (PLT.class false (F a)))
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
 

End finprod.
End finprod.