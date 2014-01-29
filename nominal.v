(* Copyright (c) 2014, Robert Dockins *)

Require Import Setoid.

Require Import basics.
Require Import categories.
Require Import preord.
Require Import sets.
Require Import finsets.
Require Import atoms.
Require Import permutations.

(** * The category of nominal types
  *)

Obligation Tactic := intuition.

Require Import List.

Module Nominal.

Record mixin_of (A:Type) (eq_mixin:Eq.mixin_of A) :=
  Mixin
  { Aeq := Eq.Pack A eq_mixin
  ; papp : perm -> Aeq -> Aeq
  ; support : Aeq -> finset atom
  ; nom_ident : forall a, papp id a ≈ a
  ; nom_comp : forall a p1 p2,
       papp p1 (papp p2 a) ≈ papp (p1 ∘ p2) a
  ; papp_respects : forall p p' a a',
       p ≈ p' -> a ≈ a' -> papp p a ≈ papp p' a'
  ; support_axiom : forall (p:perm) a,
       (forall v, v ∈ support a -> v ∈ Perm.support p -> False) ->
       papp p a ≈ a
  ; support_papp : forall (p:perm) x v,
       v ∈ support x <-> p v ∈ support (papp p x)
  }.

Record ob :=
  Ob
  { carrier :> Type
  ; eq_mixin : Eq.mixin_of carrier
  ; nominal_mixin : mixin_of carrier eq_mixin
  }.

Definition papp_op (A:ob) : perm -> A -> A :=
  papp (carrier A) (eq_mixin A) (nominal_mixin A).

Definition support_op (A:ob) : A -> finset atom :=
  support (carrier A) (eq_mixin A) (nominal_mixin A).

Canonical Structure nom_support (A:ob) : supported :=
  Supported A (support_op A).

Canonical Structure ob_eq (A:ob) : Eq.type :=
  Eq.Pack (carrier A) (eq_mixin A).

Record hom (A B:ob) :=
  Hom
  { map :> carrier A -> carrier B
  ; eq_axiom : forall x y, x ≈ y -> map x ≈ map y
  ; equivariant : forall x (p:perm),
       map (papp_op A p x) ≈ papp_op B p (map x)
  }.

Program Definition ident (A:ob) :=
  Hom A A (fun x => x) _ _.

Program Definition compose (A B C:ob) (f:hom B C) (g:hom A B) :=
  Hom A C (fun x => f (g x)) _ _.
Next Obligation.
  apply eq_axiom.
  apply eq_axiom.
  auto.
Qed.
Next Obligation.
  transitivity (f (papp_op B p (g x))).
  apply eq_axiom.
  apply equivariant.
  apply equivariant.
Qed.

Definition comp_mixin : Comp.mixin_of ob hom :=
  Comp.Mixin ob hom ident compose.

Canonical Structure comp := Comp.Pack ob hom comp_mixin.

Program Definition hom_eq_mixin (A B:ob) : Eq.mixin_of (hom A B) :=
  Eq.Mixin (hom A B) (fun f g => forall x, f x ≈ g x) _ _ _.
Next Obligation.
  rewrite H; auto.
Qed.

Lemma category_axioms : Category.axioms ob hom hom_eq_mixin comp_mixin.
Proof.
  constructor.
  repeat intro. simpl; auto.
  repeat intro. simpl; auto.
  repeat intro. simpl; auto.
  repeat intro. simpl; auto.
  transitivity (f (g' x)).
  apply eq_axiom. apply H0.
  apply H.
Qed.

Canonical Structure NOMINAL : category :=
  Category ob hom hom_eq_mixin comp_mixin category_axioms.

Canonical Structure eq (A:ob) : Eq.type := Eq.Pack (carrier A) (eq_mixin A).
Canonical Structure hom_eq (A B:ob) : Eq.type := Eq.Pack (hom A B) (hom_eq_mixin A B).

End Nominal.

Notation NOMINAL := Nominal.NOMINAL.
Notation nominal := Nominal.ob.
Canonical Structure NOMINAL.
Canonical Structure Nominal.nom_support.
Canonical Structure Nominal.eq.
Canonical Structure Nominal.hom_eq.
Canonical Structure Nominal.comp.
Coercion Nominal.carrier : Nominal.ob >-> Sortclass.
Coercion Nominal.map : Nominal.hom >-> Funclass.

Notation "p · x" := (Nominal.papp_op _ p x) (at level 35, right associativity).

Add Parametric Morphism (A B:nominal) :
  (Nominal.map A B)
    with signature (eq_op (Nominal.hom_eq A B)) ==>
                   (eq_op (Nominal.eq A)) ==>
                   (eq_op (Nominal.eq B))
   as nom_map_morphism.
Proof.
  intros.
  transitivity (x y0).
  apply Nominal.eq_axiom. auto.
  apply H.
Qed.

Add Parametric Morphism (A:nominal) : 
  (Nominal.papp_op A)
  with signature (@eq_op (Perm.eq tt tt)) ==>
                 (@eq_op (Nominal.eq A)) ==>
                 (@eq_op (Nominal.eq A))
    as papp_morphism.
Proof.           
  intros. apply Nominal.papp_respects; auto.
Qed.

Lemma nom_compose (A:nominal) (p1 p2:perm) (x:A) :
  p1 · p2 · x ≈ (p1 ∘ p2) · x.
Proof.
  apply Nominal.nom_comp.
Qed.

Lemma nom_compose' (A:nominal) (p p1 p2:perm) (x:A) :
  p1 ∘ p2 ≈ p ->
  p1 · p2 · x ≈ p · x.
Proof.
  intros. rewrite nom_compose. rewrite H. auto.
Qed.

Lemma nom_ident (A:nominal) (x:A) :
  id·x ≈ x.
Proof.
  apply Nominal.nom_ident.
Qed.

Lemma nom_ident' (A:nominal) (p:perm) (x:A) :
  p ≈ id(tt) ->
  p·x ≈ x.
Proof.
  intros. rewrite H.
  apply Nominal.nom_ident.
Qed.

Lemma support_axiom (A:nominal) (p:perm) (x:A) :
  x♯p -> p·x ≈ x.
Proof.
  intros. apply Nominal.support_axiom. auto.
Qed.

Lemma support_axiom' (A:nominal) (p:perm) (x:A) :
  x♯p -> x ≈ p·x.
Proof.  
  intros. symmetry. apply support_axiom. auto.
Qed.

Lemma support_papp (A:nominal) (p:perm) (x:A) (v:atom) :
  v ∈ ‖x‖ <-> p v ∈ ‖p·x‖.
Proof.
  intros. apply Nominal.support_papp.
Qed.

Lemma papp_inj (A:nominal) (p:perm) (x y:A) :
  p·x ≈ p·y -> x ≈ y.
Proof.
  intros.
  cut ((p⁻¹ ∘ p) · x ≈ (p⁻¹ ∘ p) · y).
  intros.
  rewrite Perm.inv_id2 in H0.
  rewrite nom_ident in H0.
  rewrite nom_ident in H0.
  auto.
  rewrite <- nom_compose.
  rewrite <- nom_compose.
  rewrite H. auto.
Qed.

(** NOMINAL is an initialized category. *)

Program Definition initius_eq_mixin :=
  Eq.Mixin False (fun _ _ => False) _ _ _.

Program Definition initius_mixin :=
  Nominal.Mixin
      False initius_eq_mixin 
      (fun p x => False_rect _ x)
      (fun x => False_rect _ x)
      _ _ _ _ _.
Next Obligation.
  elim x. elim x.
Qed.

Canonical Structure initius :=
  Nominal.Ob False initius_eq_mixin initius_mixin.

Program Definition initiate (A:nominal) : initius → A :=
  Nominal.Hom initius A (fun x => False_rect _ x) _ _.
Next Obligation.
  elim x.
Qed.
Next Obligation.
  elim x.
Qed.

Program Definition initialized_mixin :=
  Initialized.Mixin
    Nominal.ob Nominal.hom
    Nominal.hom_eq_mixin
    initius initiate
    _.
Next Obligation.
  hnf. intro x. elim x.
Qed.

Canonical Structure initialized_nominal : initialized :=
  Initialized
    Nominal.ob Nominal.hom
    Nominal.hom_eq_mixin
    Nominal.comp_mixin
    Nominal.category_axioms
    initialized_mixin.


(** NOMINAL has binary coproducts. *)

Section nom_sum.
  Variables A B:nominal.

  Definition nom_sum_equiv (x y:A+B) :=
    match x, y with
    | inl a, inl a' => a ≈ a'
    | inr b, inr b' => b ≈ b'
    | _, _ => False
    end.

  Definition nom_sum_papp (p:perm) (x:A+B) :=
    match x with
    | inl a => inl (p · a)
    | inr b => inr (p · b)
    end.

  Definition nom_sum_support (x:A+B) : finset atom :=
    match x with
    | inl a => ‖a‖
    | inr b => ‖b‖
    end.

  Program Definition nom_sum_eq_mixin :=
    Eq.Mixin (A+B) nom_sum_equiv _ _ _.
  Next Obligation.
    simpl. auto.
    simpl. auto.
  Qed.
  Next Obligation.
    simpl in *. destruct y; simpl in *; auto.
    destruct y; simpl in *; auto.
  Qed.
  Next Obligation.
    destruct z; simpl in *; eauto.
    destruct z; simpl in *; eauto.
    elim H.
    destruct z; simpl in *; eauto.
    elim H.
    destruct z; simpl in *; eauto.
  Qed.


  Program Definition nom_sum_mixin :=
    Nominal.Mixin (A+B) nom_sum_eq_mixin nom_sum_papp nom_sum_support
       _ _ _ _ _.
  Next Obligation.
    destruct a; red; simpl; auto.
    apply nom_ident.
    apply nom_ident.
  Qed.
  Next Obligation.
    destruct a; red; simpl; auto.
    apply nom_compose.
    apply nom_compose.
  Qed.
  Next Obligation.
    destruct a; destruct a'; simpl in *.
    red in H0; simpl in H0.
    red; simpl. apply papp_morphism; auto.
    red in H0; simpl in H0. elim H0.
    red in H0; simpl in H0. elim H0.
    red in H0; simpl in H0.
    red; simpl. apply papp_morphism; auto.
  Qed.
  Next Obligation.
    destruct a; red; simpl.
    apply support_axiom.
    red; simpl; intros. apply (H v); auto.
    apply support_axiom.
    red; simpl; intros. apply (H v); auto.
  Qed.
  Next Obligation.
    destruct x; apply support_papp; auto.    
    destruct x; simpl in H;
      apply support_papp in H; auto.    
  Qed.

  Canonical Structure nom_sum : nominal :=
    Nominal.Ob (A+B) nom_sum_eq_mixin nom_sum_mixin.
End nom_sum.


(** NOMINAL has colimits for directed systems. *)
Require Import directed.
Require Import cont_functors.

Section nominal_directed_colimits.
  Variable I:directed_preord.
  Variable DS:directed_system I NOMINAL.

  Record nom_colimit_type :=
    NomColim
    { nom_colim_idx : I
    ; nom_colim_elem : ds_F DS nom_colim_idx
    }.

  Definition nom_colimit_equiv (x y:nom_colimit_type) :=
    exists k
      (Hxk:nom_colim_idx x ≤ k)
      (Hyk:nom_colim_idx y ≤ k),
      ds_hom DS _ _ Hxk (nom_colim_elem x) ≈ 
      ds_hom DS _ _ Hyk (nom_colim_elem y).

  Program Definition nom_colimit_eq_mixin :=
    Eq.Mixin nom_colimit_type nom_colimit_equiv _ _ _ .
  Next Obligation.
    exists (nom_colim_idx x).
    exists (ord_refl I (nom_colim_idx x)).
    exists (ord_refl I (nom_colim_idx x)).
    auto.
  Qed.
  Next Obligation.
    destruct H as [k [Hxk [Hyk ?]]].
    exists k. exists Hyk. exists Hxk. symmetry.
    auto.
  Qed.
  Next Obligation.
    destruct H as [i [Hxi [Hyi ?]]].
    destruct H0 as [j [Hyj [Hzj ?]]].
    destruct (choose_ub I i j) as [k [Hik Hjk]].
    assert (Hxk : nom_colim_idx x ≤ k). etransitivity; eauto.
    assert (Hyk : nom_colim_idx y ≤ k). etransitivity; eauto.
    assert (Hzk : nom_colim_idx z ≤ k). etransitivity; eauto.
    exists k. exists Hxk. exists Hzk.
    rewrite <- (ds_compose DS (nom_colim_idx x) i k Hxi Hik Hxk).
    rewrite <- (ds_compose DS (nom_colim_idx z) j k Hzj Hjk Hzk).
    simpl.
    rewrite H. rewrite <- H0.
    change ((ds_hom DS i k Hik ∘ ds_hom DS (nom_colim_idx y) i Hyi) (nom_colim_elem y)
      ≈ ((ds_hom DS j k Hjk ∘ ds_hom DS (nom_colim_idx y) j Hyj) (nom_colim_elem y))).
    rewrite (ds_compose DS (nom_colim_idx y) i k Hyi Hik Hyk).
    rewrite (ds_compose DS (nom_colim_idx y) j k Hyj Hjk Hyk).
    auto.
  Qed.

  Definition nom_colimit_papp (p:perm) (x:nom_colimit_type) :=
    match x with
    | NomColim i x' => NomColim i (p · x')
    end.

  Program Definition nom_colimit_mixin :=
    Nominal.Mixin 
      nom_colimit_type 
      nom_colimit_eq_mixin
      nom_colimit_papp
      (fun x => ‖ nom_colim_elem x ‖)
      _ _ _ _ _.
  Next Obligation.
    destruct a as [i a]. exists i. simpl.
    exists (ord_refl _ _).
    exists (ord_refl _ _).
    apply Nominal.eq_axiom.
    apply nom_ident.
  Qed.
  Next Obligation.
    destruct a as [i a]. exists i. simpl.
    exists (ord_refl _ _).
    exists (ord_refl _ _).
    apply Nominal.eq_axiom.
    apply nom_compose.
  Qed.
  Next Obligation.
    destruct H0 as [k [Hk1 [Hk2 ?]]].
    destruct a as [i a].
    destruct a' as [j b].
    simpl in *.
    exists k. simpl. exists Hk1. exists Hk2.
    rewrite Nominal.equivariant.
    rewrite Nominal.equivariant.
    apply papp_morphism; auto.
  Qed.
  Next Obligation.
    destruct a as [i a]. simpl.
    exists i.
    exists (ord_refl _ _).
    exists (ord_refl _ _).
    simpl.
    apply Nominal.eq_axiom.
    apply support_axiom; auto.
  Qed.
  Next Obligation.
    destruct x as [i x]; simpl in *.
    apply support_papp. auto.
    destruct x as [i x]; simpl in *.
    apply support_papp in H. auto.
  Qed.

  Canonical Structure nom_colimit : nominal :=
    Nominal.Ob nom_colimit_type nom_colimit_eq_mixin nom_colimit_mixin.

  Program Definition nom_colimit_spoke (i:I) : ds_F DS i → nom_colimit :=
    Nominal.Hom (ds_F DS i) nom_colimit (NomColim i) _ _.
  Next Obligation.
    exists i. simpl. exists (ord_refl _ _). exists (ord_refl _ _).
    apply Nominal.eq_axiom. auto.
  Qed.

  Program Definition nom_colimit_cocone : cocone DS :=
    Cocone DS nom_colimit nom_colimit_spoke _.
  Next Obligation.
    red; simpl. intro x.
    destruct (choose_ub I i j) as [k [??]].
    exists k. simpl. exists H. exists H0.
    symmetry.
    apply (ds_compose DS i j k Hij H0 H x).
  Qed.
  
  Section nom_colimit_univ.
    Variable YC:cocone DS.

    Definition nom_colimit_univ_defn (x:nom_colimit) : cocone_point YC :=
      match x with
      | NomColim i x' => cocone_spoke YC i x'
      end.

    Program Definition nom_colimit_univ : nom_colimit → cocone_point YC :=
      Nominal.Hom nom_colimit (cocone_point YC) nom_colimit_univ_defn _ _.
    Next Obligation.
      destruct x as [i x].
      destruct y as [j y].
      destruct H as [k [Hk1 [Hk2 ?]]]. simpl in *.
      rewrite (cocone_commute YC i k Hk1).
      rewrite (cocone_commute YC j k Hk2).
      simpl. apply Nominal.eq_axiom. auto.
    Qed.
    Next Obligation.
      destruct x as [i x]. simpl.
      apply Nominal.equivariant.
    Qed.

    Lemma nom_colimit_commute : forall i,
      cocone_spoke YC i ≈ nom_colimit_univ ∘ nom_colimit_spoke i.
    Proof.
      intro. intro. simpl. auto.
    Qed.

    Lemma nom_colimit_uniq : forall (f:nom_colimit → YC),
      (forall i, cocone_spoke YC i ≈ f ∘ nom_colimit_spoke i) ->
      f ≈ nom_colimit_univ.
    Proof.
      simpl; intros. intro x.
      destruct x as [i x]. simpl.
      symmetry. apply H.
    Qed.
  End nom_colimit_univ.
    
  Definition nom_has_colimits : directed_colimit DS nom_colimit_cocone
    := DirectedColimit DS nom_colimit_cocone
         nom_colimit_univ nom_colimit_commute nom_colimit_uniq.
End nominal_directed_colimits.


(** NOMINAL has least fixpoints of continuous functors. *)
Section nominal_fixpoint.
  Variable F : functor NOMINAL NOMINAL.
  Variable HF : continuous_functor F.

  Definition fixpoint : ob NOMINAL :=
    (cont_functors.fixpoint initialized_nominal F nom_colimit_cocone).

  Definition fixpoint_initial : Alg.initial_alg NOMINAL F :=
    (cont_functors.fixpoint_initial 
      initialized_nominal F nom_colimit_cocone nom_has_colimits HF).
    
  Definition fixpoint_iso : F fixpoint ↔ fixpoint :=
    (cont_functors.fixpoint_iso
      initialized_nominal F nom_colimit_cocone nom_has_colimits HF).

End nominal_fixpoint.



(** NOMINAL is a terminated category. *)

Program Definition nom_terminus_eq_mixin :=
  Eq.Mixin unit (fun _ _ => True) _ _ _.

Program Definition nom_terminus_mixin :=
  Nominal.Mixin unit nom_terminus_eq_mixin (fun p u => u) (fun _ => nil) _ _ _ _ _.
Next Obligation.
  apply nil_elem in H. elim H.
  apply nil_elem in H. elim H.
Qed.

Canonical Structure nom_terminus : nominal :=
  Nominal.Ob unit nom_terminus_eq_mixin nom_terminus_mixin.

Program Definition nom_terminate (A:nominal) : A → nom_terminus :=
  Nominal.Hom A nom_terminus (fun _ => tt) _ _.

Program Definition nom_terminated_mixin :=
  Terminated.Mixin
    Nominal.ob Nominal.hom
    Nominal.hom_eq_mixin
    nom_terminus nom_terminate _.
Next Obligation.
  red. simpl. intros. destruct (f x). auto.
Qed.

Canonical Structure nom_terminated :=
  Terminated
    Nominal.ob Nominal.hom
    Nominal.hom_eq_mixin
    Nominal.comp_mixin
    Nominal.category_axioms
    nom_terminated_mixin.

(**  NOMINAL is a cartesian category. *)
Program Definition nom_prod_eq_mixin (A B :nominal) :=
   Eq.Mixin (A*B) (fun x y => fst x ≈ fst y /\ snd x ≈ snd y) _ _ _.
Solve Obligations using intuition eauto.

Program Definition nom_prod_mixin (A B:nominal) :=
  Nominal.Mixin (A*B) (nom_prod_eq_mixin A B)
     (fun p xy => (p · fst xy, p · snd xy))
     (fun xy => ‖fst xy‖ ++ ‖snd xy‖)
     _ _ _ _ _.
Next Obligation.
  destruct a; split; simpl; apply nom_ident.
Qed.
Next Obligation.
  destruct a; split; simpl; apply nom_compose.
Qed.
Next Obligation.
  destruct a; destruct a'; destruct H0; split; simpl in *.
  rewrite H. rewrite H0. auto.
  rewrite H. rewrite H1. auto.
Qed.  
Next Obligation.
  destruct a; split; simpl.
  apply support_axiom.
  red; simpl; intros.
  apply (H v); simpl; auto.
  apply app_elem; auto.
  apply support_axiom.
  red; simpl; intros.
  apply (H v); simpl; auto.
  apply app_elem; auto.
Qed.
Next Obligation.
  simpl.
  apply app_elem in H. apply app_elem.
  destruct H; [ left | right ].
  apply support_papp; auto.
  apply support_papp; auto.
  simpl in H.
  apply app_elem in H. apply app_elem.
  destruct H; [ left | right ].
  apply support_papp in H; auto.
  apply support_papp in H; auto.
Qed.

Canonical Structure nom_prod (A B:nominal) : nominal :=
  Nominal.Ob (A*B) (nom_prod_eq_mixin A B) (nom_prod_mixin A B).

Program Definition nom_pi1 (A B:nominal) : nom_prod A B → A :=
  Nominal.Hom (nom_prod A B) A (fun x => fst x) _ _.
Next Obligation.
  destruct H; auto.
Qed.

Program Definition nom_pi2 (A B:nominal) : nom_prod A B → B :=
  Nominal.Hom (nom_prod A B) B (fun x => snd x) _ _.
Next Obligation.
  destruct H; auto.
Qed.

Program Definition nom_pairing (C A B:nominal) (f:C → A) (g:C → B) : C → nom_prod A B
  := Nominal.Hom C (nom_prod A B) (fun c => (f c, g c)) _ _.
Next Obligation.
  split; simpl; apply Nominal.eq_axiom; auto.
Qed.
Next Obligation.
  split; simpl; apply Nominal.equivariant.
Qed.

Program Definition nom_cartesian_mixin :=
  Cartesian.Mixin 
    Nominal.ob Nominal.hom
    Nominal.hom_eq_mixin
    Nominal.comp_mixin
    nom_prod nom_pi1 nom_pi2 nom_pairing
    _.
Next Obligation.
  constructor; simpl; intros.

  red; simpl; auto.
  red; simpl; auto.
  red; simpl; intro.
  split; simpl.
  rewrite <- (H x); auto.
  rewrite <- (H0 x); auto.
Qed.

Canonical Structure nom_cartesian : cartesian :=
  Cartesian 
     Nominal.ob Nominal.hom
     Nominal.hom_eq_mixin
     Nominal.comp_mixin
     Nominal.category_axioms
     nom_terminated_mixin
     nom_cartesian_mixin.

(** NOMINAL is a cartesian closed category. *)

Record nom_exp_type (A B:nominal) :=
  NomExp
  { exp_map :> A -> B
  ; exp_support : finset atom
  ; exp_eq_axiom : forall x y, x ≈ y -> exp_map x ≈ exp_map y
  ; exp_support_axiom : forall (p:perm),
       (forall v, v ∈ exp_support -> v ∈ ‖p‖ -> False) ->
       (forall x, p · exp_map (p⁻¹ · x) ≈ exp_map x)
  }.

Program Definition exp_papp (A B:nominal) (p:perm) (f:nom_exp_type A B) : 
  nom_exp_type A B := 
  NomExp A B
    (fun x => p · f (p⁻¹ · x)) 
    (List.map p (exp_support A B f))
    _ _.
Next Obligation.
  apply papp_morphism; auto.
  apply exp_eq_axiom.
  apply papp_morphism; auto.
Qed.  
Next Obligation.
  cut (forall v, v ∈ (List.map p (exp_support A B f) : finset atom) -> p0 v = v).
  clear H.
  induction p0 using swap_induction'; intros.

  etransitivity. etransitivity. 2: apply IHp0.
  apply papp_morphism; auto.
  apply papp_morphism; auto.
  apply exp_eq_axiom.
  apply papp_morphism; auto.
  apply papp_morphism; auto.
  apply inv_eq; auto.
  intros. rewrite H.
  apply (H0 v); auto.
  apply papp_morphism; auto.
  rewrite nom_ident.
  apply papp_morphism; auto.
  apply exp_eq_axiom.
  rewrite nom_compose.
  apply papp_morphism; auto.
  hnf; simpl; auto.
  
  rewrite nom_compose.
  rewrite <- Perm.assoc.
  rewrite <- nom_compose.
  rewrite swap_commute'.
  rewrite <- nom_compose.
  set (p' := Perm.g p u ⇋ Perm.g p v).
  transitivity
    (p0 · p · p' · f (p'⁻¹ · p⁻¹ · p0⁻¹ · x)).
  apply papp_morphism. auto.
  apply papp_morphism. auto.
  apply papp_morphism. auto.
  apply exp_eq_axiom.
  rewrite inv_compose.
  rewrite <- nom_compose.
  rewrite nom_compose.
  symmetry.
  rewrite nom_compose .
  apply papp_morphism; auto.
  hnf; simpl; intros.
  destruct (string_dec u x0).
  subst x0.
  destruct (string_dec (Perm.g p u) (Perm.g p u)); auto.
  elim n; auto.
  destruct (string_dec (Perm.g p u) (Perm.g p x0)); auto.
  apply Perm.g_inj in e. contradiction.
  destruct (string_dec v x0).
  destruct (string_dec (Perm.g p v) (Perm.g p x0)); auto.
  elim n1. rewrite e; auto.
  destruct (string_dec (Perm.g p v) (Perm.g p x0)); auto.
  apply Perm.g_inj in e. contradiction.
  
  rewrite exp_support_axiom.
  apply IHp0.
  intros.
  apply H1 in H2.
  simpl in H2.
  destruct (string_dec u v0). subst v0. auto.
  destruct (string_dec v v0). subst v0.
  rewrite H in H2. contradiction.
  auto.

  simpl; intros.
  unfold Support.support in H3. simpl in H3.
  apply cons_elem in H3.
  destruct H3.
  apply atom_strong_eq in H3.
  subst v0.
  assert (u ∈ (List.map p (exp_support A B f) : finset atom)).
    revert H2. generalize (exp_support A B f). induction c.
    intros. apply nil_elem in H2. elim H2.
    intros. apply cons_elem in H2. destruct H2.
    apply atom_strong_eq in H2. subst a.
    simpl. apply cons_elem. left.
    rewrite Perm.fg. auto.
    simpl. apply cons_elem. right.
    apply IHc; auto.

  apply H1 in H3.
  simpl in H3.
  destruct (string_dec u u).
  rewrite <- H in H3.
  apply Perm.f_inj in H3. elim H0; auto.
  elim n; auto.
  apply cons_elem in H3.
  destruct H3.
  apply atom_strong_eq in H3. subst v0.
  assert (v ∈ (List.map p (exp_support A B f) : finset atom)).
    revert H2. generalize (exp_support A B f). induction c.
    intros. apply nil_elem in H2. elim H2.
    intros. apply cons_elem in H2. destruct H2.
    apply atom_strong_eq in H2. subst a.
    simpl. apply cons_elem. left.
    rewrite Perm.fg. auto.
    simpl. apply cons_elem. right.
    apply IHc; auto.

  apply H1 in H3.
  simpl in H3.  
  destruct (string_dec u v); auto.
  destruct (string_dec v v); auto.
  rewrite H in H3.
  elim n; auto.
  apply nil_elem in H3. auto.

  intros.
  destruct (Perm.support_axiom p0 v); auto.
  elim (H v); auto.
Qed.

Program Definition nom_exp_eq_mixin (A B:nominal) :=
  Eq.Mixin (nom_exp_type A B) (fun f g => forall x, f x ≈ g x) _ _ _.
Next Obligation.
  rewrite H; auto.
Qed.

Canonical Structure nom_exp_eq (A B:nominal) :=
  Eq.Pack (nom_exp_type A B) (nom_exp_eq_mixin A B).

Add Parametric Morphism (A B:nominal) :
  (exp_map A B)
  with signature (eq_op (nom_exp_eq A B)) ==>
                 (eq_op (Nominal.ob_eq A)) ==>
                 (eq_op (Nominal.ob_eq B))
   as exp_map_morphism.
Proof.
  intros. 
  transitivity (x y0).
  apply exp_eq_axiom. auto.
  apply H.
Qed.

Program Definition nom_exp_mixin (A B:nominal) :=
  Nominal.Mixin 
  (nom_exp_type A B)
  (nom_exp_eq_mixin A B)
  (exp_papp A B)
  (exp_support A B)
  _ _ _ _ _.
Next Obligation.
  hnf. simpl; intros.
  rewrite nom_ident.
  apply exp_eq_axiom.
  transitivity (id · x).
  apply papp_morphism.
  hnf; simpl; auto. auto.
  rewrite nom_ident. auto.
Qed.    
Next Obligation.
  hnf; simpl; intro; auto.
  rewrite nom_compose.
  apply papp_morphism; auto.
  apply exp_eq_axiom.
  rewrite nom_compose.
  apply papp_morphism; auto.
  symmetry. apply inv_compose.
Qed.
Next Obligation.
  hnf; simpl. intros.
  apply papp_morphism; auto.
  etransitivity.
  apply H0.
  apply exp_eq_axiom.
  apply papp_morphism; auto.
  apply inv_eq. auto.
Qed.
Next Obligation.
  hnf. simpl; intros.
  apply exp_support_axiom. auto.
Qed.
Next Obligation.
  simpl in *.
  revert H. generalize (exp_support A B x). induction c.
    intros. apply nil_elem in H. elim H.
    intros. apply cons_elem in H. destruct H.
    apply atom_strong_eq in H. subst a.
    simpl. apply cons_elem. left. auto.
    simpl. apply cons_elem. right.
    apply IHc; auto.

  simpl in *.
  revert H. generalize (exp_support A B x). induction c.
    intros. apply nil_elem in H. elim H.
    intros. apply cons_elem in H. destruct H.
    apply atom_strong_eq in H.
    apply Perm.f_inj in H. subst v.
    simpl. apply cons_elem. left. auto.
    simpl. apply cons_elem. right.
    apply IHc; auto.
Qed.

Canonical Structure nom_exp (A B:nominal) : nominal :=
  Nominal.Ob 
    (nom_exp_type A B) 
    (nom_exp_eq_mixin A B)
    (nom_exp_mixin A B).

Program Definition nom_curry (C A B:nominal) (f:C×A → B) : C → nom_exp A B :=
  Nominal.Hom C (nom_exp A B)
     (fun c => NomExp A B (fun a => f (c,a)) (‖c‖) _ _) _ _.
Next Obligation.
  apply Nominal.eq_axiom. split; auto.
Qed.
Next Obligation.
  rewrite <- Nominal.equivariant.
  apply Nominal.eq_axiom.
  split. simpl.
  apply support_axiom. auto.
  simpl.
  rewrite nom_compose.
  rewrite Perm.inv_id1.
  apply nom_ident.
Qed.
Next Obligation.
  hnf; simpl. intro.
  apply Nominal.eq_axiom.
  split; auto.
Qed.
Next Obligation.
  hnf; simpl. intro.
  rewrite <- Nominal.equivariant.
  apply Nominal.eq_axiom.
  split; simpl; auto.
  rewrite nom_compose.
  rewrite Perm.inv_id1.
  symmetry. apply nom_ident.
Qed.

Program Definition nom_apply (A B:nominal) : nom_exp A B × A → B :=
  Nominal.Hom (nom_exp A B × A) B (fun fx => fst fx (snd fx)) _ _.
Next Obligation.
  destruct x; destruct y; destruct H; simpl in *.
  etransitivity.
  apply H.
  apply exp_eq_axiom. auto.
Qed.
Next Obligation.
  simpl.
  apply papp_morphism. auto.
  apply exp_eq_axiom.
  rewrite nom_compose.
  rewrite Perm.inv_id2.
  apply nom_ident.
Qed.

Program Definition nom_ccc_mixin :=
  CartesianClosed.Mixin
    Nominal.ob Nominal.hom
    Nominal.hom_eq_mixin
    Nominal.comp_mixin
    Nominal.category_axioms
    nom_terminated_mixin
    nom_cartesian_mixin
    nom_exp nom_curry nom_apply
    _.
Next Obligation.
  constructor; simpl; intros.
  red; simpl; intros.
  destruct x; simpl. auto.
  red; simpl; intros.
  red. simpl. intros.
  etransitivity. 2: apply H.
  simpl. auto.
Qed.

Canonical Structure nom_ccc : cartesian_closed :=
  CartesianClosed 
     Nominal.ob Nominal.hom
     Nominal.hom_eq_mixin
     Nominal.comp_mixin
     Nominal.category_axioms
     nom_cartesian_mixin
     nom_terminated_mixin
     nom_ccc_mixin.

(** Atom binding construct. *)

Inductive binding_ty (A:nominal) :=
  | bind : atom -> A -> binding_ty A.

Notation "'ν' x , t" := (bind _ x t) (at level 50, format "'ν'  x ,  t").

Definition binding_equiv (A:nominal) (x y:binding_ty A) :=
  let (v, x') := x in
  let (w, y') := y in
    exists u:atom, u ∉ (v :: w :: ‖x'‖ ++ ‖y'‖ : finset atom) /\
      u ⇋ v · x' ≈ u ⇋ w · y'.

Lemma binding_equiv_forall (A:nominal) (x y:binding_ty A) (avoid : finset atom):
  binding_equiv A x y <->
  let (v,x') := x in
  let (w,y') := y in
  forall u,
      u ∉ (v :: w :: ‖x'‖ ++ ‖y'‖ : finset atom) ->
      u ∉ avoid ->
      u ⇋ v · x' ≈ u ⇋ w · y'.
Proof.
  split; intros.
  destruct x as [v x].
  destruct y as [w y].
  intros.
  destruct H as [q [??]].
  destruct (string_dec q u). subst q.
  auto.

  rewrite <- (support_axiom A (u ⇋ q) x).
  rewrite <- (support_axiom A (u ⇋ q) y).
  rewrite (Perm.swap_swap u v).
  rewrite (Perm.swap_swap u w).
  repeat rewrite nom_compose.
  rewrite Perm.swap_swizzle; auto.
  rewrite <- nom_compose.
  rewrite Perm.swap_swizzle; auto.
  rewrite <- nom_compose.
  rewrite (Perm.swap_swap v q).
  apply papp_morphism; auto.
  rewrite (Perm.swap_swap w q).
  auto.
  intro. subst w.
  apply H0.
  apply cons_elem. right.
  apply cons_elem. auto.
  intro. subst w.
  apply H.
  apply cons_elem. right.
  apply cons_elem. auto.
  intro. subst v.
  apply H0.
  apply cons_elem. auto.
  intro. subst v.
  apply H.
  apply cons_elem. auto.
  rename H1 into Havoid.
  red. simpl; intros.
  unfold Support.support in H3. simpl in H3.
  apply cons_elem in H3. destruct H3.
  apply atom_strong_eq in H3. subst v0.
  apply H0.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; auto.
  apply cons_elem in H3. destruct H3.
  apply atom_strong_eq in H3. subst v0.
  apply H.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; auto.
  apply nil_elem in H3; auto.

  rename H1 into Havoid.
  red; simpl; intros.
  unfold Support.support in H3. simpl in H3.
  apply cons_elem in H3. destruct H3.
  apply atom_strong_eq in H3. subst v0.
  apply H0.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; auto.
  apply cons_elem in H3. destruct H3.
  apply atom_strong_eq in H3. subst v0.
  apply H.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; auto.
  apply nil_elem in H3; auto.

  red.
  destruct x as [u x].
  destruct y as [w y].
  exists (fresh_atom (u::w::‖x‖++‖y‖++ avoid)).
  split.
  apply fresh_atom_is_fresh'.
  hnf; simpl; intros.
    apply cons_elem in H0. destruct H0. apply atom_strong_eq in H0.
    subst u. apply cons_elem; auto.
    apply cons_elem; right.
    apply cons_elem in H0. destruct H0. apply atom_strong_eq in H0.
    subst w. 
    apply cons_elem. auto.
    apply cons_elem; right.
    apply app_elem in H0.
    destruct H0.
    apply app_elem; auto.
    apply app_elem; right.
    apply app_elem; auto.
    
  apply H; apply fresh_atom_is_fresh'.
  hnf; simpl; intros.
    apply cons_elem in H0. destruct H0. apply atom_strong_eq in H0.
    subst u. apply cons_elem; auto.
    apply cons_elem; right.
    apply cons_elem in H0. destruct H0. apply atom_strong_eq in H0.
    subst w. 
    apply cons_elem. auto.
    apply cons_elem; right.
    apply app_elem in H0.
    destruct H0.
    apply app_elem; auto.
    apply app_elem; right.
    apply app_elem; auto.
  hnf; simpl; intros.
    apply cons_elem; right.
    apply cons_elem; right.
    apply app_elem; right.
    apply app_elem; right.
    auto.
Qed.  

Program Definition binding_eq_mixin (A:nominal) : Eq.mixin_of (binding_ty A) :=
  Eq.Mixin (binding_ty A) (binding_equiv A) _ _ _.
Next Obligation.
  apply binding_equiv_forall with nil.
  destruct x as [v x']. intros. auto.
Qed.
Next Obligation.
  apply binding_equiv_forall with nil.
  destruct x as [v x'].
  destruct y as [w y'].
  intros. clear H1.
  apply binding_equiv_forall with (avoid:=nil) in H.
  symmetry. apply H.
  intro. apply H0.
  apply cons_elem in H1. destruct H1.
  apply cons_elem. right.
  apply cons_elem. auto.
  apply cons_elem in H1. destruct H1.
  apply cons_elem. auto.
  apply app_elem in H1.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; intuition.
  intro. apply nil_elem in H1; auto.
Qed.
Next Obligation.
  unfold binding_equiv in *.
  destruct x as [v x'].
  destruct y as [w y'].
  destruct z as [u z'].
  destruct H as [q1 [??]].
  destruct H0 as [q2 [??]].
  destruct (string_dec q1 q2).
  subst q2.
  exists q1. intuition.
  apply cons_elem in H3; destruct H3.
  apply H. apply cons_elem; auto.
  apply cons_elem in H3; destruct H3.
  apply H0.
  apply cons_elem. right. apply cons_elem. left. auto.
  apply app_elem in H3. destruct H3.
  apply H.
  apply cons_elem. right. apply cons_elem. right.
  apply app_elem; auto.
  apply H0.
  apply cons_elem. right. apply cons_elem. right.
  apply app_elem; auto.
  rewrite H1. auto.

  set (atoms := (q1 :: q2 :: u :: v :: w ::‖x'‖++‖y'‖++‖z'‖)).
  set (q := fresh_atom atoms).
  exists q.
  split.
  intro.
  intros.
  eapply fresh_atom_is_fresh'.
  2: unfold q in H3; apply H3.
  unfold atoms.
    hnf; simpl; intros.
    apply cons_elem in H4. destruct H4.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. auto.
    apply cons_elem in H4. destruct H4.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. auto.
    apply app_elem in H4. destruct H4.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem; auto.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. auto.

  assert (Hqu: q <> u).
    intro.
    apply (fresh_atom_is_fresh atoms).
    fold q. rewrite H3.
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. auto.
  assert (Hqq2: q <> q2).
    intro.
    apply (fresh_atom_is_fresh atoms).
    fold q. rewrite H3.
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. auto.
  assert (Huq2 : u <> q2).
    intro.
    apply H0. rewrite H3.
    apply cons_elem. right.
    apply cons_elem. auto.
  assert (Hqw: q <> w).
    intro.
    apply (fresh_atom_is_fresh atoms).
    fold q. rewrite H3.
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. auto.
  assert (Hwq2: w <> q2).
    intro. apply H0. rewrite H3.
    apply cons_elem. auto.
  assert (Hqv : q <> v).
    intro.
    apply (fresh_atom_is_fresh atoms).
    fold q. rewrite H3.
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. auto.
  assert (Hqq1 : q <> q1).
    intro.
    apply (fresh_atom_is_fresh atoms).
    fold q. rewrite H3.
    unfold atoms.
    apply cons_elem. auto.
  assert (Hvq1 : v <> q1).
    intro.
    apply H. rewrite H3.
    apply cons_elem. auto.
  assert (Hwq1 : w <> q1).
    intro. apply H. rewrite H3.
    apply cons_elem. right.
    apply cons_elem. auto.

  rewrite <- (support_axiom A (q ⇋ q1) x').
  rewrite (Perm.swap_swap q v).
  rewrite nom_compose.
  rewrite Perm.swap_swizzle; auto.
  rewrite <- nom_compose.
  rewrite (Perm.swap_swap v q1).
  rewrite H1.
  rewrite (Perm.swap_swap q1 w).
  rewrite nom_compose.
  rewrite <- Perm.swap_swizzle; auto.
  rewrite <- nom_compose.
  rewrite (support_axiom A (q ⇋ q1) y').
  rewrite <- (support_axiom A (q ⇋ q2) y').
  rewrite nom_compose.
  rewrite Perm.swap_swizzle; auto.
  rewrite <- nom_compose.
  rewrite (Perm.swap_swap w q2).
  rewrite H2.
  rewrite (Perm.swap_swap q2 u).
  rewrite nom_compose.
  rewrite <- Perm.swap_swizzle; auto.
  rewrite <- nom_compose.
  rewrite (support_axiom A (q ⇋ q2) z').
  rewrite (Perm.swap_swap u q). auto.
  
  red; simpl; intros.
    unfold Support.support in H4. simpl in H4.
    apply cons_elem in H4. destruct H4.
    apply atom_strong_eq in H4. subst v0.
    apply (fresh_atom_is_fresh atoms).
    fold q. 
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. right.
    auto.
    apply cons_elem in H4. destruct H4.
    apply atom_strong_eq in H4. subst v0.
    apply H0.
    apply cons_elem. right.     
    apply cons_elem. right.
    apply app_elem. right.
    auto.
    apply nil_elem in H4. auto.

  red; simpl; intros.
    unfold Support.support in H4. simpl in H4.
    apply cons_elem in H4. destruct H4.
    apply atom_strong_eq in H4. subst v0.
    apply (fresh_atom_is_fresh atoms).
    fold q. 
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. auto.
    apply cons_elem in H4. destruct H4.
    apply atom_strong_eq in H4. subst v0.
    apply H0.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. auto.
    apply nil_elem in H4. auto.

  red; simpl; intros.
    unfold Support.support in H4. simpl in H4.
    apply cons_elem in H4. destruct H4.
    apply atom_strong_eq in H4. subst v0.
    apply (fresh_atom_is_fresh atoms).
    fold q. 
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. auto.
    apply cons_elem in H4. destruct H4.
    apply atom_strong_eq in H4. subst v0.
    apply H.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. auto.
    apply nil_elem in H4. auto.

  red; simpl; intros.
    unfold Support.support in H4. simpl in H4.
    apply cons_elem in H4. destruct H4.
    apply atom_strong_eq in H4. subst v0.
    apply (fresh_atom_is_fresh atoms).
    fold q. 
    unfold atoms.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. auto.
    apply cons_elem in H4. destruct H4.
    apply atom_strong_eq in H4. subst v0.
    apply H.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. auto.
    apply nil_elem in H4. auto.
Qed.

Canonical Structure binding_eq (A:nominal) :=
  Eq.Pack (binding_ty A) (binding_eq_mixin A).

Definition binding_papp (A:nominal) (p:perm) (x:binding_ty A) :=
  match x with
  | ν a, x' => ν (p a), (p·x')
  end.

Definition binding_support (A:nominal) (x:binding_ty A) :=
  match x with
  | ν a, x' => finset_remove atom_dec (‖x'‖) a
  end.

Program Definition binding_nominal_mixin (A:nominal) :=
  Nominal.Mixin 
    (binding_ty A)
    (binding_eq_mixin A)
    (binding_papp A) 
    (binding_support A)
    _ _ _ _ _.
Next Obligation.
  red; simpl.
  destruct a as [v a]; simpl.
  set (u := fresh_atom (v::‖a‖)).
  exists u. split.
  apply (fresh_atom_is_fresh').
  hnf; simpl; intros.
  apply cons_elem.
  apply cons_elem in H. destruct H; auto.
  apply cons_elem in H. destruct H; auto.
  apply app_elem in H.
  destruct H; auto.
  right.
  apply (support_papp _ id). auto.
  rewrite nom_ident. auto.
Qed.
Next Obligation.
  unfold binding_papp. destruct a; simpl.
  red. simpl.
  set (u := fresh_atom ((p1 (p2 c)) :: p1 (p2 c) ::
               ‖p1 · p2 · c0‖ ++ ‖(p1 ∘ p2) · c0‖)).
  exists u. split.
  apply fresh_atom_is_fresh.  
  rewrite <- nom_compose. auto.
Qed.  
Next Obligation.
  apply binding_equiv_forall with (avoid := nil).
  hnf; simpl. destruct a as [u a]. destruct a' as [v b].  
  simpl.
  intros w ? _.
  rewrite <- H.
  rewrite <- H.

  destruct H0 as [q [??]].

  rewrite nom_compose.
  
  replace w with (p (p⁻¹ w)).
  rewrite swap_commute.
  rewrite <- nom_compose.
  symmetry.
  rewrite nom_compose.
  rewrite swap_commute.
  rewrite <- nom_compose.
  symmetry.
  destruct (string_dec (p⁻¹ w) q).
  rewrite e.
  rewrite H2; auto.

  rewrite (Perm.swap_swap (p⁻¹ w) u).
  rewrite <- (support_axiom A (p⁻¹ w ⇋ q) a).
  rewrite nom_compose.
  rewrite nom_compose.
  rewrite <- Perm.assoc.
  rewrite <- nom_compose.
  rewrite Perm.swap_swizzle; auto.
  
  symmetry.
  rewrite <- (support_axiom A (p⁻¹ w ⇋ q) b).
  rewrite (Perm.swap_swap (p⁻¹  w) v).
  rewrite nom_compose.
  rewrite nom_compose.
  rewrite <- Perm.assoc.
  rewrite <- nom_compose.
  rewrite Perm.swap_swizzle; auto.
  rewrite <- nom_compose.
  rewrite <- nom_compose.
  rewrite (Perm.swap_swap v q).
  rewrite (Perm.swap_swap u q).
  rewrite H2. auto.
  intro.
  apply H1.
  apply cons_elem. right.
  apply cons_elem. left.
  rewrite <- H.
  rewrite <- H3.
  simpl.
  rewrite Perm.fg. auto.
  intro. subst v.
  apply H0.
  apply cons_elem. right.
  apply cons_elem. left. auto.

  red; simpl; intros.
  unfold Support.support in H4. simpl in H4.
  apply cons_elem in H4. destruct H4.
  apply atom_strong_eq in H4. subst v0.
  apply H1.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem.
  right.
  rewrite <- (Perm.fg p w).
  rewrite H.
  apply support_papp.   auto.
  apply cons_elem in H4. destruct H4.
  apply atom_strong_eq in H4. subst v0.
  apply H0.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; auto.
  apply nil_elem in H4; auto.

  intro.
  apply H1.
  apply cons_elem. left.
  rewrite <- H3.
  simpl.
  rewrite Perm.fg. auto.
  intro. subst q.
  apply H0.
  apply cons_elem; auto.
  
  red; simpl. intros.
  unfold Support.support in H4. simpl in H4.
  apply cons_elem in H4.
  destruct H4.
  apply atom_strong_eq in H4. subst v0.
  apply H1.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; auto.
  left.
  rewrite <- (Perm.fg p w).
  apply support_papp. auto.
  apply cons_elem in H4.
  destruct H4.
  apply atom_strong_eq in H4. subst v0.
  apply H0.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; auto.
  apply nil_elem in H4. auto.
  simpl.
  apply Perm.fg.
Qed.
Next Obligation.
  destruct a as [u a]; simpl.
  hnf; simpl.
  set (atoms := p u :: u :: ‖p·a‖ ++ ‖a‖ ++ ‖p‖).
  set (w := fresh_atom atoms).
  exists w.
  split. apply fresh_atom_is_fresh'.
  unfold atoms.
    hnf; simpl; intros.
    apply cons_elem in H0; destruct H0.
    apply cons_elem. auto.
    apply cons_elem in H0; destruct H0.
    apply cons_elem. right.
    apply cons_elem. auto.
    apply app_elem in H0. destruct H0.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. auto.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. auto.

  rewrite nom_compose.
  assert (w = p (p⁻¹ w)).
  symmetry. apply Perm.fg.
  pattern w at 1. rewrite H0.
  rewrite swap_commute.
  simpl.
  simpl in H.
  rewrite <- nom_compose.
  destruct (Perm.support_axiom p w).
  elimtype False.
  eapply fresh_atom_is_fresh'.
  2: unfold w in H1; apply H1.
  unfold atoms.
    hnf; simpl; intros.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. auto.
    
  rewrite (support_axiom A p).
  rewrite <- H1 at 1.
  rewrite Perm.gf. auto.

  red; simpl; intros.
  rewrite <- H1 in H2.
  rewrite Perm.gf in H2.

  assert ((w ⇋ u) v ∈ ‖a‖).
  apply <- (support_papp A (w ⇋ u)).
  generalize (Perm.swap_self_inv w u v).
  simpl. intros. rewrite H4. auto.

  simpl in H4.
  destruct (string_dec w v).
  subst v.

  elimtype False.
  eapply fresh_atom_is_fresh'.
  2: unfold w in H3; apply H3.
  unfold atoms.
    hnf; simpl; intros.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. auto.

  destruct (string_dec u v).
  eapply fresh_atom_is_fresh'.
  2: unfold w in H4; apply H4.
  unfold atoms.
    hnf; simpl; intros.
    apply cons_elem. right.
    apply cons_elem. right.
    apply app_elem. right.
    apply app_elem. auto.
      
  apply (H v); auto.
  apply finset_remove_elem.
  split; auto.
  intro. apply atom_strong_eq in H5. elim n0; auto.
Qed.
Next Obligation.
  unfold binding_support in *. destruct x as [u x]; simpl in *.
  apply finset_remove_elem in H. destruct H.
  apply finset_remove_elem. split.
  apply support_papp. auto.
  intro. apply H0.
  apply atom_strong_eq in H1.
  apply Perm.f_inj in H1. subst v; auto.
  
  unfold binding_support in *. destruct x as [u x]; simpl in *.
  apply finset_remove_elem in H. destruct H.
  apply finset_remove_elem. split.
  apply support_papp in H. auto.
  intro. apply H0.
  apply atom_strong_eq in H1. subst v. auto.
Qed.
  
Canonical Structure binding (A:nominal) : nominal :=
  Nominal.Ob (binding_ty A) (binding_eq_mixin A) (binding_nominal_mixin A).

(**  [binding] induces an endofunctor on NOMINAL. *)

Definition binding_fmap_defn (A B:nominal) (f:A → B) 
  (x:binding A) : binding B :=
  match x with
  | ν a, x' => ν a, (f x')
  end.

Program Definition binding_fmap (A B:nominal) (f:A → B) : binding A → binding B :=
  Nominal.Hom (binding A) (binding B) (binding_fmap_defn A B f) _ _.

Next Obligation.
  red; simpl; intros.
  destruct x as [u x].
  destruct y as [v y].

  apply binding_equiv_forall with (avoid := ‖x‖ ++ ‖y‖).
  simpl. intros w ? Havoid.

  rewrite (binding_equiv_forall A (ν u, x) (ν v, y) nil) in H.
  simpl in H.
  rewrite <- Nominal.equivariant.
  rewrite <- Nominal.equivariant.
  apply Nominal.eq_axiom.
  apply (H w). intro.
  apply cons_elem in H1. destruct H1.
  apply H0. apply cons_elem; auto.
  apply cons_elem in H1. destruct H1.
  apply H0. apply cons_elem. right. apply cons_elem; auto.
  contradiction.
  intro. apply nil_elem in H1. auto.
Qed.
Next Obligation.
  apply binding_equiv_forall with (avoid := nil).
  destruct x as [v x]. simpl. intros u ? ?.
  rewrite Nominal.equivariant. auto.
Qed.


Lemma binding_fmap_ident (A:nominal) :
  binding_fmap A A id(A) ≈ id(binding A).
Proof.
  hnf; simpl. intros [u x]; simpl. auto.
Qed.

Lemma binding_fmap_compose (A B C:nominal) f g :
  binding_fmap B C f ∘ binding_fmap A B g ≈ binding_fmap A C (f ∘ g).
Proof.
  hnf; simpl. intros [u x]; simpl. auto.
Qed.

Lemma binding_fmap_respects (A B:nominal) (f f':A → B) :
  f ≈ f' -> binding_fmap A B f ≈ binding_fmap A B f'.
Proof.
  repeat intro. destruct x as [u x]. simpl.
  apply binding_equiv_forall with (avoid := nil).
  intros. apply papp_morphism; auto.
Qed.

Program Definition bindingF : functor NOMINAL NOMINAL :=
  Functor NOMINAL NOMINAL 
     binding binding_fmap _ _ _.
Next Obligation.
  etransitivity. 2: apply binding_fmap_ident.
  apply binding_fmap_respects. auto.
Qed.
Next Obligation.
  symmetry.
  etransitivity. apply binding_fmap_compose.
  apply binding_fmap_respects. auto.
Qed.
Next Obligation.
  apply binding_fmap_respects. auto.
Qed.



(*
Program Definition binding_eq_dec (A:nominal) 
  (H:eq_dec (NOMINAL.ob_eq A)) : eq_dec (NOMINAL.ob_eq (binding A)) :=
  EqDec _ _.
Next Obligation.
  destruct x as [v x].
  destruct y as [w y].
  set (u := fresh_atom (v::w::support x ++ support y)).
  set (x' := PERM.swap u v · x).
  set (y' := PERM.swap u w · y).
  destruct (@eqdec _ H x' y').
  left. hnf. exists u. split; auto.
  apply fresh_atom_is_fresh.

  right.
  intros [u' [??]].
  destruct (string_dec u u').
  subst u'. elim n; auto.
  rename n0 into Huu'.

  apply n; clear n.
  subst x' y'.
  rewrite (PERM.swap_swap u v).  
  rewrite (PERM.swap_swap u w).  
  transitivity (PERM.swap v u · PERM.swap u u' · x).
  rewrite (support_axiom A (PERM.swap u u') x). auto.
  simpl; intros.
  destruct (string_dec u v0). subst v0.
  elimtype False.
  eapply fresh_atom_is_fresh'. 
  2: unfold u in H2; apply H2.
  hnf; intros.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; auto.
  destruct (string_dec u' v0). subst v0.
  elim H0.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; auto.
  auto.

  assert (Huw : u <> w).
     intro. 
     apply (fresh_atom_is_fresh (v::w::support x ++ support y)).
     fold u. rewrite H2.
     apply cons_elem. right.
     apply cons_elem. auto.

  assert (Hwu' : w <> u').
     intro. subst u'.
     apply H0.
     apply cons_elem. right.
     apply cons_elem. auto.
     
  assert (Huv : u <> v).
     intro. 
     apply (fresh_atom_is_fresh (v::w::support x ++ support y)).
     fold u. rewrite H2.
     apply cons_elem. auto.
     
  assert (Hvu' : v <> u').
     intro.
     apply H0. subst u'.
     apply cons_elem. auto.

  rewrite nom_compose.
  rewrite PERM.swap_swizzle; auto.
  rewrite <- nom_compose.
  rewrite (PERM.swap_swap v u').
  rewrite H1.
  rewrite (PERM.swap_swap u' w).
  rewrite nom_compose.
  rewrite <- PERM.swap_swizzle; auto.
  rewrite <- nom_compose.  
  rewrite (support_axiom A (PERM.swap u u') y). auto.
  simpl; intros.
  destruct (string_dec u v0).
  subst v0.
  elimtype False.
  eapply fresh_atom_is_fresh'. 
  2: unfold u in H2; apply H2.
  hnf; intros.
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; auto.
  destruct (string_dec u' v0). subst v0.
  elim H0. 
  apply cons_elem. right.
  apply cons_elem. right.
  apply app_elem; auto.
  auto.
Defined.


Program Definition atom_nom_mixin : NOMINAL.mixin_of atom (Preord.ord_eq atom) :=
  NOMINAL.Mixin atom _ PERM.perm_f (fun x => x::nil) _ _ _ _ _.
Next Obligation.
  rewrite H.
  apply atom_strong_eq in H0. subst a. auto.
Qed.
Next Obligation.
  rewrite H; auto.
  apply cons_elem; auto.
Qed.
Next Obligation.
  apply cons_elem in H.  
  destruct H.
  apply atom_strong_eq in H. subst v.
  apply cons_elem; auto.
  apply nil_elem in H. elim H.
  apply cons_elem in H.  
  destruct H.
  apply atom_strong_eq in H. 
  apply PERM.f_inj in H. subst v.
  apply cons_elem; auto.
  apply nil_elem in H. elim H.
Qed.  

Canonical Structure atom_nom : nominal :=
  NOMINAL.Ob atom _ atom_nom_mixin.

Goal (bind atom_nom "a" "a" ≈ bind atom_nom "b" "b").
Proof.
  set (x := 
    if binding_eq_dec atom_nom (PREORD_EQ_DEC _ atom_dec)
    (bind atom_nom "a" "a") (bind atom_nom "b" "b")
    then true else false).
  cut (x = true -> bind atom_nom "a" "a" ≈ bind atom_nom "b" "b").
  intros. apply H.
  reflexivity.
  unfold x.
  destruct (binding_eq_dec atom_nom (PREORD_EQ_DEC _ atom_dec)
    (bind atom_nom "a" "a") (bind atom_nom "b" "b")).
  auto. intro. discriminate H.
Qed.

Goal (bind atom_nom "a" "a" ≉ bind atom_nom "b" "c").
Proof.
  set (x := 
    if binding_eq_dec atom_nom (PREORD_EQ_DEC _ atom_dec)
    (bind atom_nom "a" "a") (bind atom_nom "b" "c")
    then true else false).
  cut (x = false -> bind atom_nom "a" "a" ≉ bind atom_nom "b" "c").
  intros. apply H.
  reflexivity.
  unfold x.
  destruct (binding_eq_dec atom_nom (PREORD_EQ_DEC _ atom_dec)
    (bind atom_nom "a" "a") (bind atom_nom "b" "c")).
  intro. discriminate.
  auto.
Qed.

Goal (bind atom_nom "a" "c" ≈ bind atom_nom "b" "c").
Proof.
  set (x := 
    if binding_eq_dec atom_nom (PREORD_EQ_DEC _ atom_dec)
    (bind atom_nom "a" "c") (bind atom_nom "b" "c")
    then true else false).
  cut (x = true -> bind atom_nom "a" "c" ≈ bind atom_nom "b" "c").
  intros. apply H.
  reflexivity.
  unfold x.
  destruct (binding_eq_dec atom_nom (PREORD_EQ_DEC _ atom_dec)
    (bind atom_nom "a" "c") (bind atom_nom "b" "c")).
  intro. auto.
  intro. discriminate.
Qed.

*)