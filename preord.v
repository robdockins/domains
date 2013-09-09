Require Import Setoid.

Require Import basics.
Require Import categories.

Module Preord.
  Record mixin_of (T:Type) :=
    Mixin
    { ord : T -> T -> Prop
    ; refl : forall x, ord x x
    ; trans : forall {x y z},
             ord x y -> ord y z -> ord x z
    }.
  Structure type : Type :=
    Pack { carrier :> Type ; mixin : mixin_of carrier }.

  Definition ord_op T := ord _ (mixin T).

  Record hom (X Y:type) := Hom
    { map :> carrier X -> carrier Y
    ; axiom : forall (a b:carrier X), ord_op X a b -> ord_op Y (map a) (map b)
    }.

  Program Definition ident (X:type) : hom X X := Hom X X (fun x => x) _.
  Program Definition compose (X Y Z:type) (g:hom Y Z) (f:hom X Y)
    := Hom X Z (fun x => g (f x)) _.
  Next Obligation.
    apply axiom. apply axiom. auto.
  Qed.

  Definition comp_mixin := Comp.Mixin type hom ident compose.

  Definition eq (X:type) (a b:X) := ord_op X a b /\ ord_op X b a.

  Definition hom_ord (X Y:type) (f g:hom X Y) := forall x, ord_op Y (f x) (g x).
  Definition hom_eq (X Y:type) (f g:hom X Y) := forall x, eq Y (f x) (g x).

  Program Definition ord_mixin X Y := Mixin (hom X Y) (hom_ord X Y) _ _.
  Next Obligation.
    red; intro. apply refl.
  Qed.
  Next Obligation.
    red; intro. eapply trans; eauto.
    apply (H x0). apply (H0 x0).
  Qed.

  Program Definition eq_mixin X Y := Eq.Mixin (hom X Y) (hom_eq X Y) _ _ _.
  Next Obligation.
    red; intros. red. split; apply refl.
  Qed.
  Next Obligation.
    red; intros. red. split.
    destruct (H x0); auto.
    destruct (H x0); auto.
  Qed.
  Next Obligation.
    intro.
    destruct (H x0). destruct (H0 x0).
    split; eapply trans; eauto.
  Qed.

  Program Definition cat_class := Category.Class type hom eq_mixin comp_mixin _.
  Next Obligation.
    constructor.
    
    repeat intro. split. simpl. red. apply refl.
    repeat intro. simpl. red. apply refl.

    repeat intro. split. simpl. red. apply refl.
    simpl. red. apply refl.
    
    repeat intro. split; simpl; red; apply refl.
    repeat intro. split; simpl; red.
    apply trans with (f (g' x)).
    apply axiom.
    destruct (H0 x); auto.
    destruct (H (g' x)); auto.
    apply trans with (f (g' x)).
    destruct (H (g' x)); auto.
    apply axiom.
    destruct (H0 x); auto.
  Qed.

  Program Definition ord_eq (T:type) : Eq.mixin_of T :=
    Eq.Mixin T (eq T) _ _ _.
  Next Obligation.
    split; apply refl.
  Qed.
  Next Obligation.
    destruct H; split; auto.
  Qed.
  Next Obligation.
    destruct H; destruct H0.
    split; eapply trans; eauto.
  Qed.
End Preord.
Notation preord := Preord.type.
Notation "x ≤ y" := (@Preord.ord_op _ x y) (at level 70).
Notation "y ≥ x" := (@Preord.ord_op _ x y) (at level 70, only parsing).
Notation "x ≰ y" := (~ (@Preord.ord_op _ x y)) (at level 70).
Notation "y ≱ x" := (~ (@Preord.ord_op _ x y)) (at level 70, only parsing).

Coercion Preord.carrier : Preord.type >-> Sortclass.

Canonical Structure hom_order X Y := Preord.Pack (Preord.hom X Y) (Preord.ord_mixin X Y).
Canonical Structure Preord_Eq (X:Preord.type) : Eq.type :=
  Eq.Pack (Preord.carrier X) (Preord.ord_eq X).
Canonical Structure PREORD :=
  Category Preord.type Preord.hom Preord.cat_class.
Canonical Structure preord_hom_eq (A B:preord):=
  Eq.Pack (Preord.hom A B) (Preord.eq_mixin A B).
Canonical Structure preord_comp :=
  Comp.Pack preord Preord.hom Preord.comp_mixin.


Lemma ord_refl : forall (T:Preord.type) (x:T), x ≤ x.
Proof.
  intros. destruct T. destruct mixin. apply refl.
Qed.

Lemma ord_trans : forall (T:Preord.type) (x y z:T), x ≤ y -> y ≤ z -> x ≤ z.
Proof.
  intros. destruct T. destruct mixin. eapply trans; eauto.
Qed.

Lemma ord_antisym : forall (T:Preord.type) (x y:T), x ≤ y -> y ≤ x -> x ≈ y.
Proof.
  intros. split; auto.
Qed.

Lemma eq_ord : forall (T:preord) (x y:T), x ≈ y -> x ≤ y.
Proof.
  intros; destruct H; auto.
Qed.

Lemma eq_ord' : forall (T:preord) (x y:T), x ≈ y -> y ≤ x.
Proof.
  intros; destruct H; auto.
Qed.

Add Parametric Relation (A:preord) : (Preord.carrier A) (@Preord.ord_op A)
  reflexivity proved by (ord_refl A)
  transitivity proved by (ord_trans A)
    as ord_rel.

Require Import Coq.Program.Basics.

Add Parametric Morphism (A:preord) :
  (@Preord.ord_op A)
    with signature (Preord.ord_op A) -->
                   (Preord.ord_op A) ++>
                   impl
     as ord_morphism.
Proof.
  repeat intro.
  transitivity x; auto.
  transitivity x0; auto.
Qed.

Add Parametric Morphism (A:preord) :
  (@Preord.ord_op A)
    with signature (eq_op (Preord_Eq A)) ==>
                   (eq_op (Preord_Eq A)) ==>
                   iff
     as ord_eq_morphism.
Proof.
  intros. 
  destruct H; destruct H0.
  split; intros.
  transitivity x; auto.
  transitivity x0; auto.
  transitivity y; auto.
  transitivity y0; auto.
Qed.

Program Definition PREORD_concrete : concrete PREORD :=
  Concrete PREORD
  Preord.carrier
  (fun X => Eq.mixin (Preord_Eq X))
  Preord.map _ _.
Next Obligation.
  split. 
  apply ord_trans with (Preord.map A B f y).
  apply Preord.axiom. destruct H0; auto. 
  destruct (H y); auto.
  apply ord_trans with (Preord.map A B f y).
  destruct (H y); auto.
  apply Preord.axiom. destruct H0; auto. 
Qed.
Next Obligation.
  split; apply Preord.refl.
Qed.

Canonical Structure PREORD_concrete.

Lemma preord_eq : forall (X Y:preord) (f:X → Y) (x y:X), x ≈ y -> f#x ≈ f#y.
Proof.
  intros. rewrite H. auto.
Qed.

Lemma preord_ord : forall (X Y:preord) (f:X → Y) (x y:X), x ≤ y -> f#x ≤ f#y.
Proof.
  intros. apply Preord.axiom. auto.
Qed.  

Hint Resolve ord_refl ord_trans ord_antisym preord_ord preord_eq eq_ord eq_ord'.


Lemma use_ord (A:preord) (a b c d:A) :
  b ≤ c -> a ≤ b -> c ≤ d -> a ≤ d.
Proof.
  intros.
  transitivity b; auto.
  transitivity c; auto.
Qed.
Arguments use_ord [A] [a] [b] [c] [d] _ _ _.


Add Parametric Relation (T:preord) : (Preord.carrier T) (@Preord.ord_op T)
  reflexivity proved by (@ord_refl T)
  transitivity proved by (@ord_trans T)
  as ord_op_rel.

Add Parametric Morphism (X Y:preord) :
  (@hommap PREORD PREORD_concrete X Y)
  with signature (eq_op (CAT_EQ PREORD X Y)) ==> 
                 (eq_op (Preord_Eq X)) ==>
                 (eq_op (Preord_Eq Y))
  as preord_apply_eq_morphism.
Proof.
  intros.
  transitivity (x#y0).
  apply preord_eq; auto.
  apply H.
Qed.

Add Parametric Morphism (X Y:preord) :
  (@hommap PREORD PREORD_concrete X Y)
  with signature (eq_op (CAT_EQ PREORD X Y)) ++> 
                 (eq_op (Preord_Eq X)) ++>
                 (Preord.ord_op Y)
  as preord_apply_eqord_morphism.
Proof.
  intros.
  transitivity (x#y0).
  apply preord_eq; auto.
  apply H.
Qed.

Add Parametric Morphism (X Y:preord) :
  (@hommap PREORD PREORD_concrete X Y)
  with signature (fun (x y:hom PREORD X Y) => Preord.ord_op (hom_order X Y) x y) ==> 
                 (Preord.ord_op X) ==>
                 (Preord.ord_op Y)
  as preord_apply_ord_morphism.
Proof.
  intros. 
  transitivity (x#y0).
  apply preord_ord. auto.
  apply H.
Qed.

Definition sum_ord (A B:preord) (x y:A+B):=
  match x, y with
  | inl x', inl y' => x' ≤ y'
  | inr x', inr y' => x' ≤ y'
  | _, _ => False
  end.

Program Definition sum_preord (A B:preord) : preord :=
  Preord.Pack (A+B) (Preord.Mixin _ (sum_ord A B) _ _).
Next Obligation.
  hnf. destruct x; auto.
Qed.
Next Obligation.
  hnf. destruct x; destruct y; destruct z; simpl in *; intuition.
  eapply ord_trans; eauto.
  eapply ord_trans; eauto.
Qed.

Canonical Structure sum_preord.

Definition prod_ord (A B:preord) (x y:A*B):=
  (fst x) ≤ (fst y) /\ (snd x) ≤ (snd y).

Program Definition prod_preord (A B:preord) : preord :=
  Preord.Pack (A*B) (Preord.Mixin _ (prod_ord A B) _ _).
Next Obligation.
  hnf. simpl; auto.
Qed.
Next Obligation.
  destruct H; destruct H0; split; simpl in *.
  eapply ord_trans; eauto.
  eapply ord_trans; eauto.
Qed.

Canonical Structure prod_preord.

Goal forall (X Y:preord) (f g:X→Y) (a b:X), 
  f ≤ g -> a ≈ b -> f#a ≤ g#b.
Proof.
  intros. rewrite H. rewrite H0. auto.
Qed.

Notation "A × B" := (prod_preord A B) (at level 54, right associativity).

Program Definition pi1 {A B:preord} : A × B → A :=
  Preord.Hom (A × B) A (fun x => fst x) _.
Next Obligation.
  destruct H; simpl; auto.
Qed.

Program Definition pi2 {A B:preord} : A × B → B :=
  Preord.Hom (A × B) B (fun x => snd x) _.
Next Obligation.
  destruct H; simpl; auto.
Qed.

Notation "'π₁'" := (@pi1 _ _).
Notation "'π₂'" := (@pi2 _ _).

Program Definition mk_pair {C A B:preord} (f:C → A) (g:C → B) : C → A×B :=
  Preord.Hom C (A×B) (fun c => (f#c, g#c)) _.
Next Obligation.
  intros. split; simpl; apply Preord.axiom; auto.
Qed.  

Program Definition pair_map {A B C D:preord} (f:A → B) (g:C → D) : A×C → B×D :=
  mk_pair (f ∘ π₁) (g ∘ π₂).


Record ord_dec (A:preord) :=
  OrdDec
  { orddec :> forall x y:A, {x ≤ y}+{x ≰ y} }.

Arguments orddec [A] [o] x y.

Canonical Structure PREORD_EQ_DEC (A:preord) (OD:ord_dec A) :=
  EqDec (Preord_Eq A) (fun (x y:A) =>
      match @orddec A OD x y with
      | left H1 => 
          match @orddec A OD y x with
          | left H2 => left _ (conj H1 H2)
          | right H => right _ (fun HEQ => H (proj2 HEQ))
          end
      | right H => right (fun HEQ => H (proj1 HEQ))
      end).

Program Definition unitpo := Preord.Pack unit (Preord.Mixin _ (fun _ _ => True) _ _).
Canonical Structure unitpo.

Program Definition emptypo := Preord.Pack False (Preord.Mixin _ (fun _ _ => False) _ _).
Canonical Structure emptypo.

Definition lift_ord (A:preord) (x:option A) (y:option A) : Prop :=
   match x with None => True | Some x' =>
     match y with None => False | Some y' => x' ≤ y' end end.

Program Definition lift_mixin (A:preord) : Preord.mixin_of (option A) :=
  Preord.Mixin (option A) (lift_ord A) _ _.
Next Obligation.
  destruct x; simpl; auto.
Qed.
Next Obligation.
  destruct x; destruct y; destruct z; simpl in *; intuition. eauto.
Qed.

Canonical Structure lift (A:preord) : preord :=
  Preord.Pack (option A) (lift_mixin A).

Program Definition liftup (A:preord) : A → lift A :=
  Preord.Hom A (lift A) (@Some A) _.

Program Definition lift_map {A B:preord} (f:A → B) : lift A → lift B :=
  Preord.Hom (lift A) (lift B) (option_map (Preord.map A B f)) _.
Next Obligation.
  red; intros. destruct a; destruct b; simpl in *; auto.
Qed.

Lemma lift_map_id (A:preord) : lift_map id(A) ≈ id(lift A).
Proof.
  split; hnf; destruct x; simpl; auto.
Qed.

Lemma lift_map_compose (A B C:preord) (g:B → C) (f:A → B) :
  lift_map (g ∘ f) ≈ lift_map g ∘ lift_map f.
Proof.
  split; hnf; destruct x; simpl; auto.
Qed.

Lemma lift_map_eq (A B:preord) (f f':A → B) : f ≈ f' -> lift_map f ≈ lift_map f'.
Proof.
  intros.
  split; hnf; destruct x; simpl; auto.
  apply H. apply H.
Qed.

Program Definition liftF : functor PREORD PREORD :=
  (Functor PREORD PREORD lift (@lift_map) _ _ _).
Next Obligation.
  transitivity (lift_map id(A)).
  apply lift_map_eq; auto.
  apply lift_map_id.
Qed.
Next Obligation.
  transitivity (lift_map (f ∘ g)).
  apply lift_map_eq; auto.
  apply lift_map_compose.
Qed.
Next Obligation.
  apply lift_map_eq. auto.
Qed.
