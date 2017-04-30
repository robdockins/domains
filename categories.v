(* Copyright (c) 2014, Robert Dockins *)

Require Import Setoid.

Require Import basics.

(** * Some elementary category theory.
    
      Here we develop enough category theory to support our investigations
      of domain theory.  We follow the general strategy used by several
      authors (FIXME look up citation) for defining category theory inside
      type theory, which is to equip every hom-set with an equivalance relation.
      Then the category axioms are all stated with respect to the setoid structure
      on hom-sets, and furthermore composition and functor actions are required
      to respect hom-set equality.
  *)

Delimit Scope category_ob_scope with cat_ob.
Delimit Scope category_hom_scope with cat.
Delimit Scope category_ops_scope with cat_ops.

Open Scope category_ob_scope.
Open Scope category_hom_scope.
Open Scope category_ops_scope.

(**  The [Comp] module represents the structure of composition
     and an identity.  Later we will layer on the category
     axioms and the setoid structure.  It is convenient to break
     out just the operations into a separate structure from
     the category structure.
  *)
Module Comp.
  Record mixin_of (ob:Type) (hom:ob -> ob -> Type) :=
    Mixin
    { identity : forall A, hom A A
    ; comp : forall A B C, hom B C -> hom A B -> hom A C }.
  Structure type : Type :=
    Pack { ob : Type; hom : ob -> ob -> Type; mixin: mixin_of ob hom }.
End Comp.
Definition comp_op T := Comp.comp _ _ (Comp.mixin T).
Definition ident_op T := Comp.identity _ _ (Comp.mixin T).

Notation "x ∘ y" := (@comp_op _ _ _ _ (x)%cat (y)%cat) : category_hom_scope.
Notation "'id'" := (@ident_op _ _) : category_hom_scope.
Notation "'id' ( A )" := (@ident_op _ (A)%cat_ob) (only parsing) 
  : category_hom_scope.

(**  Here we put together the pieces: the setoid structure
     on hom-sets, the composition strucutre, and the category axioms.
  *)
Module Category.
Section category.
  Variable ob:Type.
  Variable hom : ob -> ob -> Type.
  
  Variable (EQ:forall A B, Eq.mixin_of (hom A B)).
  Variable (COMP:Comp.mixin_of ob hom).

  Canonical Structure cat_EQ A B := Eq.Pack _ (EQ A B).
  Canonical Structure cat_COMP := Comp.Pack _ _ COMP.

  Record axioms :=
  Axioms
  { ident1 : forall A B (f:hom A B), f ∘ id(A) ≈ f

  ; ident2 : forall A B (f:hom A B), id(B) ∘ f ≈ f

  ; assoc : forall A B C D (f:hom C D) (g:hom B C) (h:hom A B),
         f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h

  ; respects : forall A B C (f f':hom B C) (g g':hom A B),
         f ≈ f' -> g ≈ g' -> (f ∘ g) ≈ (f' ∘ g')
  }.
End category.

Record category :=
  Category
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq : forall A B, Eq.mixin_of (hom A B)
  ; comp : Comp.mixin_of ob hom
  ; cat_axioms : axioms ob hom eq comp
  }.
End Category.

Notation category := Category.category.
Notation Category := Category.Category.
Notation ob := Category.ob.
Notation hom := Category.hom.
Notation "A → B" := (Category.hom _ A B) : category_hom_scope.

Bind Scope category_ob_scope with Category.ob.

Coercion ob : category >-> Sortclass.

Canonical Structure CAT_EQ (C:category) A B
  := Eq.Pack (hom C A B) (Category.eq C A B).
Canonical Structure CAT_COMP (C:category) 
  := Comp.Pack (ob C) (hom C) (Category.comp C).

(**  Here we define some easier-to-use versions of the catgory axioms.
  *)
Section category_axioms.
  Variable C:category.

  Definition cat_ident1   := Category.ident1 _ _ _ _ (Category.cat_axioms C).
  Definition cat_ident2   := Category.ident2 _ _ _ _ (Category.cat_axioms C).
  Definition cat_assoc    := Category.assoc _ _ _ _ (Category.cat_axioms C).
  Definition cat_respects := Category.respects _ _ _ _ (Category.cat_axioms C).
End category_axioms.

(** Register composition as a morphism for the setoid equality. *) 
Add Parametric Morphism (CAT:category) (A B C:ob CAT) :
  (@comp_op (CAT_COMP CAT) A B C)
   with signature (eq_op (CAT_EQ CAT B C)) ==> 
                  (eq_op (CAT_EQ CAT A B)) ==>
                  (eq_op (CAT_EQ CAT A C))
  as category_morphism.
Proof.
  intros. apply cat_respects; trivial.
Qed.

(**  Groupoids are categories in which every morphism has an inverse.
     Groupoids generalize groups (hence the name) in the sense that
     a groupoid with a single object forms a group.
     
     When [f] is a morphism in a groupoid [f⁻¹] is its inverse.
  *)
Module Groupoid.
Section groupoid.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).
  Variable comp:Comp.mixin_of ob hom.
  Variable cat_axioms : Category.axioms ob hom eq comp.

  Section axioms.
    Definition eq' A B := Eq.Pack _ (eq A B).
    Definition comp' := Comp.Pack ob hom comp.
    Canonical Structure eq'.
    Canonical Structure comp'.

    Variable inv : forall (A B:ob) (f:hom A B), hom B A.

    Record axioms :=
      Axioms
      { inv_id1 : forall A B (f:hom A B), f ∘ inv A B f ≈ id
      ; inv_id2 : forall A B (f:hom A B), inv A B f ∘ f ≈ id
      }.
  End axioms. 

  Record mixin_of :=
  Mixin
  { inv : forall (A B:ob) (f:hom A B), hom B A
  ; groupoid_axioms : axioms inv
  }.
End groupoid.

Record groupoid :=
  Groupoid
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin : forall A B, Eq.mixin_of (hom A B)
  ; comp_mixin : Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; mixin : mixin_of ob hom eq_mixin comp_mixin
  }.

Definition eq (X:groupoid) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Definition comp (X:groupoid) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Definition category (X:groupoid) : category :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).

Definition inv_op (X:groupoid) := inv _ _ _ _ (mixin X).

End Groupoid.

Notation groupoid := Groupoid.groupoid.
Notation Groupoid := Groupoid.Groupoid.

Canonical Structure Groupoid.category.
Canonical Structure Groupoid.eq.
Canonical Structure Groupoid.comp.

Coercion Groupoid.category : groupoid >-> category.

Notation "f '⁻¹'" :=  (Groupoid.inv_op _ _ _ f) : category_hom_scope.

Lemma inv_id1 (X:groupoid) :
  forall (A B:X) (f:A → B), f ∘ f⁻¹ ≈ id.

Proof (Groupoid.inv_id1 _ _ _ _ _
        (Groupoid.groupoid_axioms _ _ _ _ (Groupoid.mixin X))).
Arguments inv_id1 [X A B] f.

Lemma inv_id2 (X:groupoid) :
  forall (A B:X) (f:A → B), f⁻¹ ∘ f ≈ id.

Proof (Groupoid.inv_id2 _ _ _ _ _
        (Groupoid.groupoid_axioms _ _ _ _ (Groupoid.mixin X))).
Arguments inv_id2 [X A B] f.

Lemma inv_inv (X:groupoid) :
  forall (A B:X) (f:A → B), (f⁻¹)⁻¹ ≈ f.
Proof.
  intros.
  generalize (inv_id2 f⁻¹). intro.
  generalize (inv_id2 f). intro.
  transitivity ((f⁻¹)⁻¹ ∘ f⁻¹ ∘ f).
  - rewrite <- (cat_assoc X).
    rewrite H0. symmetry. apply cat_ident1.
  - rewrite H. apply cat_ident2.
Qed.

Lemma inv_compose (X:groupoid) :
  forall (A B C:X) (g:B → C) (f:A → B), (g ∘ f)⁻¹ ≈ f⁻¹ ∘ g⁻¹.
Proof.
  intros.
  generalize (inv_id2 (g ∘ f)). intro.
  generalize (inv_id1 f). intro.
  generalize (inv_id1 g). intro.
  assert ((g ∘ f)⁻¹ ∘ (g ∘ f) ∘ f⁻¹ ≈ (g ∘ f)⁻¹ ∘ g).
  { rewrite <- (cat_assoc X).
    rewrite <- (cat_assoc X).
    rewrite H0.
    rewrite (cat_assoc X).
    apply cat_ident1.
  }
  rewrite H in H2.
  rewrite (cat_ident2 X) in H2.
  rewrite H2.
  rewrite <- (cat_assoc X).
  rewrite H1.
  rewrite (cat_ident1 X).
  auto.  
Qed.

Lemma inv_eq (X:groupoid) (A B:X) (f g:A → B) : 
  f ≈ g -> f⁻¹ ≈ g⁻¹.
Proof.
  intro.
  generalize (inv_id1 f). intros.
  transitivity (g⁻¹ ∘ (f ∘ f⁻¹)).
  - rewrite H at 2.  
    rewrite (cat_assoc X).
    generalize (inv_id2 g). intros.
    rewrite H1.
    rewrite (cat_ident2 X). auto.
  - rewrite H0.
    rewrite (cat_ident1 X). auto.
Qed.

Lemma inv_inj (X:groupoid) (A B:X) (f g:A → B) : 
  f⁻¹ ≈ g⁻¹ -> f ≈ g.
Proof.
  intros.
  apply (inv_eq X) in H.
  rewrite inv_inv in H.
  rewrite inv_inv in H.
  auto.
Qed.

Add Parametric Morphism (X:groupoid) (A B:X) :
  (Groupoid.inv_op X A B)
    with signature (eq_op (Groupoid.eq X A B)) ==>
                   (eq_op (Groupoid.eq X B A))
     as inv_morophism.
Proof (inv_eq X A B).


(**  A monomorphism is a morphism which cancels on the left.
  *)
Section mono.
  Variable C:category.

  Record monomorphism (A B:C) :=
    Monomorphism
    { mono_hom : A → B
    ; mono_axiom : forall X (g h:X → A),
        mono_hom ∘ g ≈ mono_hom ∘ h -> g ≈ h
    }.
End mono.
Arguments mono_hom [C] [A] [B] m.
Arguments mono_axiom [C] [A] [B] m [X] [g] [h] _.

Coercion mono_hom : monomorphism >-> hom.
Notation "A ↣ B" := (monomorphism _ A B) : category_hom_scope.

Program Definition mono_eq (C:category) (A B:C) :=
  Eq.Mixin (monomorphism C A B)
     (fun f g => mono_hom f ≈ mono_hom g) _ _ _.
Next Obligation.
  eauto.
Qed.

Program Definition mono_id (C:category) (A:C) :=
  Monomorphism C A A (id(A)) _.  
Next Obligation.
  rewrite (cat_ident2 C) in H.
  rewrite (cat_ident2 C) in H.
  auto.
Qed.

Program Definition mono_compose
  (C:category) (X Y Z:C) (g:Y ↣ Z) (f:X ↣ Y) :=
  Monomorphism C X Z (mono_hom g ∘ mono_hom f) _.
Next Obligation.
  intros.
  rewrite <- (cat_assoc C) in H.
  rewrite <- (cat_assoc C) in H.
  apply mono_axiom in H.
  apply mono_axiom in H.
  auto.
Qed.

Definition mono_comp_mixin C :=
  Comp.Mixin _ _ (mono_id C) (mono_compose C).

Program Definition mono_cat_axioms (C:category) :
  Category.axioms (ob C) (monomorphism C)
     (mono_eq C) (mono_comp_mixin C).
Proof.
  constructor.

  - intros. apply cat_ident1.
  - intros. apply cat_ident2.
  - intros. apply cat_assoc.
  - intros. apply cat_respects; auto.
Qed.

Canonical Structure MONO_EQ (C:category) A B
  := Eq.Pack (monomorphism C A B) (mono_eq C A B).
Canonical Structure MONO_COMP (C:category)
  := Comp.Pack (ob C) (monomorphism C)
       (Comp.Mixin _ _ (mono_id C) (mono_compose C)).
Canonical Structure MONO_CAT (C:category)
  := Category (ob C) (monomorphism C) (mono_eq C)
         (mono_comp_mixin C) (mono_cat_axioms C).

(*
Canonical Structure MONO_CONCRETE
  (C:category)
  (CC : concrete C) :
  concrete (MONO_COMP C) :=
    Concrete (MONO_COMP C)
      (fun X => obmap _ CC X) 
      (obeq _ CC)
      (fun X Y f x => hommap _ CC (mono_hom f) x)
      (fun X Y Z g f x =>
          hommap_axiom _ CC (mono_hom g) (mono_hom f) x).
Arguments MONO_CONCRETE [C] [CC].
*)

(**  Epimorphism are morphisms that cancel on the right.
  *)
Section epic.
  Variable C:category.

  Record epimorphism (A B:C) :=
    Epimorphism
    { epi_hom : A → B
    ; epi_axiom : forall X (g h:B → X),
         g ∘ epi_hom ≈ h ∘ epi_hom ->
         g ≈ h
    }.
End epic.
Arguments epi_hom [C] [A] [B] e.
Arguments epi_axiom [C] [A] [B] e _ _ _ _.

Coercion epi_hom : epimorphism >-> hom.
Notation "A ↠ B" := (epimorphism _ A B) : category_hom_scope.

Program Definition epi_eq (C:category) (A B:C) :=
  Eq.Mixin (epimorphism C A B)
     (fun f g => epi_hom f ≈ epi_hom g) _ _ _.
Next Obligation.
  eauto.
Qed.

Program Definition epi_id (C:category) (A:C) :=
  Epimorphism C A A (id(A)) _.  
Next Obligation.
  rewrite (cat_ident1 C) in H.
  rewrite (cat_ident1 C) in H.
  auto.
Qed.

Program Definition epi_compose
  (C:category) (X Y Z:C) (g:Y ↠ Z) (f:X ↠ Y) :=
  Epimorphism C X Z (epi_hom g ∘ epi_hom f) _.
Next Obligation.
  rewrite (cat_assoc C) in H.
  rewrite (cat_assoc C) in H.
  apply epi_axiom in H.
  apply epi_axiom in H.
  auto.
Qed.

Definition epi_comp_mixin C :=
  Comp.Mixin _ _ (epi_id C) (epi_compose C).

Program Definition epi_cat_axioms (C:category) :
  Category.axioms (ob C) (epimorphism C)
     (epi_eq C) (epi_comp_mixin C).
Proof.
  constructor.

  intros. apply cat_ident1.
  intros. apply cat_ident2.
  intros. apply cat_assoc.
  intros. apply cat_respects; auto.
Qed.

Canonical Structure EPI_EQ (C:category) A B
  := Eq.Pack (epimorphism C A B) (epi_eq C A B).
Canonical Structure EPI_COMP (C:category)
  := Comp.Pack (ob C) (epimorphism C) (epi_comp_mixin C).
Canonical Structure EPI_CAT (C:category)
  := Category (ob C) (epimorphism C) (epi_eq C)
         (epi_comp_mixin C) (epi_cat_axioms C).

(*
Canonical Structure EPI_CONCRETE
  (C:category)
  (CC : concrete (CAT_COMP C)) :
  concrete (EPI_COMP C) :=
    Concrete (EPI_COMP C)
      (fun X => obmap _ CC X) 
      (obeq _ CC)
      (fun X Y f x => hommap _ CC (epi_hom f) x)
      (fun X Y Z g f x =>
          hommap_axiom _ CC (epi_hom g) (epi_hom f) x).
Arguments EPI_CONCRETE [C] [CC].
*)


(**  An isomorphism is a pair of functions that, when composed
     in each direction, are equal to the identity.
  *)
Section iso.
  Variable C:category.

  Record isomorphism (A B: C) :=
    Isomorphism
    { iso_hom : A → B
    ; iso_inv : B → A
    ; iso_axiom1 : iso_inv ∘ iso_hom ≈ id
    ; iso_axiom2 : iso_hom ∘ iso_inv ≈ id
    }.
End iso.
Arguments iso_hom [C] [A] [B] i.
Arguments iso_inv [C] [A] [B] i.
Arguments iso_axiom1 [C] [A] [B] i.
Arguments iso_axiom2 [C] [A] [B] i.

Definition iso_hom' (C:category) (A B:C) (f:isomorphism C A B) : Comp.hom _ A B :=
  iso_hom f.
Definition iso_hom'' (C:category) (A B:ob C) (f:isomorphism C A B) : CAT_EQ C A B := 
  iso_hom f.

Coercion iso_hom : isomorphism >-> hom.
Coercion iso_hom' : isomorphism >-> Comp.hom.
Coercion iso_hom'' : isomorphism >-> Eq.carrier.

Notation "A ↔ B" := (isomorphism _ A B) : category_hom_scope.

Program Definition iso_eq (C:category) (A B:C) :=
  Eq.Mixin (isomorphism C A B)
     (fun f g => iso_hom f ≈ iso_hom g) _ _ _.
Next Obligation.
  eauto.
Qed.

Program Definition iso_id (C:category) (A:C) :=
  Isomorphism C A A id(A) id(A) _ _.
Next Obligation.
  apply cat_ident1.
Qed.
Next Obligation.
  apply cat_ident1.
Qed.

Program Definition iso_compose
  (C:category) (X Y Z:C) (g:Y ↔ Z) (f:X ↔ Y) :=
  Isomorphism C X Z (iso_hom g ∘ iso_hom f) (iso_inv f ∘ iso_inv g) _ _.
Next Obligation.
  intros. 
  rewrite <- (cat_assoc C _ _ _ _ (iso_inv f) (iso_inv g) (iso_hom g ∘ iso_hom f)).
  rewrite (cat_assoc C _ _ _ _ (iso_inv g) (iso_hom g) (iso_hom f)).
  rewrite (iso_axiom1 g).
  rewrite (cat_ident2 C).
  rewrite (iso_axiom1 f).
  auto.
Qed.
Next Obligation.
  rewrite <- (cat_assoc C _ _ _ _ (iso_hom g) (iso_hom f) (iso_inv f ∘ iso_inv g)).
  rewrite (cat_assoc C _ _ _ _(iso_hom f) (iso_inv f) (iso_inv g)).
  rewrite (iso_axiom2 f).
  rewrite (cat_ident2 C).
  rewrite (iso_axiom2 g).
  auto.
Qed.

Definition iso_comp_mixin C :=
  Comp.Mixin _ _ (iso_id C) (iso_compose C).

Program Definition iso_cat_axioms (C:category) :
  Category.axioms (ob C) (isomorphism C)
     (iso_eq C) (iso_comp_mixin C).
Proof.
  constructor.

  - intros; simpl. apply cat_ident1.
  - intros; simpl. apply cat_ident2.
  - intros; simpl. apply cat_assoc.
  - simpl; intros. apply cat_respects; auto.
Qed.

Definition iso_inverse (C:category) (A B:C) (f:A ↔ B) : B ↔ A :=
  Isomorphism C B A (iso_inv f) (iso_hom f)
    (iso_axiom2 f) (iso_axiom1 f).

Program Definition iso_groupoid_mixin (C:category) :=
  Groupoid.Mixin (ob C) (isomorphism C)
      (iso_eq C) (iso_comp_mixin C) (iso_inverse C) _.
Next Obligation.
  constructor.

  simpl; intros. 
  apply iso_axiom2.
  apply iso_axiom1.
Qed.


(*
Canonical Structure ISO_EQ (C:category) A B
  := Eq.Pack (isomorphism C A B) (iso_eq C A B).
Canonical Structure ISO_COMP (C:category)
  := Comp.Pack (ob C) (isomorphism C) (iso_comp_mixin C).
Canonical Structure ISO_CAT (C:category)
  := Category (ob C) (isomorphism C)
          (iso_eq C) (iso_comp_mixin C) (iso_cat_axioms C).
*)
Canonical Structure ISO_GROUPOID (C:category)
  := Groupoid (ob C) (isomorphism C)
          (iso_eq C) (iso_comp_mixin C)
          (iso_cat_axioms C) (iso_groupoid_mixin C).



(**  Categories with terminal objects, which we call terminated categories.

     Such categories have a distinguished object [terminus] (notation [!])
     and a family of morphisms [terminate : A → !] for each object [A].
     Furthermore, [terminate] is universial, in that every for every
     [f : A → !], [f ≈ terminate].
  *)
Module Terminated.
Section terminated.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).

  Definition eq' A B := Eq.Pack _ (eq A B).

  Canonical Structure eq'.

  Record mixin_of :=
  Mixin
  { terminus : ob
  ; terminate : forall A:ob, hom A terminus
  ; axiom : forall A (f:hom A terminus), f ≈ terminate A
  }.
End terminated.
  
Record terminated :=
  Terminated
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin : forall A B, Eq.mixin_of (hom A B)
  ; comp_mixin : Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; mixin : mixin_of ob hom eq_mixin
  }.

Canonical Structure eq (X:terminated) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Canonical Structure comp (X:terminated) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Canonical Structure category (X:terminated) :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).

Definition terminus_op (X:terminated) := terminus _ _ _ (mixin X).
Definition terminate_op (X:terminated) := terminate _ _ _ (mixin X).
End Terminated.

Notation terminated := Terminated.terminated.
Notation Terminated := Terminated.Terminated.

Canonical Structure Terminated.eq.
Canonical Structure Terminated.comp.
Canonical Structure Terminated.category.
Coercion Terminated.category : terminated >-> category.

Notation "'!'" := (Terminated.terminus_op _) : category_ob_scope.
Notation "'∗'" := (Terminated.terminate_op _ _) : category_ops_scope.

Lemma terminate_univ (X:terminated) :
  forall (A:X) (f:A → !), f ≈ ∗.
Proof (Terminated.axiom _ _ _ (Terminated.mixin X)).

(**  Categories with initial objects, called initilized categories.

     Such categories have a distinguished object [initium] (notation [¡])
     and a family of morphisms [initiate : ¡ → A] for each object [A].
     Furthermore, [initiate] is universial, in that every for every
     [f : ¡ → A], [f ≈ initiate].
  *)
Module Initialized.
Section initialized.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).

  Definition eq' A B := Eq.Pack _ (eq A B).

  Canonical Structure eq'.

  Record mixin_of :=
  Mixin
  { initium : ob
  ; initiate : forall A:ob, hom initium A
  ; axiom : forall A (f:hom initium A), f ≈ initiate A
  }.
End initialized.
  
Record initialized :=
  Initialized
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin : forall A B, Eq.mixin_of (hom A B)
  ; comp_mixin : Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; mixin : mixin_of ob hom eq_mixin
  }.

Canonical Structure eq (X:initialized) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Canonical Structure comp (X:initialized) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Canonical Structure category (X:initialized) :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).

Definition initium_op (X:initialized) := initium _ _ _ (mixin X).
Definition initiate_op (X:initialized) := initiate _ _ _ (mixin X).
End Initialized.

Notation initialized := Initialized.initialized.
Notation Initialized := Initialized.Initialized.

Canonical Structure Initialized.eq.
Canonical Structure Initialized.comp.
Canonical Structure Initialized.category.
Coercion Initialized.category : initialized >-> category.

Notation "'¡'" := (Initialized.initium_op _) : category_ob_scope.
Notation initiate := (Initialized.initiate_op _ _).

Lemma initiate_univ (X:initialized) :
  forall (A:X) (f:¡ → A), f ≈ initiate.
Proof (Initialized.axiom _ _ _ (Initialized.mixin X)).


(**  Cocartesian categories have all finite coproducts.  In particular
     they are initialized and have a binary coproduct for every pair
     of objects satisfying the usual universal property.

     The coproduct of [A] and [B] is written [A + B].  The injection
     functions are [ι₁] and [ι₂].  When we have [f:A → C]  and [g:B → C],
     the case function [either f g : A⊕B → C] is the mediating universal
     morphism for the colimit diagram.
  *)
Module Cocartesian.
Section cocartesian.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).
  Variable comp:Comp.mixin_of ob hom.
  
  Definition eq' A B := Eq.Pack _ (eq A B).
  Definition comp' := Comp.Pack ob hom comp.

  Canonical Structure eq'.
  Canonical Structure comp'.

  Section axioms.
    Variable sum : ob -> ob -> ob.
    Variable inl : forall A B, hom A (sum A B).
    Variable inr : forall A B, hom B (sum A B).
    Variable either : forall C A B:ob,
      hom A C -> hom B C -> hom (sum A B) C.

    Record axioms :=
      Axioms
      { inl_commute : forall (C A B:ob) f g,
          either C A B f g ∘ inl A B ≈ f 
      ; inr_commute : forall (C A B:ob) f g,
          either C A B f g ∘ inr A B ≈ g
      ; either_univ : forall (C A B:ob) f g h,
          h ∘ inl A B ≈ f ->
          h ∘ inr A B ≈ g ->
          h ≈ either C A B f g
      }.
  End axioms.

  Record mixin_of :=
  Mixin
  { sum : ob -> ob -> ob
  ; inl : forall A B:ob, hom A (sum A B)
  ; inr : forall A B:ob, hom B (sum A B)
  ; either : forall C A B:ob, hom A C -> hom B C -> hom (sum A B) C
  ; cocartesian_axioms : axioms sum inl inr either
  }.
End cocartesian.
  
Record cocartesian :=
  Cocartesian
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin:forall A B:ob, Eq.mixin_of (hom A B)
  ; comp_mixin:Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; init_mixin : Initialized.mixin_of ob hom eq_mixin
  ; mixin : mixin_of ob hom eq_mixin comp_mixin
  }.

Definition sum_op (X:cocartesian) := sum _ _ _ _ (mixin X).
Definition inl_op (X:cocartesian) := inl _ _ _ _ (mixin X).
Definition inr_op (X:cocartesian) := inr _ _ _ _ (mixin X).
Definition either_op (X:cocartesian) := either _ _ _ _ (mixin X).

Definition eq (X:cocartesian) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Definition comp (X:cocartesian) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Definition initalized (X:cocartesian) :=
  Initialized (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) (init_mixin X).
Definition category (X:cocartesian) :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).
End Cocartesian.

Notation cocartesian := Cocartesian.cocartesian.
Notation Cocartesian := Cocartesian.Cocartesian.

Canonical Structure Cocartesian.eq.
Canonical Structure Cocartesian.comp.
Canonical Structure Cocartesian.category.
Canonical Structure Cocartesian.initalized.

Coercion Cocartesian.initalized : cocartesian >-> initialized.
Coercion Cocartesian.category : cocartesian >-> category.

Notation "A + B" := (Cocartesian.sum_op _ A B)
  : category_ob_scope.
Notation "'ι₁'"  := (Cocartesian.inl_op _ _ _) : category_ops_scope.
Notation "'ι₂'"  := (Cocartesian.inr_op _ _ _) : category_ops_scope.
Notation either := Cocartesian.either_op.
Arguments either [X C A B] f g.

Lemma inl_commute (X:cocartesian) :
  forall (C A B:ob X) (f:A → C) (g:B → C), either f g ∘ ι₁ ≈ f.

Proof (Cocartesian.inl_commute _ _ _ _ _ _ _ _ 
         (Cocartesian.cocartesian_axioms _ _ _ _ (Cocartesian.mixin X))).

Lemma inr_commute (X:cocartesian) :
  forall (C A B:ob X) (f:A → C) (g:B → C), either f g ∘ ι₂ ≈ g.

Proof (Cocartesian.inr_commute _ _ _ _ _ _ _ _ 
         (Cocartesian.cocartesian_axioms _ _ _ _ (Cocartesian.mixin X))).

Lemma either_univ (X:cocartesian) :
  forall (C A B:ob X) (f:A → C) (g:B → C) (h:A+B → C),
  h ∘ ι₁ ≈ f -> h ∘ ι₂ ≈ g -> h ≈ either f g.

Proof (Cocartesian.either_univ _ _ _ _ _ _ _ _
         (Cocartesian.cocartesian_axioms _ _ _ _ (Cocartesian.mixin X))).

Program Definition sum_map (X:cocartesian) (A B C D:ob X)
  (f:A → B) (g:C → D) : A+C → B+D := either (ι₁ ∘ f) (ι₂ ∘ g).
Arguments sum_map [X A B C D] f g.

Add Parametric Morphism (X:cocartesian) (C A B:ob X) :
  (@Cocartesian.either_op X C A B)
   with signature (eq_op (Cocartesian.eq X A C)) ==>
                  (eq_op (Cocartesian.eq X B C)) ==>
                  (eq_op (Cocartesian.eq X (A+B)%cat_ob C))
    as either_morphism.
Proof.
  intros. apply either_univ.
  rewrite <- H. apply inl_commute.
  rewrite <- H0. apply inr_commute.
Qed.

(**  Cartesian categories have all finite products.  In particular
     they are terminated and have a binary product for every pair
     of objects satisfying the usual universal property.

     The product of [A] and [B] is written [A × B].  The projection
     functions are [π₁] and [π₂].  When we have [f:C → A]  and [g:C → B],
     the pairing function [〈 f, g 〉 : C → A×B] is the mediating universal
     morphism for the limit diagram.
  *)
Module Cartesian.
Section cartesian.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).
  Variable comp:Comp.mixin_of ob hom.
  
  Definition eq' A B := Eq.Pack _ (eq A B).
  Definition comp' := Comp.Pack ob hom comp.

  Canonical Structure eq'.
  Canonical Structure comp'.

  Section axioms.

    Variable product : ob -> ob -> ob.
    Variable proj1 : forall A B, hom (product A B) A.
    Variable proj2 : forall A B, hom (product A B) B.
    Variable pairing : forall C A B:ob, hom C A -> hom C B -> hom C (product A B).

    Record axioms :=
      Axioms
      { proj1_commute : forall (C A B:ob) f g,
          proj1 A B ∘ pairing C A B f g ≈ f
      ; proj2_commute : forall (C A B:ob) f g,
          proj2 A B ∘ pairing C A B f g ≈ g
      ; pairing_univ : forall (C A B:ob) f g h,
          proj1 A B ∘ h ≈ f ->
          proj2 A B ∘ h ≈ g ->
          h ≈ pairing C A B f g
      }.
  End axioms.

  Record mixin_of :=
  Mixin
  { product : ob -> ob -> ob
  ; proj1 : forall A B:ob, hom (product A B) A
  ; proj2 : forall A B:ob, hom (product A B) B
  ; pairing : forall C A B:ob, hom C A -> hom C B -> hom C (product A B)
  ; cartesian_axioms : axioms product proj1 proj2 pairing
  }.
End cartesian.
  
Record cartesian :=
  Cartesian
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin:forall A B:ob, Eq.mixin_of (hom A B)
  ; comp_mixin:Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; term_mixin : Terminated.mixin_of ob hom eq_mixin
  ; mixin : mixin_of ob hom eq_mixin comp_mixin
  }.

Definition product_op (X:cartesian) := product _ _ _ _ (mixin X).
Definition proj1_op (X:cartesian) := proj1 _ _ _ _ (mixin X).
Definition proj2_op (X:cartesian) := proj2 _ _ _ _ (mixin X).
Definition pairing_op (X:cartesian) := pairing _ _ _ _ (mixin X).

Definition eq (X:cartesian) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Definition comp (X:cartesian) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Definition terminated (X:cartesian) :=
  Terminated (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) (term_mixin X).
Definition category (X:cartesian) :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).
End Cartesian.

Notation cartesian := Cartesian.cartesian.
Notation Cartesian := Cartesian.Cartesian.

Canonical Structure Cartesian.eq.
Canonical Structure Cartesian.comp.
Canonical Structure Cartesian.category.
Canonical Structure Cartesian.terminated.

Coercion Cartesian.terminated : cartesian >-> terminated.
Coercion Cartesian.category : cartesian >-> category.

Notation "A × B" := (Cartesian.product_op _ A B)
  : category_ob_scope.
Notation "'π₁'"  := (Cartesian.proj1_op _ _ _) : category_ops_scope.
Notation "'π₂'"  := (Cartesian.proj2_op _ _ _) : category_ops_scope.
Notation "〈 f , g 〉" := (Cartesian.pairing_op _ _ _ _ f g)
  : category_ops_scope.

Lemma proj1_commute (X:cartesian) :
  forall (C A B:ob X) (f:C → A) (g:C → B), π₁ ∘ 〈 f, g 〉 ≈ f.

Proof (Cartesian.proj1_commute _ _ _ _ _ _ _ _ 
         (Cartesian.cartesian_axioms _ _ _ _ (Cartesian.mixin X))).

Lemma proj2_commute (X:cartesian) :
  forall (C A B:ob X) (f:C → A) (g:C → B), π₂ ∘ 〈 f, g 〉 ≈ g.

Proof (Cartesian.proj2_commute _ _ _ _ _ _ _ _ 
         (Cartesian.cartesian_axioms _ _ _ _ (Cartesian.mixin X))).

Lemma pairing_univ (X:cartesian) :
  forall (C A B:ob X) (f:C → A) (g:C → B) (h:C → A × B),
  π₁ ∘ h ≈ f -> π₂ ∘ h ≈ g -> h ≈ 〈 f, g 〉.

Proof (Cartesian.pairing_univ _ _ _ _ _ _ _ _
         (Cartesian.cartesian_axioms _ _ _ _ (Cartesian.mixin X))).

Program Definition pair_map (X:cartesian) (A B C D:ob X)
  (f:A → B) (g:C → D) : A×C → B×D :=
  〈 f ∘ π₁, g ∘ π₂ 〉.
Arguments pair_map [X A B C D] f g.

Add Parametric Morphism (X:cartesian) (C A B:ob X) :
  (Cartesian.pairing_op X C A B)
   with signature (eq_op (Cartesian.eq X C A)) ==>
                  (eq_op (Cartesian.eq X C B)) ==>
                  (eq_op (Cartesian.eq X C (A×B)%cat_ob))
    as pairing_morphism.
Proof.
  intros. apply pairing_univ.
  rewrite proj1_commute. auto.
  rewrite proj2_commute. auto.
Qed.


(**  A distributive category has binary products and binary coproducts,
     and sums distribute over products. 
  *)
Module Distributive.
Section distributive.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).
  Variable comp:Comp.mixin_of ob hom.
  Variable cat_axioms : Category.axioms ob hom eq comp.
  Variable terminated : Terminated.mixin_of ob hom eq.
  Variable cartesian : Cartesian.mixin_of ob hom eq comp.
  Variable initialized : Initialized.mixin_of ob hom eq.
  Variable cocartesian : Cocartesian.mixin_of ob hom eq comp.
  
  Definition eq' A B := Eq.Pack _ (eq A B).
  Definition comp' := Comp.Pack ob hom comp.
  Definition cartesian' := Cartesian ob hom eq comp cat_axioms terminated cartesian.
  Definition cocartesian' := Cocartesian ob hom eq comp cat_axioms initialized cocartesian.

  Canonical Structure eq'.
  Canonical Structure comp'.
  Canonical Structure cartesian'.
  Canonical Structure cocartesian'.

  Record mixin_of :=
  { distrib_law : forall A B C:ob, A×(B+C) ↔ (A×B) + (A×C)
  }.

End distributive.

Record distributive :=
  Distributive
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin : forall A B:ob, Eq.mixin_of (hom A B)
  ; comp_mixin : Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; terminated_mixin : Terminated.mixin_of ob hom eq_mixin
  ; cartesian_mixin : Cartesian.mixin_of ob hom eq_mixin comp_mixin
  ; initialized_mixin : Initialized.mixin_of ob hom eq_mixin
  ; cocartesian_mixin : Cocartesian.mixin_of ob hom eq_mixin comp_mixin
  ; mixin : mixin_of ob hom eq_mixin comp_mixin cat_axioms terminated_mixin cartesian_mixin initialized_mixin cocartesian_mixin
  }.

Definition distrib_law_op (X:distributive) :=
   distrib_law _ _ _ _ _ _ _ _ _ (mixin X).

Definition eq (X:distributive) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Definition comp (X:distributive) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Definition category (X:distributive) : category :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).
Definition terminated (X:distributive) : terminated :=
  Terminated (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) (terminated_mixin X).
Definition cartesian (X:distributive) : cartesian :=
  Cartesian (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) 
     (terminated_mixin X) (cartesian_mixin X).
Definition initialized (X:distributive) : initialized :=
  Initialized (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) (initialized_mixin X).
Definition cocartesian (X:distributive) : cocartesian :=
  Cocartesian (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) 
     (initialized_mixin X) (cocartesian_mixin X).
End Distributive.
  
Notation distributive := Distributive.distributive.
Notation Distributive := Distributive.Distributive.

Canonical Structure Distributive.eq.
Canonical Structure Distributive.comp.
Canonical Structure Distributive.category.
Canonical Structure Distributive.terminated.
Canonical Structure Distributive.cartesian.
Canonical Structure Distributive.initialized.
Canonical Structure Distributive.cocartesian.

Coercion Distributive.category : distributive >-> category.
Coercion Distributive.terminated : distributive >-> terminated.
Coercion Distributive.cartesian : distributive >-> cartesian.
Coercion Distributive.initialized : distributive >-> initialized.
Coercion Distributive.cocartesian : distributive >-> cocartesian.

Notation distrib_law := Distributive.distrib_law_op.
Arguments distrib_law [X A B C].

(**  Cartesian closed categories, in addition to being cartesian,
     have "internal" hom objects corresponding to each homset called
     the exponential object.  Here we give the definition of cartesian
     closure in terms of curry and apply morphisms.
     
     When [A] and [B] are objects, [A ⇒ B] is the exponential object.
     The morphism [apply : (A⇒B) × A → B] applies an internal hom
     to an argument.  For [f : C×A → B], we have a unique curried
     morphism [Λ f : C → A⇒B] that commutes with the action of [apply].
  *)
Module CartesianClosed.
Section cartesian_closed.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).
  Variable comp:Comp.mixin_of ob hom.
  Variable cat_axioms : Category.axioms ob hom eq comp.
  Variable terminated : Terminated.mixin_of ob hom eq.
  Variable cartesian : Cartesian.mixin_of ob hom eq comp.
  
  Definition eq' A B := Eq.Pack _ (eq A B).
  Definition comp' := Comp.Pack ob hom comp.
  Definition cartesian' := Cartesian ob hom eq comp cat_axioms terminated cartesian.

  Canonical Structure eq'.
  Canonical Structure comp'.
  Canonical Structure cartesian'.

  Section axioms.
    Variable exp : ob -> ob -> ob.
    Variable curry : forall C A B, (C×A → B) -> (C → exp A B).
    Variable apply : forall A B, exp A B × A → B.

    Record axioms :=
      Axioms
      { curry_commute : forall C A B (f:C×A → B),
           apply A B ∘ 〈 curry C A B f ∘ π₁, π₂ 〉 ≈ f
      ; curry_univ : forall C A B (f:C×A → B) (f':C → exp A B),
           apply A B ∘ 〈 f' ∘ π₁, π₂ 〉 ≈ f ->
           f' ≈ curry C A B f
      }.
  End axioms.

  Record mixin_of :=
  Mixin
  { exp : ob -> ob -> ob
  ; curry : forall C A B, (C×A → B) -> (C → exp A B)
  ; apply : forall A B, exp A B × A → B
  ; ccc_axioms : axioms exp curry apply
  }.
End cartesian_closed.

Record cartesian_closed :=
  CartesianClosed
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin : forall A B:ob, Eq.mixin_of (hom A B)
  ; comp_mixin : Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; cartesian_mixin : Cartesian.mixin_of ob hom eq_mixin comp_mixin
  ; terminated_mixin : Terminated.mixin_of ob hom eq_mixin
  ; mixin : mixin_of ob hom eq_mixin comp_mixin cat_axioms terminated_mixin cartesian_mixin
  }.

Definition curry_op (X:cartesian_closed) := curry _ _ _ _ _ _ _ (mixin X).
Definition apply_op (X:cartesian_closed) := apply _ _ _ _ _ _ _ (mixin X).
Definition exp_op (X:cartesian_closed) := exp _ _ _ _ _ _ _ (mixin X).

Definition eq (X:cartesian_closed) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Definition comp (X:cartesian_closed) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Definition category (X:cartesian_closed) : category :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).
Definition terminated (X:cartesian_closed) : terminated :=
  Terminated (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) (terminated_mixin X).
Definition cartesian (X:cartesian_closed) : cartesian :=
  Cartesian (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) 
     (terminated_mixin X) (cartesian_mixin X).
End CartesianClosed.
  
Notation cartesian_closed := CartesianClosed.cartesian_closed.
Notation CartesianClosed := CartesianClosed.CartesianClosed.

Canonical Structure CartesianClosed.eq.
Canonical Structure CartesianClosed.comp.
Canonical Structure CartesianClosed.category.
Canonical Structure CartesianClosed.terminated.
Canonical Structure CartesianClosed.cartesian.

Coercion CartesianClosed.category : cartesian_closed >-> category.
Coercion CartesianClosed.terminated : cartesian_closed >-> terminated.
Coercion CartesianClosed.cartesian : cartesian_closed >-> cartesian.

Notation "'Λ' f" := (CartesianClosed.curry_op _ _ _ _ f) : category_ops_scope.
Notation "A ⇒ B" := (CartesianClosed.exp_op _ A B)
  : category_ob_scope.
Notation apply := (CartesianClosed.apply_op _ _ _).

Lemma curry_commute (X:cartesian_closed) : 
  forall (C A B:ob X) (f:C×A → B), apply ∘ 〈 Λ f ∘ π₁, π₂ 〉 ≈ f.

Proof (CartesianClosed.curry_commute _ _ _ _ _ _ _ _ _ _
         (CartesianClosed.ccc_axioms _ _ _ _ _ _ _ (CartesianClosed.mixin X))).

Lemma curry_univ (X:cartesian_closed) :
  forall (C A B:ob X) (f:C×A → B) (f':C → A ⇒ B),
          apply ∘ 〈 f' ∘ π₁, π₂ 〉 ≈ f -> f' ≈ Λ f.

Proof (CartesianClosed.curry_univ _ _ _ _ _ _ _ _ _ _
         (CartesianClosed.ccc_axioms _ _ _ _ _ _ _ (CartesianClosed.mixin X))).

Add Parametric Morphism (X:cartesian_closed) (C A B:ob X) :
  (CartesianClosed.curry_op X C A B)
  with signature (eq_op (CartesianClosed.eq X (C×A)%cat_ob B)) ==>
                 (eq_op (CartesianClosed.eq X C (A⇒B)%cat_ob))
   as curry_morphism.
Proof.
  intros. apply curry_univ. rewrite curry_commute. auto.
Qed.

Lemma curry_commute3 (X:cartesian_closed) : 
  forall (D C A B:X) (f:C×A → B) (g:D → C) (h:D → A),
    apply ∘ 〈 Λ f ∘ g, h 〉 ≈ f ∘ 〈 g, h 〉.
Proof.
  intros.
  transitivity (apply ∘ 〈Λ f ∘ π₁, π₂〉 ∘ 〈g, h〉).
  - rewrite <- (cat_assoc X). apply (cat_respects X); auto.
    symmetry. apply pairing_univ.
    + rewrite (cat_assoc X).
      transitivity (Λ(f) ∘ π₁ ∘ 〈g,h〉).
      * apply cat_respects; auto.
        apply (proj1_commute X).
      * rewrite <- (cat_assoc X).
        apply cat_respects; auto.
        apply proj1_commute.
    + rewrite (cat_assoc X).
      transitivity (π₂ ∘ 〈g,h〉).
      * apply cat_respects; auto.
        apply (proj2_commute X).
      * apply (proj2_commute X).
  - apply cat_respects; auto.
    apply curry_commute.
Qed.

Lemma curry_commute2 (X:cartesian_closed) : 
  forall (C A B:X) (f:C×A → B) (h:C → A),
    apply ∘ 〈 Λ f, h 〉 ≈ f ∘ 〈 id, h 〉.
Proof.
  intros. rewrite <- (curry_commute3 X C C A B f id h).
  apply cat_respects; auto.
  apply pairing_morphism; auto.
  symmetry. apply cat_ident1.
Qed.

(**  Here I define "polynomial categories" as categories with finite sums,
     finite products, and exponents where sums distribute over products.

     As far as I know, this terminology is not already taken.
  *)
Module PolynomialCategory.

Record polynomial_category :=
  PolynomialCategory
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin : forall A B:ob, Eq.mixin_of (hom A B)
  ; comp_mixin : Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; terminated_mixin : Terminated.mixin_of ob hom eq_mixin
  ; cartesian_mixin : Cartesian.mixin_of ob hom eq_mixin comp_mixin
  ; initialized_mixin : Initialized.mixin_of ob hom eq_mixin
  ; cocartesian_mixin : Cocartesian.mixin_of ob hom eq_mixin comp_mixin
  ; ccc_mixin : CartesianClosed.mixin_of ob hom eq_mixin comp_mixin 
       cat_axioms terminated_mixin cartesian_mixin
  ; distributive_mixin : Distributive.mixin_of ob hom eq_mixin comp_mixin
       cat_axioms terminated_mixin cartesian_mixin
                  initialized_mixin cocartesian_mixin
  }.

Definition eq (X:polynomial_category) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Definition comp (X:polynomial_category) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Definition category (X:polynomial_category) : category :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).
Definition terminated (X:polynomial_category) : terminated :=
  Terminated (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X)
     (terminated_mixin X).
Definition cartesian (X:polynomial_category) : cartesian :=
  Cartesian (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) 
     (terminated_mixin X) (cartesian_mixin X).
Definition initialized (X:polynomial_category) : initialized :=
  Initialized (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X)
     (initialized_mixin X).
Definition cocartesian (X:polynomial_category) : cocartesian :=
  Cocartesian (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) 
     (initialized_mixin X) (cocartesian_mixin X).
Definition cartesian_closed (X:polynomial_category) : cartesian_closed :=
  CartesianClosed (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) 
      (cartesian_mixin X) (terminated_mixin X) (ccc_mixin X).
Definition distributive (X:polynomial_category) : distributive :=
  Distributive (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X)
      (terminated_mixin X) (cartesian_mixin X)
      (initialized_mixin X) (cocartesian_mixin X)
      (distributive_mixin X).
End PolynomialCategory.

Notation polynomial_category := PolynomialCategory.polynomial_category.
Notation PolynomialCategory := PolynomialCategory.PolynomialCategory.

Canonical Structure PolynomialCategory.eq.
Canonical Structure PolynomialCategory.comp.
Canonical Structure PolynomialCategory.category.
Canonical Structure PolynomialCategory.terminated.
Canonical Structure PolynomialCategory.cartesian.
Canonical Structure PolynomialCategory.initialized.
Canonical Structure PolynomialCategory.cocartesian.
Canonical Structure PolynomialCategory.cartesian_closed.
Canonical Structure PolynomialCategory.distributive.

Coercion PolynomialCategory.category : polynomial_category >-> category.
Coercion PolynomialCategory.terminated : polynomial_category >-> terminated.
Coercion PolynomialCategory.cartesian : polynomial_category >-> cartesian.
Coercion PolynomialCategory.initialized : polynomial_category >-> initialized.
Coercion PolynomialCategory.cocartesian : polynomial_category >-> cocartesian.
Coercion PolynomialCategory.cartesian_closed : polynomial_category >-> cartesian_closed.
Coercion PolynomialCategory.distributive : polynomial_category >-> distributive.


(**  A concrete category is one where every object has a [Type]
     carrier, and every hom defines a function between the carriers.

     Further, equal homs produce extensionally-equal functions, and
     compostion of homs corresponds to to the composition of functions.
  *)
Record concrete (C:category) :=
  Concrete
  { obmap : ob C -> Type
  ; obeq : forall A:ob C, Eq.mixin_of (obmap A)
  ; hommap : forall {X Y:ob C} (f:hom C X Y),
               obmap X -> obmap Y
  ; hommap_eq : forall (A B:ob C) (f g:hom C A B) (x y:obmap A),
       f ≈ g -> Eq.eq _ (obeq A) x y -> Eq.eq _ (obeq B) (hommap f x) (hommap g y)
  ; hommap_axiom : forall 
    {X Y Z:ob C} 
     (g:hom C Y Z) (f:hom C X Y) (x:obmap X),
       Eq.eq _ (obeq Z) (hommap (g ∘ f) x) (hommap g (hommap f x))
  }.

Notation "f # x" := (hommap _ _ f x) 
  : category_hom_scope.

Canonical Structure CONCRETE_EQ (CAT:category) (CC:concrete CAT) (A:ob CAT) :=
  Eq.Pack (obmap CAT CC A) (obeq CAT CC A).
  
Add Parametric Morphism (C:category) (CC:concrete C) (A B:ob C) :
  (@hommap C CC A B)
    with signature (eq_op (CAT_EQ C A B)) ==>
                   (eq_op (CONCRETE_EQ _ CC A)) ==>
                   (eq_op (CONCRETE_EQ _ CC B))
   as apply_morphism.
Proof.
  intros; apply hommap_eq; auto.
Qed.  


Module Functor.
Section functor.  
  Variable C D:category.

  (** NOTE!! 
      The functor axioms are written in a very specific way that differs
      slightly from the usual presentation.
      This is done so that the definition of functor composition
      is associative up to convertability, even for the axiom proofs!

      In general, it is extremely convenient if we are able to work
      effectively with functors up to convertability, so we go out of
      our way to make the laws we want regarding functors to work up
      to convertability.  Then the prover figures them all out in the
      right places.  This is very good, because the alternative involves
      adding (in various unplesant places) explicit transformations witnessing,
      e.g., the assocativity of functor composition: horrible, horrible, horrible!

      The general pattern is: write the axioms so they always work in a sort
      of continuation-passing form, and define functors so that their axiom
      proofs are transparent.  Then beta and eta conversion are sufficent
      to show the convertability of various nestings of functor compositions.
  *)
  Structure functor :=
    Functor
    { ob_map : ob C -> ob D
    ; hom_map : forall A B,  A → B -> (ob_map A) → (ob_map B)
    ; ident : forall A (f:A → A), f ≈ id(A) -> hom_map A A f ≈ id(ob_map A)
    ; compose : forall A B C (f:B → C) (g:A → B) (h:A → C),
                       h ≈ f ∘ g -> hom_map A C h ≈ hom_map B C f ∘ hom_map A B g
    ; respects : forall A B f g, f ≈ g -> hom_map A B f ≈ hom_map A B g
    }.
End functor.
End Functor.
Arguments Functor.ob_map [C] [D] f X.
Arguments Functor.hom_map [C] [D] f A B f0.
Arguments Functor.Functor C D _ _ _ _ _.
Arguments Functor.functor C D.
Arguments Functor.ident [C] [D] f A f0 _.
Arguments Functor.compose [C] [D] f A B C0 f0 g h _.
Arguments Functor.respects [C] [D] f A B f0 g _.

Notation functor := Functor.functor.
Notation Functor := Functor.Functor.

(**  The '·' symbol is used to indicate the action of a functor on a hom.  Thus, if
     [f : A → B] is a hom in category [C] then [F·f : F A → F B] is a hom in category [D].
  *)
Notation "F · f" := (Functor.hom_map F _ _ f) : category_hom_scope.
Coercion Functor.ob_map : functor >-> Funclass.

Section functor_compose.
  Variable C D E:category.

  (** NOTE! these proof obligations are given explicitly.
      This means that composition with the identity is convertabile
      to forgetting the composition, provided that the thing being
      composed with is a structure object (that is, Coq can convert it
      to the application of the record constructor to some fields).
    *)
  Definition FunctorIdent : functor C C :=
  Functor C C
    (fun X => X)
    (fun A B f => f)
    (fun A f H => H)
    (fun A B C f g h H => H)
    (fun A B f g H => H).

  (** NOTE! the following axioms are given explicitly.
      This is to make sure that functor composition is associative up
      to convertability.
    *)
  Definition FunctorCompose (F:functor D E) (G:functor C D) : functor C E :=
  Functor C E
    (fun X => Functor.ob_map F (Functor.ob_map G X))
    (fun A B f =>
      Functor.hom_map F (Functor.ob_map G A) (Functor.ob_map G B)
        (Functor.hom_map G A B f))
    (fun A f H => 
      Functor.ident _ _ _
        (Functor.ident _ _ _ H))
    (fun A B C f g h H =>
      Functor.compose _ _ _ _ _ _ _
        (Functor.compose _ _ _ _ _ _ _ H))
    (fun A B f g H =>
      Functor.respects _ _ _ _ _
        (Functor.respects _ _ _ _ _ H)).

End functor_compose.

Add Parametric Morphism (C D:category) (F:functor C D) (A B:ob C) :
  (@Functor.hom_map C D F A B)
  with signature (eq_op (CAT_EQ C A B)) ==> 
                 (eq_op (CAT_EQ D (Functor.ob_map F A) (Functor.ob_map F B)))
  as functor_morphism.
Proof.
  intros. apply Functor.respects. trivial.
Qed.

Canonical Structure FuncComp :=
  Comp.Pack _ functor
    (Comp.Mixin _ functor
      (fun X => FunctorIdent X)
      (fun X Y Z => FunctorCompose X Y Z)).

Definition repack (C D:category) (X:functor C D) : functor C D :=
  Functor C D
    (Functor.ob_map X)
    (Functor.hom_map X)
    (Functor.ident X )
    (Functor.compose X)
    (Functor.respects X).
Arguments repack [C] [D] X.

Lemma repack_equal (C D:category) (X:functor C D) : X = repack X.
Proof.
  destruct X; reflexivity.
Qed.

(**  Here we check to ensure we have achieved functor
     laws up to convertablity.  The following goals
     are all proved by the "reflexivity" tactic, which
     demonstrates that Coq's conversion is sufficent to
     demonstrate the equality.  To get conversion with
     the identity, we need to "repack" the functor variables
     because Coq does _not_ have eta-conversion for records.

     Concrete functor instances should be sufficently transparent
     to make this repacking unnecessary in practice.
  *)
Section test_functor_assocative_convertability.
  Variables C D E F:category.
  Variable G:functor E F.
  Variable H:functor D E.
  Variable I:functor C D.

  Goal (G ∘ (H ∘ I) = (G ∘ H) ∘ I).
  Proof (Logic.eq_refl _).

  Goal (G ∘ id = repack G).
  Proof (Logic.eq_refl _).

  Goal (id ∘ G = repack G).
  Proof (Logic.eq_refl _).

End test_functor_assocative_convertability.


(**  Leibniz equality can be used to define a setoid on any type.
  *)
Program Definition lib_eq (X:Type) : Eq.mixin_of X :=
  Eq.Mixin X (@eq X) _ _ _.


(**  Natural transfomations, defined in the standard way.
  *)
Module NT.
Section nt.
  Variables C D:category.
  Variable F G:functor C D.

  Structure nt := NT
    { transform :> forall A, F A → G A
    ; axiom : forall A B (f:A → B), transform B ∘ F·f ≈ G·f ∘ transform A
    }.
End nt.

Arguments nt [C] [D] F G.
Arguments NT [C] [D] F G transform axiom.
Arguments transform [C] [D] [F] [G] (n)%cat (A)%cat_ob.
Arguments axiom [C] [D] [F] [G] n [A] [B] (f)%cat.

Section nt_compose.
  Variables C D E:category.

  Program Definition ident (F:functor C D) : nt F F :=
    NT F F (fun A => id(F A)) _.
  Next Obligation.
    rewrite (cat_ident2 D).
    rewrite (cat_ident1 D).
    trivial.
  Qed.

  Program Definition compose (F G H:functor C D) (s:nt G H) (t:nt F G) : nt F H :=
    NT F H (fun A => s A ∘ t A) _.
  Next Obligation.
    rewrite <- (cat_assoc D _ _ _ _ (s B) (t B) (F·f)).
    rewrite (axiom t).
    rewrite (cat_assoc D _ _ _ _ (s B) (G·f) (t A)).
    rewrite (axiom s).
    rewrite <- (cat_assoc D).
    trivial.
  Qed.

  (**  There are two possible ways to combine a natural transformation
       with the action of a functor to get another natural transformation,
       depending on which side you wish to compose the functor.
    *)
  Program Definition stacknt
    (F:functor D E) (G H:functor C D)
    (n:nt G H) : nt (F ∘ G) (F ∘ H) :=
    NT _ _ (fun A => F·(n A)) _.
  Next Obligation.
    rewrite <- (Functor.compose F). 2: reflexivity.
    rewrite axiom.
    rewrite (Functor.compose F). 2: reflexivity.
    trivial.
  Qed.

  Program Definition pushnt
    (G H:functor D E)
    (n:nt G H) (F:functor C D)
    : nt (G ∘ F) (H ∘ F) :=
    NT _ _ (fun A => n (F A)) (fun A B f => NT.axiom n (F·f)).
End nt_compose.

Section NT_mixins.
  Variables C D:category.

  Program Definition NTEQ_mixin
    (G H:functor C D) :=
      (Eq.Mixin _ (fun s t:nt G H => forall A, s A ≈ t A) _ _ _).
  Next Obligation.
    eauto.
  Qed.

  Definition NTComp_mixin :=
    (Comp.Mixin (functor C D) (@nt C D)
      (ident C D) (compose C D)).
End NT_mixins.
End NT.

Coercion NT.transform : NT.nt >-> Funclass.
Notation "F ▹ nt" := (NT.stacknt _ _ _ F _ _ nt)
  : category_hom_scope.
Notation "nt ◃ F" := (NT.pushnt _ _ _ _ _ nt F)
  : category_hom_scope.
Notation nt := NT.nt.
Notation NT := NT.NT.

Canonical Structure NTEQ (C D:category) G H :=
  Eq.Pack (nt G H) (NT.NTEQ_mixin C D G H).

Canonical Structure NTComp (C D:category) :=
  Comp.Pack (functor C D) (@NT.nt C D) (NT.NTComp_mixin C D).


(**  [FUNC C D] is the functor category from [C] to [D],
     whose objects are the functors from [C] to [D] and whose
     morphisms are natural transformations.
  *)
Program Definition FUNC
  (C D:category) : category :=
  Category (functor C D) (@NT.nt C D)
           (NT.NTEQ_mixin C D)
           (NT.NTComp_mixin C D) _.
Next Obligation.
  intros. constructor.
  intros. hnf. intro. apply cat_ident1.
  intros. hnf. intro. apply cat_ident2.
  intros. hnf. intro. apply cat_assoc.
  intros. hnf. intro. apply cat_respects.
  apply H. apply H0.
Qed.

(* Would these do anything worthwhile ?
Canonical Structure FUNC_COMP C D := CAT_COMP _ _ (FUNC C D).
Canonical Structure FUNC_EQ C D := CAT_EQ _ _ (FUNC C D).
*)
 
(**  Here we define pullbacks in the direct style.
  *)
Module Pullback.
Section pullback.
  Variable C:category.

  Definition commuting_square (X Y Z W:ob C) 
    (f:X → Z) (g:Y → Z)
    (f':W → Y) (g': W → X) :=
      g ∘ f' ≈ f ∘ g'.

  Record square  (X Y Z W:ob C) 
    (f:X → Z) (g:Y → Z)
    (f':W → Y) (g': W → X) :=
    Square
    { commute : commuting_square X Y Z W f g f' g'
    ; map : forall Q p q,
           commuting_square X Y Z Q f g p q ->
           Q → W
    ; axiom1 : forall Q p q H,
           g' ∘ map Q p q H ≈ q
    ; axiom2 : forall Q p q H,
           f' ∘ map Q p q H ≈ p
    ; uniq : forall Q p q H k,
           f ∘ g' ∘ k ≈ f ∘ q -> k ≈ map Q p q H
    }.

  Record pullback (X Y Z:ob C) (f:X → Z) (g:Y → Z) :=
    Pullback
    { pb_ob : ob C
    ; pb_f : pb_ob → Y
    ; pb_g : pb_ob → X
    ; is_pullback : square X Y Z pb_ob f g pb_f pb_g
    }.
End pullback.

Arguments commuting_square [C] [X] [Y] [Z] [W] f g f' g'.
Arguments square [C] [X] [Y] [Z] [W] f g f' g'.
Arguments Square [C] [X] [Y] [Z] [W] [f] [g] [f'] [g'] _ _ _ _ _.
Arguments pullback [C] [X] [Y] [Z] f g.
Arguments Pullback [C] [X] [Y] [Z] [f] [g] _ _ _ _.
Arguments commute [C] [X] [Y] [Z] [W] [f] [g] [f'] [g'] _.
Arguments map [C] [X] [Y] [Z] [W] [f] [g] [f'] [g'] _ [Q] _ _ _.
Arguments axiom1 [C] [X] [Y] [Z] [W] [f] [g] [f'] [g'] _ _ _ _ _.
Arguments axiom2 [C] [X] [Y] [Z] [W] [f] [g] [f'] [g'] _ _ _ _ _.
Arguments uniq [C] [X] [Y] [Z] [W] [f] [g] [f'] [g'] _ _ _ _ _ _ _.
Arguments pb_ob [C] [X] [Y] [Z] [f] [g] _.
Arguments pb_f [C] [X] [Y] [Z] [f] [g] _.
Arguments pb_g [C] [X] [Y] [Z] [f] [g] _.
Arguments is_pullback [C] [X] [Y] [Z] [f] [g] _.

Section pullback_lemma.
  Variable C:category.

  (**  The pullback lemma proved here is that, given objects and
       morphisms as in the below diagram; if both of the inner
       diagrams are pullbacks then the outer diagram is a pullback.

<<
        f1 
     R ----> S
     |       |
  g1 |       | h1
     v  f2   v
     W ----> Y
     |       |
  g2 |       | h2
     V  f3   v
     X ----> Z
>>
  *)

  Variables X Y Z W R S:ob C.
  Variable f1:R → S.
  Variable f2:W → Y.
  Variable f3:X → Z.
  Variable g1:R → W.
  Variable g2:W → X.
  Variable h1:S → Y.
  Variable h2:Y → Z.

  Section pullback_lemma1.
    Variable PB1: Pullback.square f2 h1 f1 g1.
    Variable PB2: Pullback.square f3 h2 f2 g2.

    Section pb_map.
    Variable Q:ob C.
    Variable p:Q → S.
    Variable q:Q → X.
    Variable H:commuting_square f3 (h2 ∘ h1) p q.

    Lemma pb_lemma1_comm : commuting_square f3 h2 (h1 ∘ p) q.
    Proof.
      red. red in H.
      rewrite <- H.
      apply cat_assoc.
    Qed.

    Definition pullback_lemma1_map1 : Q → W :=
      Pullback.map PB2 (h1 ∘ p) q pb_lemma1_comm.

    Program Definition pullback_lemma_map2 : Q → R :=
      Pullback.map PB1 p pullback_lemma1_map1 _.
    Next Obligation.
      red. red in H.
      generalize (axiom2 PB2 _ _ _ pb_lemma1_comm).  intro.
      auto.
    Qed.      
    End pb_map.

    Program Definition pullback_lemma1 : square f3 (h2 ∘ h1) f1 (g2 ∘ g1) :=
      Square _ (fun Q p q H => pullback_lemma_map2 Q p q H) _ _ _ .
    Next Obligation.
      red.
      generalize (commute PB1). generalize (commute PB2).
      simpl; intros.
      red in H; red in H0.
      etransitivity.
      - symmetry. apply cat_assoc.
      - rewrite H0.
        etransitivity. apply cat_assoc.
        rewrite H.
        symmetry. apply cat_assoc.
    Qed.      
    Next Obligation.
      unfold pullback_lemma_map2.
      etransitivity.
      - symmetry. apply cat_assoc.
      - generalize (axiom1 PB1 _ p _ (pullback_lemma_map2_obligation_1 Q p q H)).
        intros. rewrite H0.
        apply (axiom1 PB2).
    Qed.
    Next Obligation.
      apply (axiom2 PB1 _ p _ (pullback_lemma_map2_obligation_1 Q p q H)).
    Qed.
    Next Obligation.
      assert (g1 ∘ k ≈ pullback_lemma1_map1 Q p q H).
      { apply (uniq PB2).
        rewrite <- H0.
        rewrite <- (cat_assoc _ _ _ _ _ f3 g2 _).
        rewrite <- (cat_assoc _ _ _ _ _ f3 (g2 ∘ g1) _).
        apply cat_respects; auto.
        apply cat_assoc.
      }
      apply (uniq PB1).
      rewrite <- (cat_assoc _ _ _ _ _ f2 g1 _).
      rewrite H1. auto.
    Qed.      
  End pullback_lemma1.
End pullback_lemma.

End Pullback.

Notation pullback := Pullback.pullback.
Notation Pullback := Pullback.Pullback.


(**  Here we define adjunction using the unit/counit definition.
  *)
Module Adjunction.
Section adjunction.
  Variable C D:category.
  Variable L:functor D C.
  Variable R:functor C D.

  Record adjunction :=
    Adjunction
    { unit   : nt id(D) (R ∘ L)
    ; counit : nt (L ∘ R) id(C)
    ; adjoint_axiom1 : counit◃L ∘ L▹unit ≈ id
    ; adjoint_axiom2 : R▹counit ∘ unit◃R ≈ id
    }.
End adjunction.

Arguments adjunction [C] [D] L R.
Arguments Adjunction [C] [D] L R _ _ _ _.
Arguments unit [C] [D] [L] [R] a.
Arguments counit [C] [D] [L] [R] a.
Arguments adjoint_axiom1 [C] [D] [L] [R] a _.
Arguments adjoint_axiom2 [C] [D] [L] [R] a _.
End Adjunction.

Notation Adjunction := Adjunction.Adjunction.
Notation adjunction := Adjunction.adjunction.


(**  Here we define the category of cones, the morphisms of which
     are homs in the original category that commute with the
     spokes of the cones.
  *)
Module Cone.
Section cone.
  Variable C:category.

  Variable J:category.
  Definition diagram := functor J C.
  Variable F:diagram.

  Record cone :=
    Cone
    { point : ob C
    ; spoke : forall j, point → (F j) 
    ; axiom : forall j j' (h:j → j'), spoke j' ≈ F·h ∘ spoke j 
    }.
  
  Record cone_hom (M N:cone) :=
    Cone_hom
    { hom_map :> point M → point N
    ; hom_axiom : forall j,
         spoke M j ≈ spoke N j ∘ hom_map
    }.
  Global Arguments hom_map [M] [N] c.
  Global Arguments hom_axiom [M] [N] c j.

  Program Definition cone_ident (M:cone) :=
    Cone_hom M M (id) _.
  Next Obligation. 
    rewrite (cat_ident1 C _ _ (spoke M j)). reflexivity.
  Qed.

  Program Definition cone_compose (M N O:cone)
    (f:cone_hom N O) (g:cone_hom M N) : cone_hom M O :=
    Cone_hom M O (hom_map f ∘ hom_map g) _.
  Next Obligation.
    intros.
    rewrite (hom_axiom g).
    rewrite (hom_axiom f).
    symmetry; apply cat_assoc.
  Qed.    

  Program Definition CONE : category :=
    Category cone cone_hom
      (fun A B => Eq.Mixin _ (fun f g => hom_map f ≈ hom_map g) _ _ _)
      (Comp.Mixin _ _ cone_ident cone_compose)
      _.
  Next Obligation.      
    eauto.
  Qed.
  Next Obligation.
    constructor.
    intros. apply cat_ident1.
    intros. apply cat_ident2.
    intros. apply cat_assoc.
    intros. apply cat_respects; auto.
  Qed.
End cone.
End Cone.

(**  Here we define algebras of an endofunctor, and we define
     initial algebras directly.  We'll be interested in
     initial algebras when it comes time to define recursive domains.
  *)
Module Alg.
Section alg.
  Variable C:category.
  Variable F:functor C C.

  Record alg :=
  Alg
  { carrier :> ob C
  ; iota : (F carrier) → carrier
  }.

  Record alg_hom (M N:alg) :=
  Alg_hom
  { hom_map : carrier M → carrier N
  ; hom_axiom : hom_map ∘ iota M ≈ iota N ∘ F·hom_map
  }.

  Program Definition ident (M:alg) : alg_hom M M :=
    Alg_hom M M (id) _.
  Next Obligation.
    intros.
    rewrite (cat_ident2 _ _ _ (iota M)).
    rewrite (Functor.ident F); trivial.
    rewrite (cat_ident1 _ _ _ (iota M)).
    trivial.
  Qed.

  Program Definition compose (M N O:alg)
    (f:alg_hom N O) (g:alg_hom M N) : alg_hom M O :=
    Alg_hom M O (hom_map _ _ f ∘ hom_map _ _ g) _.
  Next Obligation.
    intros.
    rewrite <- (cat_assoc _ _ _ _ _ (hom_map N O f)).
    rewrite (hom_axiom _ _ g).
    rewrite (cat_assoc _ _ _ _ _ (hom_map N O f)).
    rewrite (hom_axiom _ _ f).
    rewrite <- (cat_assoc _ _ _ _ _ (iota O)).
    rewrite <- (Functor.compose F); reflexivity.
  Qed.

  Record initial_alg :=
  Initial_alg
  { init :> alg
  ; cata : forall M:alg, alg_hom init M
  ; cata_axiom : forall (M:alg) (h:alg_hom init M), 
       hom_map _ _ h ≈ hom_map _ _ (cata M)
  }.

  Lemma cata_axiom' I :
    forall (M:alg) (h:carrier (init I) → carrier M),
      (h ∘ iota (init I) ≈ iota  M ∘ F·h) ->
      h ≈ hom_map _ _ (cata I M).
  Proof.
    intros.
    apply (cata_axiom I M (Alg_hom _ _ h H)).
  Qed.

  Definition lift_alg (A:alg) :=
    Alg (F A) (F·iota A).

  Definition out (I:initial_alg) :=
    hom_map _ _ (cata I (lift_alg I)).

  Lemma in_out : forall (I:initial_alg),
    iota I ∘ out I ≈ id.
  Proof.
    intros.
    transitivity (hom_map _ _ (cata I I)).
    - apply cata_axiom'.
      rewrite <- (cat_assoc _ _ _ _ _ (iota I)).
      apply cat_respects; auto.
      rewrite (hom_axiom _ _ (cata I (lift_alg I))).
      simpl.
      symmetry. apply Functor.compose. auto.

    - symmetry. apply cata_axiom'.
      rewrite (cat_ident2 _ _ _ (iota I)).
      rewrite (Functor.ident F); auto.
      rewrite (cat_ident1 _ _ _ (iota I)).
      auto.
  Qed.

  Lemma out_in : forall (I:initial_alg),
    out I ∘ iota I ≈ id.
  Proof.
    intros.
    transitivity (F·(hom_map _ _ (cata I I))).
    - unfold out.
      rewrite (hom_axiom).
      simpl.
      symmetry.
      apply Functor.compose.
      rewrite in_out.
      symmetry.
      apply cata_axiom'.
      rewrite (cat_ident2 _ _ _ (iota I)).
      rewrite Functor.ident.
      rewrite (cat_ident1 _ _ _ (iota I)).
      reflexivity. reflexivity.
    - apply Functor.ident.
      symmetry.
      apply cata_axiom'.
      rewrite (cat_ident2 _ _ _ (iota I)).
      rewrite Functor.ident.
      rewrite (cat_ident1 _ _ _ (iota I)).
      reflexivity. reflexivity.
  Qed.    

  Lemma initial_inj_epic : forall (I:initial_alg) B (g h: I → B),
    g ∘ iota I ≈ h ∘ iota I ->
    g ≈ h.
  Proof.
    intros.
    cut (g ∘ id ≈ h ∘ id ).
    { rewrite (cat_ident1 _ _ _ g).
      rewrite (cat_ident1 _ _ _ h).
      auto.
    }
    rewrite <- (in_out I).
    rewrite (cat_assoc _ _ _ _ _ g).
    rewrite H.
    rewrite (cat_assoc _ _ _ _ _ h).
    trivial.
  Qed.

End alg.
Arguments carrier [C] [F] a.
Arguments iota [C] [F] a.
Arguments alg_hom [C] [F] M N.
Arguments hom_map [C] [F] [M] [N] a.
Arguments hom_axiom [C] [F] [M] [N] a.
Arguments ident [C] [F] M.
Arguments compose [C] [F] [M] [N] [O] f g.
Arguments Alg [C] [F] carrier iota.
Arguments Alg_hom [C] [F] [M] [N] hom_map hom_axiom.

Arguments init [C] [F] i.
Arguments cata [C] [F] i M.
Arguments cata_axiom [C] [F] i M h.
Arguments Initial_alg [C] [F] init cata cata_axiom.

Program Definition ALG C (F:functor C C) : category :=
    Category (alg C F) (@alg_hom C F)
      (fun A B => Eq.Mixin _ (fun f g => Alg.hom_map f ≈ Alg.hom_map g) _ _ _)
      (Comp.Mixin _ _ (@ident _ _) (@compose _ _)) 
      _.
Next Obligation.
  eauto.
Qed.
Next Obligation.
  constructor.
  - intros. apply cat_ident1.
  - intros. apply cat_ident2.
  - intros. apply cat_assoc.
  - intros. apply cat_respects; auto.
Qed.
Arguments ALG [C] F.

Section forget.
  Variable (C:category).
  Variable (F:functor C C).

  Program Definition forget : functor (ALG F) C :=
    Functor (ALG F) C (@carrier C F) (@hom_map C F) _ _ _.
End forget.
Arguments forget [C] F.

Definition free C (F:functor C C) (FREE:functor C (ALG F)) :=
  adjunction FREE (Alg.forget F).
Arguments free [C] F FREE.

End Alg.

Coercion Alg.carrier : Alg.alg >-> ob.
Coercion Alg.init : Alg.initial_alg >-> Alg.alg.
Coercion Alg.hom_map : Alg.alg_hom >-> hom.
Notation ALG := Alg.ALG.
Notation Alg := Alg.Alg.
Notation alg := Alg.alg.

Canonical Structure Alg.ALG.


(**  The product category.
  *)
Module PROD.
Section product_category.
  Variables C D:category.

  Record prod_ob :=
    Ob
    { obl : ob C
    ; obr : ob D
    }.

  Record prod_hom (X Y:prod_ob) :=
    Hom
    { homl : obl X → obl Y
    ; homr : obr X → obr Y
    }.
  Arguments homl [X] [Y] p.
  Arguments homr [X] [Y] p.

  Definition prod_ident (X:prod_ob) : prod_hom X X :=
    Hom X X id(obl X) id(obr X).

  Definition prod_compose (X Y Z:prod_ob)
    (f:prod_hom Y Z) (g:prod_hom X Y) : prod_hom X Z :=
    Hom X Z (homl f ∘ homl g) (homr f ∘ homr g).

  Definition comp_mixin : Comp.mixin_of prod_ob prod_hom :=
    Comp.Mixin prod_ob prod_hom prod_ident prod_compose.

  Canonical Structure hom_comp : Comp.type :=
    Comp.Pack prod_ob prod_hom comp_mixin.

  Definition hom_equiv (X Y:prod_ob) (f g:prod_hom X Y) :=
    homl f ≈ homl g /\ homr f ≈ homr g.

  Program Definition hom_eq_mixin X Y : Eq.mixin_of (prod_hom X Y) :=
    Eq.Mixin (prod_hom X Y) (hom_equiv X Y) _ _ _.
  Next Obligation.
    red. split; auto.
  Qed.
  Next Obligation.
    destruct H.
    red. split; auto.
  Qed.
  Next Obligation.
    destruct H. destruct H0.
    red. split; eauto.
  Qed.

  Canonical Structure hom_eq X Y : Eq.type :=
    Eq.Pack (prod_hom X Y) (hom_eq_mixin X Y).

  Lemma prod_cat_axioms :
    Category.axioms prod_ob prod_hom hom_eq_mixin comp_mixin.
  Proof.
    constructor.

    - simpl; intros. split; simpl; apply cat_ident1.
    - simpl; intros. split; simpl; apply cat_ident2.
    - simpl; intros. split; simpl; apply cat_assoc.
    - simpl; intros. destruct H; destruct H0.
      split; simpl; apply cat_respects; auto.
  Qed.    

  Canonical Structure PROD := 
    Category prod_ob prod_hom hom_eq_mixin comp_mixin prod_cat_axioms.
End product_category.
End PROD.

Notation PROD := PROD.PROD.
Canonical Structure PROD.
Canonical Structure PROD.hom_eq.
Canonical Structure PROD.hom_comp.

Notation obl := PROD.obl.
Notation obr := PROD.obr.
Notation homl := PROD.homl.
Notation homr := PROD.homr.
Arguments obl [C] [D] _.
Arguments obr [C] [D] _.
Arguments homl [C] [D] [X] [Y] _.
Arguments homr [C] [D] [X] [Y] _.

Section pairF.
  Variables C D E:category.
  Variable F:functor C D.
  Variable G:functor C E.

  Program Definition pairF : functor C (PROD D E) :=
    Functor C (PROD D E)
      (fun X => PROD.Ob D E (F X) (G X))
      (fun X Y f => PROD.Hom _ _ _ _ (F·f) (G·f))
      _ _ _.
  Next Obligation.
    simpl; intros. split; simpl.
    apply Functor.ident; auto.
    apply Functor.ident; auto.
  Qed.
  Next Obligation.
    simpl; intros. split; simpl.
    apply Functor.compose; auto.
    apply Functor.compose; auto.
  Qed.
  Next Obligation.
    simpl; intros. split; simpl.
    apply Functor.respects; auto.
    apply Functor.respects; auto.
  Qed.
End pairF.
Arguments pairF [C D E] _ _.

Section projF.
  Variables C D:category.
  
  Program Definition fstF : functor (PROD C D) C :=
    Functor (PROD C D) C
      (fun X => obl X)
      (fun X Y f => homl f)
      _ _ _.
  Next Obligation.
    intros. destruct H; auto.
  Qed.
  Next Obligation.
    intros. destruct H; auto.
  Qed.
  Next Obligation.
    intros. destruct H; auto.
  Qed.

  Program Definition sndF : functor (PROD C D) D :=
    Functor (PROD C D) D
      (fun X => obr X)
      (fun X Y f => homr f)
      _ _ _.
  Next Obligation.
    intros. destruct H; auto.
  Qed.
  Next Obligation.
    intros. destruct H; auto.
  Qed.
  Next Obligation.
    intros. destruct H; auto.
  Qed.
End projF.


(**  The category with a single object and a single morphism.
  *)
Program Definition ONE : category :=
  Category
      unit (fun _ _ => unit)
      (fun A B => Eq.Mixin _ (fun x y => True) _ _ _)
      (Comp.Mixin _ _ (fun _ => tt) (fun _ _ _ _ _ => tt))
      _.
Solve Obligations of ONE with auto.
Next Obligation.
  constructor.
  intros. hnf. auto.
  intros. hnf. auto.
  intros. hnf. auto.
  intros. hnf. auto.
Qed.


(**  The constant functor.
  *)
Program Definition fconst (C D:category) (A:ob D) : functor C D :=
  Functor C D (fun _ => A) (fun _ _ _ => id(A)) _ _ _.
Next Obligation.
  intros. apply eq_symm. apply cat_ident1.
Defined.

(** The category of types from a fixed universe, with all type-theoretic
    functions up to Leibniz equality.  This works axiom-free in recent Coq because
    we have eta-conversion.
 *)
Module TYPE.
  Definition tob := Type.
  Definition thom (A B:tob) := A -> B.

  Definition ident A 
    := fun x:A => x.

  Definition compose (A B C:tob) (f:B -> C) (g:A -> B)
    := fun x:A => f (g x).

  Program Definition TYPE : category :=
    Category tob thom
        (fun A B => (lib_eq (thom A B))) 
        (Comp.Mixin _ _ ident compose)
        _.
  Next Obligation.
    constructor.
    
    intros; compute. reflexivity.
    intros; compute. reflexivity.
    intros; compute. reflexivity.
    intros. hnf in *. subst. auto.
  Qed.
End TYPE.

Notation TYPE := TYPE.TYPE.


(**  The category of setoids with equality-respecting functions.
  *)
Module SET.

(** Note: we can't use Eq.type because then a universe inconsitency arises.
    However, the following workaround seems just as good.
 *)
Record ob :=
  Ob 
  { carrier :> Type
  ; mixin : Eq.mixin_of carrier
  }.

(** This lets us treat a set_ob like an Eq.type *)
Canonical Structure set_ob_Eq X := Eq.Pack (carrier X) (mixin X).

Record hom (A B:ob) :=
  Hom
  { hom_map :> A -> B
  ; hom_axiom : forall x y, x ≈ y -> hom_map x ≈ hom_map y
  }.

Program Definition set_hom_eq A B : Eq.mixin_of (hom A B) :=
  Eq.Mixin _ (fun f g => forall x, f x ≈ g x) _ _ _.
Next Obligation.
  eauto.
Qed.

Definition ident (A:ob) : hom A A :=
  Hom A A (fun x => x) (fun x y H => H).

Definition compose (A B C:ob) (f:hom B C) (g:hom A B) : hom A C :=
  Hom A C 
    (fun x => f (g x)) 
    (fun x y H => hom_axiom _ _ f _ _ (hom_axiom _ _ g _ _ H)).

Definition set_hom_comp : Comp.mixin_of ob hom :=
  Comp.Mixin ob hom ident compose.
End SET.

Canonical Structure SET_EQ A B := Eq.Pack _ (SET.set_hom_eq A B).
Canonical Structure SET_COMP := Comp.Pack _ _ SET.set_hom_comp.

Program Definition SET : category :=
  Category SET.ob SET.hom SET.set_hom_eq SET.set_hom_comp _.
Next Obligation.
  constructor.
  - intros. hnf. simpl. intros. apply eq_refl.
  - intros. hnf. simpl. intros. apply eq_refl.
  - intros. hnf. simpl. intros. apply eq_refl.
  - intros. hnf. simpl; intros.
    apply eq_trans with (SET.hom_map _ _ f' (SET.hom_map _ _ g x)).
    + apply H.
    + apply SET.hom_axiom.
      apply H0.
Qed.

Coercion SET.carrier : SET.ob >-> Sortclass.
Coercion SET.hom_map : SET.hom >-> Funclass.
Canonical Structure SET.set_ob_Eq.

Program Definition SET_concrete : concrete SET :=
  Concrete SET
  SET.carrier
  (fun X => SET.mixin X)
  SET.hom_map _ _.
Next Obligation.
  transitivity (f y).
  apply SET.hom_axiom; auto.
  apply H.
Qed.
Next Obligation.
  apply eq_refl.
Qed.

Canonical Structure SET_concrete.

Add Parametric Morphism (A B:ob SET) :
  (@SET.hom_map A B)
    with signature (eq_op (SET_EQ A B)) ==>
                   (eq_op (SET.set_ob_Eq A)) ==>
                   (eq_op (SET.set_ob_Eq B))
     as SET_morphism.
Proof.
  intros.
  transitivity (x y0).
  apply SET.hom_axiom. auto.
  apply H.
Qed.

Definition SET_terminus : ob SET := SET.Ob unit (lib_eq _).
Program Definition SET_terminate (A:ob SET) : A → SET_terminus :=
  SET.Hom A SET_terminus (fun x => tt) _.

Program Definition SET_terminated : terminated :=
  Terminated SET.ob SET.hom SET.set_hom_eq SET.set_hom_comp
     SET_obligation_1
     (Terminated.Mixin SET.ob SET.hom SET.set_hom_eq
       SET_terminus SET_terminate _).
Next Obligation.
  hnf. simpl. intro.
  destruct (f x). auto.
Qed.
Canonical Structure SET_terminated.

Definition elem (X:ob SET) (x:X) : ! → X :=
  SET.Hom !%cat_ob X (fun _ => x) (fun a b H => eq_refl _ _).

(**  We can define the category class structure for the large
     category of small categories.  However! we cannot complete
     the construction due to a universe inconsistency.  If we
     had universe polymorphism we could get the definition we want.
  *)
Program Definition CAT_axioms :=
   Category.Axioms
      category
      functor
      (fun A B => lib_eq (functor A B))
      (Comp.Mixin category functor
        (fun X => FunctorIdent X)
        (fun X Y Z => FunctorCompose X Y Z))
      _ _ _ _.
Next Obligation.
  intros. hnf. destruct f; auto.
Qed.
Next Obligation.
  intros. hnf. destruct f; auto.
Qed.
Next Obligation.
  intros. hnf in *. subst. auto.
Qed.

(** No can do, universe inconsistency:
<<
Definition CAT : category := Category category functor _ _ CAT_axioms.
>>
*)
