(* Copyright (c) 2014, Robert Dockins *)

Require Import Setoid.

Require Import basics.
Require Import categories.



(** * Bicategories *)

Close Scope category_ob_scope.
Close Scope category_ops_scope.

Delimit Scope bicategory_scope with bicat.
Open Scope bicategory_scope.

Module Bicategory.
Section bicategory.
  Variable ob:Type.
  Variable hom : ob -> ob -> Type.
  Variable hom2 : forall X Y:ob, hom X Y -> hom X Y -> Type.
  
  Variable (eq : forall A B f g, Eq.mixin_of (hom2 A B f g)).
  Variable (comp : forall A B, (Comp.mixin_of (hom A B) (hom2 A B))).
  Variable (cat_axioms: forall A B:ob, 
    Category.axioms (hom A B) (hom2 A B) (eq A B) (comp A B)).

  Variable Ident:forall A:ob, hom A A.
  Variable CompHom : forall (A B C:ob) (f:hom B C) (g:hom A B), hom A C.
  Variable CompHoriz : forall (A B C:ob) (f f':hom B C) (g g':hom A B),
    hom2 B C f f' -> hom2 A B g g' -> hom2 A C (CompHom A B C f g) (CompHom A B C f' g').

  Canonical Structure HOM A B :=
    Category (hom A B) (hom2 A B) (eq A B) (comp A B) (cat_axioms A B).

  Notation "f • g" := (CompHom _ _ _ f g)
    (at level 32, left associativity).
  Notation "'Id'" := (Ident _ : HOM _ _).
  Notation "'Id' ( A )" := (Ident A : HOM A A).
  Notation "x ⋆ y" := (CompHoriz _ _ _ _ _ _ _ x y : @Category.hom (HOM _ _) _ _)
    (at level 37, left associativity).

  Record mixin_of :=
  Mixin
  { unit1 : forall {A B} (f:HOM A B),
        f • Id(A) ↔ f

  ; unit2 : forall {A B} (f:HOM A B),
        Id(B) • f ↔ f

  ; assoc : forall {A B C D} (f:hom C D) (g:hom B C) (h:hom A B),
        (f • g) • h ↔ f • (g • h)

  ; unit1_natural : forall A B (f g:HOM A B) (x:g → f),
        iso_hom (unit1 f) ∘ (x ⋆ id(Id(A))) ≈ x ∘ iso_hom (unit1 g)

  ; unit2_natural : forall A B (f g:HOM A B) (x:g → f),
        iso_hom (unit2 f) ∘ (id(Id(B)) ⋆ x) ≈ x ∘ iso_hom (unit2 g)

  ; assoc_natural : forall A B C D (f f':HOM C D) (g g':HOM B C) (h h':HOM A B)
        (x:f → f') (y:g → g') (z:h → h'),

        iso_hom (assoc f' g' h') ∘ ((x ⋆ y) ⋆ z)
        ≈
        (x ⋆ (y ⋆ z)) ∘ iso_hom (assoc f g h)

  ; unitor_triangle : forall (A B C:ob) (g:HOM B C) (f:HOM A B),
        iso_hom (unit1 g) ⋆ id(f) 
        ≈
        (id(g) ⋆ iso_hom (unit2 f))
        ∘
        iso_hom (assoc g Id f)

  ; associator_pentagon : forall (A B C D E:ob)
        (f:HOM A B) (g:HOM B C) (h:HOM C D) (i:HOM D E),

        iso_hom (assoc i h (g • f))
        ∘
        iso_hom (assoc (i•h) g f)
        ≈
        id(i) ⋆ iso_hom (assoc h g f)
        ∘
        iso_hom (assoc i (h • g) f)
        ∘
        iso_hom (assoc i h g) ⋆ id(f)
  }.
End bicategory.

Record bicategory :=
  Bicategory
  { ob : Type
  ; hom : ob -> ob -> Type
  ; hom2 : forall X Y:ob, hom X Y -> hom X Y -> Type
  ; eq : forall A B f g, Eq.mixin_of (hom2 A B f g)
  ; comp : forall A B, (Comp.mixin_of (hom A B) (hom2 A B))
  ; cat_axioms : forall A B:ob, 
       Category.axioms (hom A B) (hom2 A B) (eq A B) (comp A B)
  ; Ident : forall A:ob, hom A A
  ; CompHom : forall (A B C:ob) (f:hom B C) (g:hom A B), hom A C
  ; CompHoriz : forall (A B C:ob) (f f':hom B C) (g g':hom A B),
       hom2 B C f f' -> hom2 A B g g' -> hom2 A C (CompHom A B C f g) (CompHom A B C f' g')
  ; mixin : mixin_of ob hom hom2 eq comp cat_axioms Ident CompHom CompHoriz
  }.

End Bicategory.

Notation bicategory := Bicategory.bicategory.
Notation Bicategory := Bicategory.Bicategory.
Notation ob := Bicategory.ob.
Notation hom := Bicategory.hom.
Notation hom2 := Bicategory.hom2.
Coercion ob : bicategory >-> Sortclass.

Canonical Structure HOM (C:bicategory) (A B:ob C) :=
  Category (hom C A B) (hom2 C A B) 
           (Bicategory.eq C A B) 
           (Bicategory.comp C A B) 
           (Bicategory.cat_axioms C A B).

Canonical Structure BICAT_EQ (C:bicategory) A B F G 
  := Eq.Pack (hom2 C A B F G) (Bicategory.eq C A B F G).
Canonical Structure BICAT_COMP (C:bicategory) (A B:ob C)
  := Comp.Pack (hom C A B) (hom2 C A B) (Bicategory.comp C A B).

Definition hom1_compose (X:bicategory) (A B C:X) (G:HOM X B C) (F:HOM X A B) : HOM X A C :=
  Bicategory.CompHom X A B C G F.
Definition hom1_ident (X:bicategory) (A:X) : HOM X A A :=
  Bicategory.Ident X A.

Notation "G • F" := (hom1_compose _ _ _ _ G F)
  (at level 32, left associativity).
Notation "A → B" := (Bicategory.hom _ A B) : bicategory_scope.
Notation "F ⇒ G" := (Bicategory.hom2 _ _ _ F G) : bicategory_scope.

Definition comp_horiz (X:bicategory) (A B C:X) (F F':B → C) (G G':A → B) :
  F ⇒ F' -> G ⇒ G' -> F•G ⇒ F'•G'

  := Bicategory.CompHoriz X A B C F F' G G'.   

Notation "'Id'" := (hom1_ident _ _).
Notation "'Id' ( A )" := (hom1_ident _ A) (only parsing).
Notation "x ⋆ y" := (comp_horiz _ _ _ _ _ _ _ _ x y)
    (at level 37, left associativity).

Definition left_whisker (X:bicategory) (A B C:ob X) (g h:B → C) 
  (x:g ⇒ h) (f:A → B) : g•f ⇒ h•f := x ⋆ id(f).
Definition right_whisker (X:bicategory) (A B C:ob X) (f g:A → B)
  (h:B → C) (x:f ⇒ g) : h•f ⇒ h•g := id(h) ⋆ x.
  
Arguments left_whisker [X A B C g h] x f.
Arguments right_whisker [X A B C f g] h x.

Notation "x ◃ f" := (@left_whisker _ _ _ _ _ x f) : bicategory_scope.
Notation "h ▹ x" := (@right_whisker _ _ _ _ _ h x) : bicategory_scope.

Definition bicat_assoc (X:bicategory) :
  forall (A B C D:ob X) (f:HOM X C D) (g:HOM X B C) (h:HOM X A B),
  (f • g) • h ↔ f • (g • h)

  := @Bicategory.assoc _ _ _ _ _ _ _ _ _ (Bicategory.mixin X).
  
Definition bicat_unit1 (X:bicategory) :
  forall (A B:ob X) (f:HOM X A B), f • Id(A) ↔ f

  := @Bicategory.unit1 _ _ _ _ _ _ _ _ _ (Bicategory.mixin X).

Definition bicat_unit2 (X:bicategory) :
  forall (A B:ob X) (f:HOM X A B), Id(B) • f ↔ f

  := @Bicategory.unit2 _ _ _ _ _ _ _ _ _ (Bicategory.mixin X).

Arguments bicat_assoc [X A B C D] f g h.
Arguments bicat_unit1 [X A B] f.
Arguments bicat_unit2 [X A B] f.


Module Pseudofunctor.

Record pseudofunctor (X Y:bicategory) :=
  Pseudofunctor
  { ob_map :> ob X -> ob Y
  ; hom_map : forall {A B:ob X}, functor (HOM X A B) (HOM Y (ob_map A) (ob_map B))

  ; compose : forall {A B C:ob X} (g:B → C) (f:A → B),
                        hom_map g • hom_map f ↔ hom_map (g • f)

  ; ident : forall A:ob X,
                        Id(ob_map A) ↔ hom_map (Id(A))

  ; compose_natural :
         forall (A B C:ob X) (g g':B → C) (f f':A → B) (x:g ⇒ g') (y:f ⇒ f'),
           hom_map·(x ⋆ y) ∘ iso_hom (compose g f)
           ≈ iso_hom (compose g' f') ∘ (hom_map·x ⋆ hom_map·y)

  ; unit1 :
         forall (A:ob X) (f:A → A),
           iso_hom (bicat_unit1 (hom_map f))
           ≈ 
           hom_map·(bicat_unit1 f)
           ∘
           iso_hom (compose f Id(A))
           ∘
           ( id ⋆ iso_hom (ident A) )

  ; unit2 :
         forall (A:ob X) (f:A → A),
           iso_hom (bicat_unit2 (hom_map f))
           ≈ 
           hom_map·(bicat_unit2 f)
           ∘
           iso_hom (compose Id(A) f)
           ∘
           ( iso_hom (ident A) ⋆ id )


  ; assoc :
         forall (A B C D:ob X) (h:HOM X C D) (g:HOM X B C) (f:HOM X A B),
           iso_hom (compose h (g•f))
           ∘
           (id(hom_map h) ⋆ iso_hom (compose g f))
           ∘
           iso_hom (bicat_assoc (hom_map h) (hom_map g) (hom_map f))
           ≈
           hom_map·(bicat_assoc h g f)
           ∘
           iso_hom (compose (h•g) f)
           ∘
           ( iso_hom (compose h g) ⋆ id(hom_map f) )
 }.

End Pseudofunctor.

Notation pseudofunctor := Pseudofunctor.pseudofunctor.
Notation Pseudofunctor := Pseudofunctor.Pseudofunctor.

Notation "F ✧ h" := (Pseudofunctor.hom_map _ _ F h)
  (at level 55, right associativity).
Notation "F ✦ h" := (Pseudofunctor.hom_map _ _ F·h)
  (at level 55, right associativity).

(** * The large bicategory of small categories.
  *)
Section CAT.
  Lemma nt_cat_axioms (X Y:category) :
    Category.axioms (functor X Y) (@nt X Y) (NT.NTEQ_mixin X Y) (NT.NTComp_mixin X Y).
  Proof.  
    constructor.

    intros. intro. simpl. apply cat_ident1.
    intros. intro. simpl. apply cat_ident2.
    intros. intro. simpl. apply cat_assoc.
    intros. intro. simpl. apply cat_respects.
    apply H. apply H0.
  Qed.    

  Program Definition NTCompHoriz (X Y Z:category)
    (F F':functor Y Z) (G G':functor X Y)
    (m:nt F F') (n:nt G G') : nt (F∘G) (F'∘G')
    := NT (F∘G) (F'∘G') (fun A => m (G' A) ∘ F·(n A)) _.
  Next Obligation.
    rewrite <- (cat_assoc Z).
    rewrite <- (Functor.compose F). 2: reflexivity.
    rewrite (NT.axiom n f).
    rewrite (Functor.compose F). 2: reflexivity.
    rewrite (cat_assoc Z).
    rewrite (NT.axiom m (G'·f)).
    symmetry. apply cat_assoc.
  Qed.

  Canonical Structure NTCAT (X Y:category) :=
    Category (functor X Y) (@nt X Y) _ _ (nt_cat_axioms X Y).

  Program Definition nt_unit1 (X Y:category) (f:functor X Y) : f ∘ id ↔ f
    := Isomorphism _ _ _
         (NT (f∘id) f (fun A => id(f A)) _)
         (NT f (f∘id) (fun A => id(f A)) _)
         _ _.
  Next Obligation.
    rewrite (cat_ident2 Y).
    rewrite (cat_ident1 Y).
    auto.
  Qed.
  Next Obligation.
    rewrite (cat_ident2 Y).
    rewrite (cat_ident1 Y).
    auto.
  Qed.
  Next Obligation.
    intro A. simpl. apply cat_ident1.
  Qed.
  Next Obligation.
    intro A. simpl. apply cat_ident1.
  Qed.

  Program Definition nt_unit2 (X Y:category) (f:functor X Y) : id ∘ f ↔ f
    := Isomorphism _ _ _
         (NT (id∘f) f (fun A => id) _)
         (NT f (id∘f) (fun A => id) _)
         _ _.
  Next Obligation.
    rewrite (cat_ident2 Y).
    rewrite (cat_ident1 Y).
    auto.
  Qed.
  Next Obligation.
    rewrite (cat_ident2 Y).
    rewrite (cat_ident1 Y).
    auto.
  Qed.
  Next Obligation.
    intro A. simpl. apply cat_ident1.
  Qed.
  Next Obligation.
    intro A. simpl. apply cat_ident1.
  Qed.

  Program Definition nt_assoc (X Y Z W:category)
    (f:functor Z W) (g:functor Y Z) (h:functor X Y) : (f∘g)∘h ↔ f∘(g∘h)

    := Isomorphism _ _ _
          (NT ((f∘g)∘h) (f∘(g∘h)) (fun A => id) _)
          (NT (f∘(g∘h)) ((f∘g)∘h) (fun A => id) _)
          _ _.
  Next Obligation.
    rewrite (cat_ident2 W).
    rewrite (cat_ident1 W).
    auto.
  Qed.
  Next Obligation.
    rewrite (cat_ident2 W).
    rewrite (cat_ident1 W).
    auto.
  Qed.
  Next Obligation.
    intro A. simpl. apply cat_ident1.
  Qed.
  Next Obligation.
    intro A. simpl. apply cat_ident1.
  Qed.
    
  Program Definition cat_bicategory_mixin :=
    Bicategory.Mixin
      category functor nt _ _ nt_cat_axioms
      FunctorIdent FunctorCompose NTCompHoriz
      nt_unit1 nt_unit2 nt_assoc
      _ _ _ _ _.
  Next Obligation.
    intro. simpl.
    etransitivity.
    apply cat_ident2.
    rewrite Functor.ident. auto. auto.
  Qed.
  Next Obligation.
    intro. simpl.
    etransitivity.
    apply cat_ident2.
    etransitivity.
    apply cat_ident2.
    symmetry. apply cat_ident1.
  Qed.
  Next Obligation.
    intro. simpl.
    etransitivity.
    apply cat_ident2.
    etransitivity.
    symmetry. apply cat_assoc.
    etransitivity.
    2: apply cat_assoc.
    apply cat_respects. auto.
    symmetry.
    etransitivity. apply cat_ident1.
    apply Functor.compose. auto.
  Qed.    
  Next Obligation.
    intro. simpl.
    symmetry. apply cat_ident1.
  Qed.
  Next Obligation.
    intro. simpl.
    rewrite Functor.ident. 2: auto.
    rewrite Functor.ident.
    apply cat_respects.
    symmetry. 
    etransitivity. apply cat_ident1. apply cat_ident1.
    symmetry. apply cat_ident1.
    apply Functor.ident.
    apply Functor.ident.
    auto.
  Qed.
    
  Definition CAT : bicategory :=
    Bicategory 
       category functor nt _ _ nt_cat_axioms
       FunctorIdent FunctorCompose NTCompHoriz
       cat_bicategory_mixin.
End CAT.
Canonical Structure CAT.
