Require Import Setoid.

Require Import basics.
Require Import categories.


(** Monoidal category *)

Module Monoidal.
Section Monoidal.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).
  Variable comp:Comp.mixin_of ob hom.
  Variable cat_axioms:Category.axioms ob hom eq comp.
  
  Definition eq' A B := Eq.Pack _ (eq A B).
  Definition comp' := Comp.Pack ob hom comp.
  Definition cat' := Category ob hom eq comp cat_axioms.
  Canonical Structure eq'.
  Canonical Structure comp'.
  Canonical Structure cat'.

  Section axioms.
    Variable tensor : ob -> ob -> ob.
    Variable unit : ob.
    Variable tensor_map : forall (A B C D:ob) (f:A → B) (g:C → D),
      tensor A C → tensor B D.
    Arguments tensor_map [A B C D] f g.

    Variable assoc : forall (A B C:ob), tensor (tensor A B) C ↔ tensor A (tensor B C).
    Variable unitor1 : forall (A:ob), tensor unit A ↔ A.
    Variable unitor2 : forall (A:ob), tensor A unit ↔ A.

    Record axioms :=
      Axioms
      { tensor_map_respects : forall A B C D (f f':A → C) (g g':B → D),
           f ≈ f' -> g ≈ g' -> tensor_map f g ≈ tensor_map f' g'

      ; tensor_map_id : forall (A B:ob),
           tensor_map id(A) id(B) ≈ id(tensor A B)

      ; tensor_map_compose : forall (A A' B B' C C':ob) 
            (f:hom A B) (g:hom A' B') (h:hom B C) (i:hom B' C'),
            tensor_map h i ∘ tensor_map f g ≈ tensor_map (h ∘ f) (i ∘ g)

      ; unitor1_natural : forall (A B:ob) (x:A → B),
           unitor1 B ∘ tensor_map id x ≈ x ∘ unitor1 A

      ; unitor2_natural : forall (A B:ob) (x:A → B),
           unitor2 B ∘ tensor_map x id ≈ x ∘ unitor2 A

      ; assoc_natural : forall (A A' B B' C C':ob) (f:A→A') (g:B → B') (h:C → C'),
           assoc A' B' C' ∘ tensor_map (tensor_map f g) h
           ≈
           tensor_map f (tensor_map g h) ∘ assoc A B C

      ; unitor_triangle : forall (A B:ob),
           tensor_map (unitor2 A) id(B) ≈
           tensor_map id(A) (unitor1 B) ∘ assoc A unit B

      ; assoc_pentagon : forall (A B C D:ob),
            assoc A B (tensor C D) ∘ assoc (tensor A B) C D
            ≈
            tensor_map id(A) (assoc B C D)
            ∘
            assoc A (tensor B C) D
            ∘
            tensor_map (assoc A B C) id(D)
      }.
  End axioms.

  Record mixin_of :=
  Mixin
  { tensor : ob -> ob -> ob
  ; unit : ob
  ; tensor_map : forall (A B C D:ob) (f:hom A B) (g:hom C D),
      hom (tensor A C) (tensor B D)
  ; assoc : forall (A B C:ob), tensor (tensor A B) C ↔ tensor A (tensor B C)
  ; unitor1 : forall (A:ob), tensor unit A ↔ A
  ; unitor2 : forall (A:ob), tensor A unit ↔ A
  ; monoidal_axioms : axioms tensor unit tensor_map assoc unitor1 unitor2
  }.
End Monoidal.

Record monoidal :=
  Monoidal
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq:forall A B:ob, Eq.mixin_of (hom A B)
  ; comp:Comp.mixin_of ob hom
  ; cat_axioms:Category.axioms ob hom eq comp
  ; mixin : mixin_of ob hom eq comp cat_axioms
  }.

Definition category (X:monoidal) :=
  Category (ob X) (hom X) (eq X) (comp X) (cat_axioms X).

End Monoidal.

Notation monoidal := Monoidal.monoidal.
Notation Monoidal := Monoidal.Monoidal.
Canonical Structure Monoidal.category.
Coercion Monoidal.category : monoidal >-> category.

Canonical Structure monoidal_eq (X:monoidal) (A B:ob X) :=
  Eq.Pack (A → B) (Monoidal.eq X A B).

Definition tensor (X:monoidal) : ob X -> ob X -> ob X:=
  Monoidal.tensor _ _ _ _ _ (Monoidal.mixin X).
Definition munit (X:monoidal) : ob X :=
  Monoidal.unit _ _ _ _ _ (Monoidal.mixin X).

Arguments tensor [X] A B.

Notation "A ⊗ B" := (@tensor _ A B) : category_ob_scope.
Notation "1" := (munit _) : category_ob_scope.

Definition tensor_map (X:monoidal) (A B C D:ob X) (f:A → B) (g:C → D) : A⊗C → B⊗D :=
  Monoidal.tensor_map _ _ _ _ _ (Monoidal.mixin X) A B C D f g.

Definition associator (X:monoidal) (A B C:ob X) : (A⊗B)⊗C ↔ A⊗(B⊗C) :=
  Monoidal.assoc _ _ _ _ _ (Monoidal.mixin X) A B C.

Definition unitor1 (X:monoidal) (A:ob X) : 1⊗A ↔ A :=
  Monoidal.unitor1 _ _ _ _ _ (Monoidal.mixin X) A.

Definition unitor2 (X:monoidal) (A:ob X) : A⊗1 ↔ A :=
  Monoidal.unitor2 _ _ _ _ _ (Monoidal.mixin X) A.

Arguments tensor_map [X A B C D] f g.
Arguments associator [X] A B C.
Arguments unitor1 [X] A.
Arguments unitor2 [X] A.


Lemma tensor_map_respects (X:monoidal) : 
  forall (A B C D:ob X) (f f':A → C) (g g':B → D),
    f ≈ f' -> g ≈ g' -> tensor_map f g ≈ tensor_map f' g'.

Proof (@Monoidal.tensor_map_respects _ _ _ _ _ _ _ _ _ _ _
          (@Monoidal.monoidal_axioms _ _ _ _ _ (Monoidal.mixin X))).

Add Parametric Morphism (X:monoidal) (A B C D:ob X) :
  (@tensor_map X A B C D)
  with signature eq_op _ ==> eq_op _ ==> eq_op _
  as tensor_map_morphism.
Proof.
  intros. apply tensor_map_respects; auto.
Qed.

Lemma tensor_map_id (X:monoidal) : forall (A B:ob X),
  tensor_map id(A) id(B) ≈ id(A ⊗ B).

Proof (@Monoidal.tensor_map_id _ _ _ _ _ _ _ _ _ _ _
          (@Monoidal.monoidal_axioms _ _ _ _ _ (Monoidal.mixin X))).

Lemma tensor_map_compose (X:monoidal) : forall (A A' B B' C C':ob X) 
            (f:A → B) (g:A' → B') (h:B → C) (i:B' → C'),
            tensor_map h i ∘ tensor_map f g ≈ tensor_map (h ∘ f) (i ∘ g).

Proof (@Monoidal.tensor_map_compose _ _ _ _ _ _ _ _ _ _ _
          (@Monoidal.monoidal_axioms _ _ _ _ _ (Monoidal.mixin X))).

Lemma unitor1_natural (X:monoidal) : forall (A B:ob X) (x:A → B),
           unitor1 B ∘ tensor_map id x ≈ x ∘ unitor1 A.

Proof (@Monoidal.unitor1_natural _ _ _ _ _ _ _ _ _ _ _
          (@Monoidal.monoidal_axioms _ _ _ _ _ (Monoidal.mixin X))).

Lemma unitor2_natural (X:monoidal) : forall (A B:ob X) (x:A → B),
           unitor2 B ∘ tensor_map x id ≈ x ∘ unitor2 A.

Proof (@Monoidal.unitor2_natural _ _ _ _ _ _ _ _ _ _ _
          (@Monoidal.monoidal_axioms _ _ _ _ _ (Monoidal.mixin X))).

Lemma assoc_natural (X:monoidal) : 
  forall (A A' B B' C C':ob X) (f:A→A') (g:B → B') (h:C → C'),
           associator A' B' C' ∘ tensor_map (tensor_map f g) h
           ≈
           tensor_map f (tensor_map g h) ∘ associator A B C.

Proof (@Monoidal.assoc_natural _ _ _ _ _ _ _ _ _ _ _
          (@Monoidal.monoidal_axioms _ _ _ _ _ (Monoidal.mixin X))).

Lemma unitor_triangle (X:monoidal) : forall (A B:ob X),
           tensor_map (unitor2 A) id(B) ≈
           tensor_map id(A) (unitor1 B) ∘ associator A 1 B.

Proof (@Monoidal.unitor_triangle _ _ _ _ _ _ _ _ _ _ _
          (@Monoidal.monoidal_axioms _ _ _ _ _ (Monoidal.mixin X))).

Lemma assoc_pentagon (X:monoidal) : forall (A B C D:ob X),
            associator A B (C⊗D)
            ∘
            associator (A⊗B) C D
            ≈
            tensor_map id(A) (associator B C D)
            ∘
            associator A (B⊗C) D
            ∘
            tensor_map (associator A B C) id(D).

Proof (@Monoidal.assoc_pentagon _ _ _ _ _ _ _ _ _ _ _
          (@Monoidal.monoidal_axioms _ _ _ _ _ (Monoidal.mixin X))).

Lemma kelly1 (X:monoidal) (A B:ob X) :
  unitor1 (A⊗B) ∘ associator 1 A B ≈ tensor_map (unitor1 A) id(B).
Admitted.

Lemma kelly2 (X:monoidal) (A B:ob X) :
  tensor_map id(A) (unitor2 B) ∘ associator A B 1 ≈ unitor2 (A⊗B).
Admitted.

Lemma kelly3 (X:monoidal) : @unitor1 X 1 ≈ @unitor2 X 1.
Admitted.

Module Enriched.
Section Enriched.
  Variable M:monoidal.

  Notation α := (@associator M _ _ _).
  Notation ρ := (@unitor1 M _).
  Notation λ := (@unitor2 M _).
  Notation "f ⋆ g" := (tensor_map f g)
    (at level 37, left associativity).

  Section axioms.
    Variable Ob:Type.
    Variable Hom:Ob -> Ob -> M.
    Variable compose : forall (A B C:Ob), Hom B C ⊗ Hom A B → Hom A C.
    Variable identity : forall (A:Ob), 1 → Hom A A.

    Record axioms :=
    Axioms
    { compose_assoc : forall (A B C D:Ob),
           compose A B D ∘ (compose B C D ⋆ id(Hom A B))
           ≈
           compose A C D ∘ (id(Hom C D) ⋆ compose A B C) ∘ α

    ; compose_unital1 : forall (A B:Ob),
           ρ ≈ compose A B B ∘ (identity B ⋆ id(Hom A B))

    ; compose_unital2 : forall (A B:Ob),
           λ ≈ compose A A B ∘ (id(Hom A B) ⋆ identity A)
    }.
  End axioms.

  Record enriched :=
  Enriched
  { Ob :> Type
  ; Hom : Ob -> Ob -> M
  ; compose : forall (A B C:Ob), Hom B C ⊗ Hom A B → Hom A C
  ; identity : forall (A:Ob), 1 → Hom A A
  ; enriched_axioms : axioms Ob Hom compose identity
  }.
  Notation comp E := (compose E _ _ _).

  Lemma compose_assoc' (X:enriched) (Z1 Z2:M) (A B C D:Ob X) (f:Z1 → _) (g: Z2 → _) :
    compose X A B D ∘ ((compose X B C D ∘ g) ⋆ f) ≈
    compose X A C D ∘ (id ⋆ compose X A B C) ∘ α ∘ (g ⋆ f).
  Proof.
    transitivity (comp X ∘ (comp X ⋆ id) ∘ (g ⋆ f)).
    rewrite <- (cat_assoc M).
    rewrite (tensor_map_compose M).
    rewrite (cat_ident2 M). auto.
    rewrite (compose_assoc X); auto. apply enriched_axioms.
  Qed.

  Record functor (X Y:enriched) :=
  Functor
  { ob_map :> Ob X -> Ob Y
  ; hom_map : forall (A B:Ob X), Hom X A B → Hom Y (ob_map A) (ob_map B)

  ; respect_compose : forall (A B C:Ob X),
        hom_map A C ∘ comp X ≈ comp Y ∘ (hom_map B C ⋆ hom_map A B)

  ; respect_units : forall (A:Ob X),
        hom_map A A ∘ identity X A ≈ identity Y (ob_map A)
  }.
  Arguments hom_map [X Y] f A B.

  Program Definition FunctorCompose (X Y Z:enriched) (F:functor Y Z) (G:functor X Y) :=
    Functor X Z
      (fun A => F (G A))
      (fun A B => hom_map F (G A) (G B) ∘ hom_map G A B)
      _ _.
  Next Obligation.
    rewrite <- (cat_assoc M).
    rewrite (respect_compose _ _ G).
    rewrite (cat_assoc M).
    rewrite (respect_compose _ _ F).
    rewrite <- (cat_assoc M).
    apply cat_respects. auto.
    apply (tensor_map_compose M).
  Qed.
  Next Obligation.
    rewrite <- (cat_assoc M).
    rewrite respect_units. apply respect_units.
  Qed.

  Program Definition FunctorIdent (X:enriched) :=
    Functor X X
      (fun A => A)
      (fun A B => id(Hom X A B))
      _ _.
  Next Obligation.
    etransitivity.
    apply cat_ident2.
    rewrite tensor_map_id.
    symmetry. apply cat_ident1.
  Qed.
  Next Obligation.
    apply cat_ident2.
  Qed.

  Definition functor_comp :=
    Comp.Mixin enriched functor FunctorIdent FunctorCompose.

  Record nt (X Y:enriched) (F G:functor X Y) :=
  NT
  { transform :> forall A:Ob X, 1 → Hom Y (F A) (G A)
  ; nt_axiom : forall (A B:Ob X),
       comp Y ∘ (hom_map G A B ⋆ transform A) ∘ λ⁻¹
       ≈
       comp Y ∘ (transform B ⋆ hom_map F A B) ∘ ρ⁻¹
  }.

Check unitor1_natural.

  Lemma unitor1_natural' (A B:M) (x:A → B) :
    id ⋆ x ∘ ρ⁻¹ ≈ iso_hom (ρ⁻¹) ∘ x.
  Proof.
    transitivity (iso_hom ρ⁻¹ ∘ (x ∘ ρ) ∘ ρ⁻¹).
    rewrite <- (unitor1_natural M).
    rewrite (cat_assoc M).        
    simpl.
    rewrite (iso_axiom1 ρ). rewrite (cat_ident2 M); auto.
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    simpl.
    rewrite (cat_assoc M).
    transitivity (iso_inv ρ ∘ x ∘ id).
    apply cat_respects. auto.
    apply (iso_axiom2 ρ).    
    apply cat_ident1.    
  Qed.    

  Lemma unitor2_natural' (A B:M) (x:A → B) :
    x ⋆ id ∘ λ⁻¹ ≈ iso_hom (λ⁻¹) ∘ x.
  Admitted.

  Lemma unitor_lemma1 : λ ∘ ρ⁻¹ ≈ id.
  Proof.
    rewrite <- (kelly3 M). apply (iso_axiom2 ρ).
  Qed.    

  Lemma unitor_lemma2 (A:ob M) :
    id ⋆ λ⁻¹ ∘ ρ⁻¹ ≈ associator 1 A 1 ∘ (ρ⁻¹ ⋆ id ∘ λ⁻¹).
  Proof.
    rewrite (unitor2_natural').
    rewrite (unitor1_natural').

    cut (ρ ∘ ρ⁻¹ ∘ λ⁻¹ ≈ ρ ∘ associator 1 A 1 ∘ (λ⁻¹ ∘ ρ⁻¹)).
    intros.
    assert
      (iso_hom ρ⁻¹ ∘ (ρ ∘ ρ⁻¹ ∘ λ⁻¹)
        ≈ iso_hom ρ⁻¹ ∘ (ρ ∘ associator 1 A 1 ∘ (λ⁻¹ ∘ ρ⁻¹))).
    rewrite H. auto.
    rewrite (cat_assoc M) in H0.
    rewrite (cat_assoc M) in H0.
    rewrite (cat_assoc M) in H0.
    rewrite (cat_assoc M) in H0.
    simpl in H0.
    etransitivity.
    etransitivity.
    2: apply H0.
    symmetry.
    etransitivity.
    rewrite <- (cat_assoc M).
    apply cat_respects.
    apply (iso_axiom1 ρ).
    reflexivity.
    apply (cat_ident2 M).
    apply cat_respects; auto.
    etransitivity.
    apply cat_respects.
    apply (iso_axiom1 ρ).
    reflexivity.
    apply cat_ident2.

    rewrite (kelly1 M A 1).
    symmetry.
    etransitivity. apply cat_assoc.
    rewrite unitor2_natural'.
    etransitivity. symmetry. apply cat_assoc.
    etransitivity. apply cat_respects. reflexivity.
    apply iso_axiom2.
    rewrite (cat_ident1 M).
    symmetry.
    etransitivity. apply cat_respects.
    apply iso_axiom2. reflexivity.
    apply cat_ident2.
  Qed.   

  Lemma unitor_lemma3 (A B:M) :
    associator A 1 B ∘ λ⁻¹ ⋆ id ≈ id ⋆ ρ⁻¹.
  Proof.
    cut (id ⋆ ρ ∘ iso_hom (associator A 1 B) ∘ λ⁻¹ ⋆ id
          ≈ id ⋆ ρ ∘ id ⋆ ρ⁻¹).
    intros.
    transitivity
      (id ⋆ ρ⁻¹ ∘ (id ⋆ ρ ∘ associator A 1 B ∘ λ⁻¹ ⋆ id)).
    rewrite (cat_assoc M).
    rewrite (cat_assoc M).
    rewrite (tensor_map_compose M).
    etransitivity.
    symmetry. apply (cat_ident2 M).
    rewrite <- (cat_assoc M).
    apply cat_respects.
    etransitivity.
    symmetry. apply tensor_map_id.
    apply tensor_map_respects.
    symmetry. apply cat_ident1.
    symmetry. apply iso_axiom1.
    auto.
    rewrite H.
    etransitivity.
    apply cat_respects. reflexivity.
    rewrite tensor_map_compose.
    apply tensor_map_respects.
    apply cat_ident1.
    apply iso_axiom2.
    etransitivity.
    apply cat_respects. reflexivity.
    apply tensor_map_id.
    rewrite (cat_ident1 M). auto.

    rewrite <- (unitor_triangle M A B).
    rewrite tensor_map_compose.
    rewrite tensor_map_compose.
    apply tensor_map_respects.
    rewrite (cat_ident1 M).
    apply iso_axiom2.
    rewrite (cat_ident1 M).
    symmetry.
    apply iso_axiom2.
  Qed.

  Program Definition nt_compose (X Y:enriched) (F G H:functor X Y)
    (x:nt X Y G H) (y:nt X Y F G) : nt X Y F H :=

    NT X Y F H (fun A => comp Y ∘ (x A ⋆ y A) ∘ ρ⁻¹) _.
  Next Obligation.
    symmetry.
    rewrite <- (cat_assoc M _ _ _ _ (comp Y) (x B ⋆ y B) (iso_inv ρ)).
    rewrite (compose_assoc' Y).
    transitivity (comp Y ∘ id ⋆ comp Y ∘ α ∘ (x B ⋆ y B) ⋆ hom_map F A B
      ∘ ρ⁻¹ ⋆ id ∘ ρ⁻¹).
    apply cat_respects; auto.
    repeat rewrite <- (cat_assoc M).
    apply cat_respects; auto.
    apply cat_respects; auto.
    apply cat_respects; auto.
    rewrite (tensor_map_compose M).
    apply tensor_map_respects; auto.
    symmetry. apply cat_ident1; auto.
    
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    rewrite (cat_assoc M _ _ _ _ α).
    rewrite (assoc_natural M).

    transitivity (comp Y ∘ x B ⋆ (comp Y ∘ y B ⋆ hom_map F A B ∘ ρ⁻¹) ∘ ρ⁻¹).
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    apply cat_respects; auto.
    rewrite (cat_assoc M).
    rewrite (tensor_map_compose M).
    rewrite (cat_ident2 M).
    transitivity (x B ⋆ (comp Y ∘ y B ⋆ hom_map F A B) ∘ 
                ((id ⋆ ρ⁻¹) ∘ (id ⋆ ρ)) ∘ α ∘ (ρ⁻¹ ⋆ id ∘ ρ⁻¹)).
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    apply cat_respects. auto.
    symmetry.
    rewrite (tensor_map_compose M).
    rewrite (cat_ident2 M).
    etransitivity. apply cat_respects.
    simpl. rewrite (iso_axiom1 ρ).
    apply (tensor_map_id M). reflexivity.
    rewrite (cat_ident2 M). auto.
    rewrite (cat_assoc M).
    rewrite (cat_assoc M).
    rewrite (tensor_map_compose M).
    rewrite (cat_ident1 M).
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    apply cat_respects. auto.
    rewrite (cat_assoc M).
    rewrite <- (unitor_triangle M).
    rewrite (cat_assoc M).
    rewrite (tensor_map_compose M).
    etransitivity. apply cat_respects. 2: reflexivity.
    apply tensor_map_respects. 2: apply cat_ident1.
    instantiate (1:=id). 
    apply unitor_lemma1.

    etransitivity. apply cat_respects.
    apply (tensor_map_id M). reflexivity.
    apply cat_ident2.
    rewrite <- (nt_axiom _ _ _ _ y).
    transitivity
       (comp Y ∘ x B ⋆ (comp Y ∘ hom_map G A B ⋆ y A)
         ∘ id ⋆ λ⁻¹ ∘ ρ⁻¹).
    symmetry.
    rewrite <- (cat_assoc M _ _ _ _ (comp Y)).
    rewrite (tensor_map_compose M).
    rewrite (cat_ident1 M).
    auto.
    transitivity
       (comp Y ∘ x B ⋆ (comp Y ∘ hom_map G A B ⋆ y A) ∘
         α ∘ ρ⁻¹ ⋆ id ∘ λ⁻¹).
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    apply cat_respects. auto.
    apply cat_respects. auto.
    apply unitor_lemma2.
    transitivity
      (comp Y ∘ id ⋆ comp Y ∘ α ∘ (x B ⋆ hom_map G A B ⋆ y A)
        ∘ ρ⁻¹ ⋆ id ∘ λ⁻¹).
    apply cat_respects; auto.
    apply cat_respects; auto.
    symmetry.
    rewrite <- (cat_assoc M).
    rewrite (assoc_natural M _ _ _ _ _ _ (x B)).
    rewrite <- (cat_assoc M).
    rewrite (cat_assoc M _ _ _ _ (id ⋆ comp Y)).
    rewrite (tensor_map_compose M).
    rewrite (cat_ident2 M).
    rewrite (cat_assoc M).
    auto.
    rewrite <- (compose_assoc). 2: apply enriched_axioms.
    apply cat_respects. 2: auto.
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    rewrite (tensor_map_compose M).
    rewrite (tensor_map_compose M).
    rewrite (cat_assoc M).
    rewrite <- (nt_axiom _ _ _ _ x A B).
    rewrite (cat_ident1 M).
    rewrite (cat_ident2 M).
    rewrite <- (cat_assoc M).
    rewrite (compose_assoc' Y).
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    rewrite <- (cat_assoc M).
    apply cat_respects. auto.
    transitivity
      (id ⋆ comp Y ∘ (α ∘ (hom_map H A B ⋆ x A) ⋆ y A) ∘ (λ⁻¹) ⋆ id).
    rewrite <- (cat_assoc M).
    apply cat_respects. auto.
    rewrite <- (cat_assoc M).
    apply cat_respects. auto.
    rewrite (tensor_map_compose M).
    rewrite (cat_ident1 M). auto.
    rewrite (assoc_natural M).
    rewrite (cat_assoc M).
    rewrite (cat_assoc M).
    rewrite (tensor_map_compose M).
    rewrite (cat_ident2 M).
    transitivity
      (hom_map H A B ⋆ (comp Y ∘ x A ⋆ y A) ∘ id ⋆ ρ⁻¹).
    rewrite <- (cat_assoc M).
    apply cat_respects. auto.
    apply unitor_lemma3.

    rewrite (tensor_map_compose M).
    rewrite (cat_ident1 M).
    auto.
  Qed.    

End Enriched.
End Enriched.

Notation enriched := Enriched.enriched.
Notation Enriched := Enriched.Enriched.
