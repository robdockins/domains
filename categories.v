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
Notation "x ∘ y" := (@comp_op _ _ _ _ x y) (at level 40, left associativity).
Notation "'id'" := (@ident_op _ _).
Notation "'id' ( A )" := (@ident_op _ A).


(**  Here we put together the pieces: the setoid structure
     on hom-sets, the composition strucutre, and the category axioms.
  *)
Module Category.
Section category.
  Variable Ob:Type.
  Variable Hom : Ob -> Ob -> Type.
  
  Section category_axioms.
    Variable (EQ:forall A B, Eq.mixin_of (Hom A B)).
    Variable (COMP:@Comp.mixin_of Ob Hom).

    Canonical Structure cat_EQ A B := Eq.Pack _ (EQ A B).
    Canonical Structure cat_COMP := Comp.Pack _ _ COMP.

    Record category_axioms :=
    { ident1 : forall A B (f:Hom A B), f ∘ id(A) ≈ f
    ; ident2 : forall A B (f:Hom A B), id(B) ∘ f ≈ f
    ; assoc : forall A B C D (f:Hom C D) (g:Hom B C) (h:Hom A B), f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
    ; respects : forall A B C (f f':Hom B C) (g g':Hom A B),
           f ≈ f' -> g ≈ g' -> (f ∘ g) ≈ (f' ∘ g')
    }.
  End category_axioms.

  Structure class_of :=
    Class
    { eq : forall A B, Eq.mixin_of (Hom A B)
    ; comp : Comp.mixin_of Ob Hom
    ; axioms : category_axioms eq comp
    }.
End category.
End Category.

Structure category :=
  Category
  { ob : Type
  ; hom : ob -> ob -> Type
  ; cat_class : Category.class_of ob hom
  }.
Notation "A → B" := (hom _ A B) (at level 65).

Canonical Structure CAT_EQ (C:category) A B
  := Eq.Pack _ (Category.eq _ _ (cat_class C) A B).
Canonical Structure CAT_COMP (C:category) 
  := Comp.Pack _ _ (Category.comp _ _ (cat_class C)).


(**  Here we define some easier-to-use versions of the catgory axioms.
  *)
Section category_axioms.
  Variable C:category.

  Definition cat_ident1   := Category.ident1 _ _ _ _ (Category.axioms _ _ (cat_class C)).
  Definition cat_ident2   := Category.ident2 _ _ _ _ (Category.axioms _ _ (cat_class C)).
  Definition cat_assoc    := Category.assoc _ _ _ _ (Category.axioms _ _ (cat_class C)).
  Definition cat_respects := Category.respects _ _ _ _ (Category.axioms _ _ (cat_class C)).
End category_axioms.
Arguments cat_ident1 {C} [A] [B] f.
Arguments cat_ident2 {C} [A] [B] f.
Arguments cat_assoc {C} [A] [B] [C0] [D] f g h.
Arguments cat_respects {C} [A] [B] [C0] [f] [f'] [g] [g'] _ _.


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

Notation "f '#' x" := (hommap _ _ f x) (at level 33, right associativity).

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


(**  A monomorphism is a morphism which cancels on the left.
  *)
Section mono.
  Variable C:category.

  Record monomorphism (A B:ob C) :=
    Monomorphism
    { mono_hom : A → B
    ; mono_axiom : forall X (g h:X → A),
        mono_hom ∘ g ≈ mono_hom ∘ h -> g ≈ h
    }.
End mono.
Arguments mono_hom [C] [A] [B] m.
Arguments mono_axiom [C] [A] [B] m [X] [g] [h] _.

Coercion mono_hom : monomorphism >-> hom.
Notation "A ↣ B" := (monomorphism _ A B) (at level 65).

Program Definition mono_eq (C:category) (A B:ob C) :=
  Eq.Mixin (monomorphism C A B)
     (fun f g => mono_hom f ≈ mono_hom g) _ _ _.
Next Obligation.
  eauto.
Qed.

Program Definition mono_id (C:category) (A:ob C) :=
  Monomorphism C A A (id(A)) _.  
Next Obligation.
  rewrite (cat_ident2 g) in H.
  rewrite (cat_ident2 h) in H.
  auto.
Qed.

Program Definition mono_compose
  (C:category) (X Y Z:ob C) (g:Y ↣ Z) (f:X ↣ Y) :=
  Monomorphism C X Z (mono_hom g ∘ mono_hom f) _.
Next Obligation.
  intros.
  rewrite <- (cat_assoc g f g0) in H.
  rewrite <- (cat_assoc g f h) in H.
  apply mono_axiom in H.
  apply mono_axiom in H.
  auto.
Qed.

Canonical Structure MONO_EQ (C:category) A B
  := Eq.Pack (monomorphism C A B) (mono_eq C A B).
Canonical Structure MONO_COMP (C:category)
  := Comp.Pack (ob C) (monomorphism C)
       (Comp.Mixin _ _ (mono_id C) (mono_compose C)).
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

  Record epimorphism (A B:ob C) :=
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
Notation "A ↠ B" := (epimorphism _ A B) (at level 65).

Program Definition epi_eq (C:category) (A B:ob C) :=
  Eq.Mixin (epimorphism C A B)
     (fun f g => epi_hom f ≈ epi_hom g) _ _ _.
Next Obligation.
  eauto.
Qed.

Program Definition epi_id (C:category) (A:ob C) :=
  Epimorphism C A A (id(A)) _.  
Next Obligation.
  rewrite (cat_ident1 g) in H.
  rewrite (cat_ident1 h) in H.
  auto.
Qed.

Program Definition epi_compose
  (C:category) (X Y Z:ob C) (g:Y ↠ Z) (f:X ↠ Y) :=
  Epimorphism C X Z (epi_hom g ∘ epi_hom f) _.
Next Obligation.
  intros.
  rewrite (cat_assoc g0 g f) in H.
  rewrite (cat_assoc h g f) in H.
  apply epi_axiom in H.
  apply epi_axiom in H.
  auto.
Qed.

Canonical Structure EPI_EQ (C:category) A B
  := Eq.Pack (epimorphism C A B) (epi_eq C A B).
Canonical Structure EPI_COMP (C:category)
  := Comp.Pack (ob C) (epimorphism C)
       (Comp.Mixin _ _ (epi_id C) (epi_compose C)).

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


(**  An isomorphism is a pair of functions that, when comoposed
     in each direction, are equal to the identity.
  *)
Section iso.
  Variable C:category.

  Record isomorphism (A B:ob C) :=
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

Coercion iso_hom : isomorphism >-> hom.
Notation "A ↔ B" := (isomorphism _ A B) (at level 65).

Program Definition iso_eq (C:category) (A B:ob C) :=
  Eq.Mixin (isomorphism C A B)
     (fun f g => iso_hom f ≈ iso_hom g) _ _ _.
Next Obligation.
  eauto.
Qed.

Program Definition iso_id (C:category) (A:ob C) :=
  Isomorphism C A A (id(A)) (id(A)) _ _.  
Next Obligation.
  apply cat_ident1.  
Qed.
Next Obligation.
  apply cat_ident1.  
Qed.

Program Definition iso_compose
  (C:category) (X Y Z:ob C) (g:Y ↔ Z) (f:X ↔ Y) :=
  Isomorphism C X Z (iso_hom g ∘ iso_hom f) (iso_inv f ∘ iso_inv g) _ _.
Next Obligation.
  intros. 
  rewrite <- (cat_assoc (iso_inv f) (iso_inv g) (iso_hom g ∘ iso_hom f)).
  rewrite (cat_assoc (iso_inv g) (iso_hom g) (iso_hom f)).
  rewrite (iso_axiom1 g).
  rewrite (cat_ident2 f).
  rewrite (iso_axiom1 f).
  auto.
Qed.
Next Obligation.
  rewrite <- (cat_assoc (iso_hom g) (iso_hom f) (iso_inv f ∘ iso_inv g)).
  rewrite (cat_assoc (iso_hom f) (iso_inv f) (iso_inv g)).
  rewrite (iso_axiom2 f).
  rewrite (cat_ident2 (iso_inv g)).
  rewrite (iso_axiom2 g).
  auto.
Qed.

Canonical Structure ISO_EQ (C:category) A B
  := Eq.Pack (isomorphism C A B) (iso_eq C A B).
Canonical Structure ISO_COMP (C:category)
  := Comp.Pack (ob C) (isomorphism C)
      (Comp.Mixin _ _ (iso_id C) (iso_compose C)).


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

(**  The '@' symbol is used to indicate the action of a functor on a hom.  Thus, if
     [f : A → B] is a hom in category [C] then [F@f : F A → F B] is a hom in category [D].
  *)
Notation "F '@' f" := (Functor.hom_map F _ _ f) (at level 36, left associativity).
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

Canonical Structure repack (C D:category) (X:functor C D) : functor C D :=
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
    reflexivity.
  Qed.

  Goal (G ∘ id = repack G).
    reflexivity.
  Qed.

  Goal (id ∘ G = repack G).
    reflexivity.
  Qed.
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
    ; axiom : forall A B (f:A → B), transform B ∘ F@f ≈ G@f ∘ transform A
    }.
End nt.

Arguments nt [C] [D] F G.
Arguments NT [C] [D] F G transform axiom.
Arguments transform [C] [D] [F] [G] n A.
Arguments axiom [C] [D] [F] [G] n [A] [B] f.

Section nt_compose.
  Variables C D E:category.

  Program Definition ident (F:functor C D) : nt F F :=
    NT F F (fun A => id(F A)) _.
  Next Obligation.
    rewrite (cat_ident2 (F@f)).
    rewrite (cat_ident1 (F@f)).
    trivial.
  Qed.

  Program Definition compose (F G H:functor C D) (s:nt G H) (t:nt F G) : nt F H :=
    NT F H (fun A => s A ∘ t A) _.
  Next Obligation.
    rewrite <- (cat_assoc (s B) (t B) (F@f)).
    rewrite (axiom t).
    rewrite (cat_assoc (s B) (G@f) (t A)).
    rewrite (axiom s).
    rewrite <- (cat_assoc (H@f)).
    trivial.
  Qed.

  (**  There are two possible ways to combine a natural transformation
       with the action of a functor to get another natural transformation,
       depending on which side you wish to compose the functor.
    *)
  Program Definition stacknt
    (F:functor D E) (G H:functor C D)
    (n:nt G H) : nt (F ∘ G) (F ∘ H) :=
    NT _ _ (fun A => F@(n A)) _.
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
    NT _ _ (fun A => n (F A)) (fun A B f => NT.axiom n (F@f)).
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
Notation "F @@ nt" := (NT.stacknt _ _ _ F _ _ nt) (at level 36).
Notation "nt >> F" := (NT.pushnt _ _ _ _ _ nt F) (at level 36).
Notation nt := NT.nt.
Notation NT := NT.NT.

Canonical Structure NTEQ (C D:category) G H :=
  Eq.Pack _
    (NT.NTEQ_mixin C D G H).

Canonical Structure NTComp (C D:category) :=
  Comp.Pack (functor C D) (@NT.nt C D)
             (NT.NTComp_mixin C D).
  

(**  [FUNC C D] is the functor category from [C] to [D],
     whose objects are the functors from [C] to [D] and whose
     morphisms are natural transformations.
  *)
Program Definition FUNC
  (C D:category) : category :=
  Category
        (functor C D) (@NT.nt C D)
        (Category.Class _ _
          (fun G H => NT.NTEQ_mixin C D G H)
          (NT.NTComp_mixin C D) _).
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
      symmetry. apply cat_assoc.
      rewrite H0.
      etransitivity. apply cat_assoc.
      rewrite H.
      symmetry. apply cat_assoc.
    Qed.      
    Next Obligation.
      unfold pullback_lemma_map2.
      etransitivity.
      symmetry. apply cat_assoc.
      generalize (axiom1 PB1 _ p _ (pullback_lemma_map2_obligation_1 Q p q H)).
      intros. rewrite H0.
      apply (axiom1 PB2).
    Qed.
    Next Obligation.
      apply (axiom2 PB1 _ p _ (pullback_lemma_map2_obligation_1 Q p q H)).
    Qed.
    Next Obligation.
      assert (g1 ∘ k ≈ pullback_lemma1_map1 Q p q H).
      apply (uniq PB2).
      rewrite <- H0.
      rewrite <- (cat_assoc f3 g2 _).
      rewrite <- (cat_assoc f3 (g2 ∘ g1) _).
      apply cat_respects.
      auto.
      apply cat_assoc.
      apply (uniq PB1).
      rewrite <- (cat_assoc f2 g1 _).
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
    { unit   : nt (FunctorIdent D) (R ∘ L)
    ; counit : nt (L ∘ R) (FunctorIdent C)
    ; adjoint_axiom1 : counit>>L ∘ L@@unit ≈ id
    ; adjoint_axiom2 : R@@counit ∘ unit>>R ≈ id
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
    ; axiom : forall j j' (h:j → j'), spoke j' ≈ F@h ∘ spoke j 
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
    rewrite (cat_ident1 (spoke M j)). reflexivity.
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
      (Category.Class _ _
      (fun A B => Eq.Mixin _ (fun f g => hom_map f ≈ hom_map g) _ _ _)
      (Comp.Mixin _ _ cone_ident cone_compose)
      _).
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
  ; hom_axiom : hom_map ∘ iota M ≈ iota N ∘ F@hom_map
  }.

  Program Definition ident (M:alg) : alg_hom M M :=
    Alg_hom M M (id) _.
  Next Obligation.
    intros.
    rewrite (cat_ident2 (iota M)).
    rewrite (Functor.ident F); trivial.
    rewrite (cat_ident1 (iota M)).
    trivial.
  Qed.

  Program Definition compose (M N O:alg)
    (f:alg_hom N O) (g:alg_hom M N) : alg_hom M O :=
    Alg_hom M O (hom_map _ _ f ∘ hom_map _ _ g) _.
  Next Obligation.
    intros.
    rewrite <- (cat_assoc (hom_map N O f)).
    rewrite (hom_axiom _ _ g).
    rewrite (cat_assoc (hom_map N O f)).
    rewrite (hom_axiom _ _ f).
    rewrite <- (cat_assoc (iota O)).
    rewrite <- (Functor.compose F); reflexivity.
  Qed.

  Record initial_alg :=
  Initial_alg
  { init :> alg
  ; cata : forall M:alg, alg_hom init M
  ; cata_axiom : forall (M:alg) (h:alg_hom init M), hom_map _ _ h ≈ hom_map _ _ (cata M)
  }.

  Lemma cata_axiom' I :
    forall (M:alg) (h:carrier (init I) → carrier M),
      (h ∘ iota (init I) ≈ iota  M ∘ F@h) ->
      h ≈ hom_map _ _ (cata I M).
  Proof.
    intros.
    apply (cata_axiom I M (Alg_hom _ _ h H)).
  Qed.

  Definition lift_alg (A:alg) :=
    Alg (F A) (F@iota A).

  Definition out (I:initial_alg) :=
    hom_map _ _ (cata I (lift_alg I)).

  Lemma in_out : forall (I:initial_alg),
    iota I ∘ out I ≈ id.
  Proof.
    intros.
    transitivity (hom_map _ _ (cata I I)).
    apply cata_axiom'.
    rewrite <- (cat_assoc (iota I)).
    apply cat_respects; auto.
    rewrite (hom_axiom _ _ (cata I (lift_alg I))).
    simpl.
    symmetry. apply Functor.compose. auto.

    symmetry. apply cata_axiom'.
    rewrite (cat_ident2 (iota I)).
    rewrite (Functor.ident F); auto.
    rewrite (cat_ident1 (iota I)).
    auto.
  Qed.

  Lemma out_in : forall (I:initial_alg),
    out I ∘ iota I ≈ id.
  Proof.
    intros.
    transitivity (F@(hom_map _ _ (cata I I))).
    unfold out.
    rewrite (hom_axiom).
    simpl.
    symmetry.
    apply Functor.compose.
    rewrite in_out.
    symmetry.
    apply cata_axiom'.
    rewrite (cat_ident2 (iota I)).
    rewrite Functor.ident.
    rewrite (cat_ident1 (iota I)).
    reflexivity. reflexivity.
    apply Functor.ident.
    symmetry.
    apply cata_axiom'.
    rewrite (cat_ident2 (iota I)).
    rewrite Functor.ident.
    rewrite (cat_ident1 (iota I)).
    reflexivity. reflexivity.
  Qed.    

  Lemma initial_inj_epic : forall (I:initial_alg) B (g h: I → B),
    g ∘ iota I ≈ h ∘ iota I ->
    g ≈ h.
  Proof.
    intros.
    cut (g ∘ id ≈ h ∘ id ).
    rewrite (cat_ident1 g).
    rewrite (cat_ident1 h).
    auto.
    rewrite <- (in_out I).
    rewrite (cat_assoc g).
    rewrite H.
    rewrite (cat_assoc h).
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
    Category _ _
      (Category.Class _ _
      (fun A B => Eq.Mixin _ (fun f g => Alg.hom_map f ≈ Alg.hom_map g) _ _ _)
      (Comp.Mixin _ _ (@ident _ _) (@compose _ _)) _).
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
    Category.category_axioms prod_ob prod_hom hom_eq_mixin comp_mixin.
  Proof.
    constructor.

    simpl; intros. split; simpl; apply cat_ident1.
    simpl; intros. split; simpl; apply cat_ident2.
    simpl; intros. split; simpl; apply cat_assoc.
    simpl; intros. destruct H; destruct H0.
    split; simpl; apply cat_respects; auto.
  Qed.    

  Definition prod_cat_class : Category.class_of prod_ob prod_hom :=
    Category.Class prod_ob prod_hom hom_eq_mixin comp_mixin prod_cat_axioms.

  Canonical Structure PROD := Category prod_ob prod_hom prod_cat_class.
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
      (fun X Y f => PROD.Hom _ _ _ _ (F@f) (G@f))
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
  Category unit (fun _ _ => unit)
    (Category.Class _ _
      (fun A B => Eq.Mixin _ (fun x y => True) _ _ _)
      (Comp.Mixin _ _ (fun _ => tt) (fun _ _ _ _ _ => tt))
      _).
Solve Obligations of ONE using auto.
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
  Functor C D (fun _ => A) (fun _ _ _ => id(A)) _ _ _ .
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
    Category _ _ 
      (Category.Class _ _ 
        (fun A B => (lib_eq (thom A B))) 
        (Comp.Mixin _ _ ident compose)
        _).
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
Record set_ob :=
  (** Note: we can't use Eq.type because then a universe inconsitency arises.
      However, the following workaround seems just as good.
   *)
  Set_ob 
  { carrier :> Type
  ; mixin : Eq.mixin_of carrier
  }.

(** This lets us treat a set_ob like an Eq.type *)
Canonical Structure set_ob_Eq X := Eq.Pack (carrier X) (mixin X).

Record hom (A B:set_ob) :=
  Hom
  { hom_map :> A -> B
  ; hom_axiom : forall x y, x ≈ y -> hom_map x ≈ hom_map y
  }.

Program Definition set_hom_eq A B : Eq.mixin_of (hom A B) :=
  Eq.Mixin _ (fun f g => forall x, f x ≈ g x) _ _ _.
Next Obligation.
  eauto.
Qed.

Definition ident (A:set_ob) : hom A A :=
  Hom A A (fun x => x) (fun x y H => H).

Definition compose (A B C:set_ob) (f:hom B C) (g:hom A B) : hom A C :=
  Hom A C 
    (fun x => f (g x)) 
    (fun x y H => hom_axiom _ _ f _ _ (hom_axiom _ _ g _ _ H)).

Definition set_hom_comp : Comp.mixin_of set_ob hom :=
  Comp.Mixin _ _ ident compose.
End SET.

Canonical Structure SET_EQ A B := Eq.Pack _ (SET.set_hom_eq A B).
Canonical Structure SET_COMP := Comp.Pack _ _ SET.set_hom_comp.

Program Definition SET : category :=
  Category _ _ (Category.Class _ _ SET.set_hom_eq SET.set_hom_comp _).
Next Obligation.
  constructor.
  intros. hnf. simpl. intros. apply eq_refl.
  intros. hnf. simpl. intros. apply eq_refl.
  intros. hnf. simpl. intros. apply eq_refl.
  intros. hnf. simpl; intros.
  apply eq_trans with (SET.hom_map _ _ f' (SET.hom_map _ _ g x)).
  apply H.
  apply SET.hom_axiom.
  apply H0.
Qed.

Coercion SET.carrier  : SET.set_ob >-> Sortclass.
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


Definition SET1 : ob SET := SET.Set_ob unit (lib_eq _).

Definition elem (X:ob SET) (x:X) : SET1 → X :=
  SET.Hom _ _ (fun _ => x) (fun a b H => eq_refl _ _).


(**  We can define the category class structure for the large
     category of small categories.  However! we cannot complete
     the construction due to a universe inconsistency.  If we
     had universe polymorphism we could get the definition we want.
  *)
Program Definition CAT_class : Category.class_of category functor :=
    Category.Class _ _
      (fun A B => lib_eq (functor A B))
      (Comp.Mixin category functor
        (fun X => FunctorIdent X)
        (fun X Y Z => FunctorCompose X Y Z)) _.
Next Obligation.
  constructor.
  intros. hnf. destruct f; auto.
  intros. hnf. destruct f; auto.
  intros. reflexivity.
  intros. hnf in *. subst. auto.
Qed.

(** No can do, universe inconsistency:

<<
Definition CAT : category := Category _ _ CAT_class.
>>
*)
