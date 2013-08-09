Require Import Setoid.

Module Eq.
  Record mixin_of (T:Type) :=
    Mixin
    { eq : T -> T -> Prop
    ; refl : forall x, eq x x
    ; symm : forall {x y}, eq x y -> eq y x
    ; trans : forall {x y z},
             eq x y -> eq y z -> eq x z
    }.
  Structure type : Type :=
    Pack { carrier :> Type ; mixin : mixin_of carrier }.

End Eq.
Definition eq_op T := Eq.eq _ (Eq.mixin T).
Notation "x ≈ y" := (@eq_op _ x y) (at level 70).
Notation "x ≉ y" := (~(@eq_op _ x y)) (at level 70).

Coercion Eq.carrier : Eq.type >-> Sortclass.

Lemma eq_refl : forall (T:Eq.type) (x:T), x ≈ x.
Proof.
  intros. destruct T. destruct mixin. apply refl.
Qed.

Lemma eq_trans : forall (T:Eq.type) (x y z:T), x ≈ y -> y ≈ z -> x ≈ z.
Proof.
  intros. destruct T. destruct mixin. eapply trans; eauto.
Qed.

Lemma eq_symm : forall (T:Eq.type) (x y:T), x ≈ y -> y ≈ x.
Proof.
  intros. destruct T. destruct mixin. eapply symm; eauto.
Qed.

Hint Resolve eq_refl eq_symm eq_trans.

Add Parametric Relation (T:Eq.type) : (Eq.carrier T) (@eq_op T)
  reflexivity proved by (@eq_refl T)
  symmetry proved by (@eq_symm T)
  transitivity proved by (@eq_trans T)
  as eq_op_rel.

Record eq_dec (T:Eq.type) :=
    EqDec
    { eqdec :> forall x y:T, {x ≈ y}+{x ≉ y} }. 

Arguments eqdec [T] [e] x y.
