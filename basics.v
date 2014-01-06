(* Copyright (c) 2014, Robert Dockins *)

Require Import Setoid.

(** * Setoids and equality.

      This module introduces setoids, which consist of a type packaged together with
      an equivalence relation.  We roughly follow the techniques described in the paper
      _Packaging Mathematical Structures_ by Garillot et al. (TPHOLS 2009).  The mainstay
      of this technique is using canonoical structures to automatically infer structures
      given the carrier type.

      We use the symbol ≈ to indicate the equality relation on setoids.  For the vast
      majority of this development, ≈ will be the notion of equivalence of interest.
  *)

Module Eq.
  Record mixin_of (T:Type) :=
    Mixin
    { eq : T -> T -> Prop
    ; refl : forall x, eq x x
    ; symm : forall x y, eq x y -> eq y x
    ; trans : forall x y z,
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
