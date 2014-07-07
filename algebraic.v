(* Copyright (c) 2014, Robert Dockins *)

Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.

Definition way_below {A:preord} (CL:color) (x y:A) :=
  forall (D:cl_eset CL A) lub, least_upper_bound lub D ->
    y ≤ lub ->
    exists d, d ∈ D /\ x ≤ d.

Definition compact {A:preord} (CL:color) (a:A) := way_below CL a a.

Module algebraic.
Section algebraic.
  Variable CL:color.

  Record mixin_of
    (ord:preord) (basis:preord) :=
    Mixin
    { basis_inj : basis → ord
    ; basis_dec : forall x y:basis, {x ≤ y}+{x ≰ y}
    ; basis_enum : eset basis
    ; basis_enum_complete :
          forall k:basis, k ∈ basis_enum
    ; basis_inj_reflects : forall k k',
           basis_inj k ≤ basis_inj k' -> k ≤ k'

    ; basis_compact :
          forall k:basis, compact CL (basis_inj k)

    ; decomp : ord -> cl_eset CL basis
    ; decomp_complete : forall x k,
          k ∈ decomp x <-> way_below CL (basis_inj k) x
    ; decomp_axiom : forall x,
          least_upper_bound x (image basis_inj (decomp x))
    }.

  Record type :=
    Pack { carrier :> Type
         ; base : Type
         ; carrier_ord : Preord.mixin_of carrier
         ; base_ord : Preord.mixin_of base
         ; ord := Preord.Pack carrier carrier_ord
         ; basis := Preord.Pack base base_ord
         ; mixin :> mixin_of ord basis
         }. 
End algebraic.
End algebraic.

Canonical Structure basis_dec CL (T:algebraic.type CL) :=
  OrdDec
    (algebraic.basis CL T)
    (algebraic.basis_dec CL _ _ (algebraic.mixin CL T)).

