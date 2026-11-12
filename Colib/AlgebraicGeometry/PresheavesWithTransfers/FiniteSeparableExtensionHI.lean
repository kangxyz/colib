/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteSeparableExtension
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
public import Colib.AlgebraicGeometry.Sites.Smooth.BaseChange.ForgetBaseA1

/-!
# Ordinary homotopy invariance of the actual extended coefficient

The finite-separable coefficient is the actual additive precomposition functor.
Its literal native affine projection is the original coefficient's projection
followed by the actual native cylinder comparison. Thus ordinary coefficient
HI is preserved, with an independent coefficient universe. This neither uses
nor asserts strict invariance, a cohomology comparison, Cartesian trace
naturality, or specialization of a finite-flat family at 0 and 1.

This supplies the last two declarations of motivic's
`Transfers/Presheaf/FiniteSeparableExtension`, blob
93476ac76015855f7831c652724407e4cb191a98, in the current native cylinder model.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} (L : Type u) [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

local notation "F" => SmoothSite.finiteSeparableForgetBase k L

/-- The literal native extended projection factors through the original native projection. -/
theorem finiteSeparableExtension_projection (P : PresheafWithTransfers.{v} k)
    (X : SmoothSite (Spec (.of L))) :
    A1.projectionPullback (.of L) ((toPresheaf L).obj (finiteSeparableExtension L P)) X =
      A1.projectionPullback (.of k) ((toPresheaf k).obj P) ((F).obj X) ≫
        ((toPresheaf k).obj P).map (SmoothSite.finiteSeparableForgetBaseA1Iso k L X).hom.op := by
  let a := SmoothSite.productFst X (SmoothSite.additiveGroupObject (Spec (.of L)))
  let b := SmoothSite.productFst ((F).obj X) (SmoothSite.additiveGroupObject (Spec (.of k)))
  let i := SmoothSite.finiteSeparableForgetBaseA1Iso k L X
  change ((toPresheaf L).obj (finiteSeparableExtension L P)).map a.op =
    ((toPresheaf k).obj P).map b.op ≫ ((toPresheaf k).obj P).map i.hom.op
  have h : i.hom ≫ b = (F).map a :=
    SmoothSite.finiteSeparableForgetBaseA1Iso_hom_projection k L X
  calc
    _ = ((toPresheaf k).obj P).map ((F).map a).op := finiteSeparableExtension_graph L P a
    _ = _ := by rw [← h, op_comp, Functor.map_comp]

/-- Ordinary HI is preserved by the real extended coefficient, not by an assumed value iso. -/
theorem finiteSeparableExtension_isA1Invariant (P : PresheafWithTransfers.{v} k)
    (hP : P.IsA1Invariant) : (finiteSeparableExtension L P).IsA1Invariant := by
  intro X
  rw [finiteSeparableExtension_projection]
  let := hP ((F).obj X)
  infer_instance

end AlgebraicGeometry.PresheafWithTransfers
