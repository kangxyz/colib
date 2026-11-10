/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.Contraction
import Colib.AlgebraicGeometry.PresheavesWithTransfers.RepresentableLarge
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus

/-!
# Actual large-coefficient consumers of native contraction

The coefficients are the existing universe-lifted signed representables and
the existing reduced torus. The tests retain the actual exterior transfer,
two negative signs, the positive Laurent graph, and the ordinary quotient map.
These source examples have not been elaborated by Lean.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe u

namespace TransferContractionTest

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "A" => SmoothSite.additiveGroupObject S
local notation "T" => SmoothSite.multiplicativeGroupObject S

example : GeometricallyIntegral (A).hom := inferInstance

example : GeometricallyIntegral (T).hom := inferInstance

/-- No small-universe replacement of the actual reduced torus is needed. -/
example (q : ℕ) : PresheafWithTransfers.{u + 1} k :=
  contraction (reducedTorus k q)

/-- Arbitrary signed correspondences act by literal exterior precomposition. -/
example (Z : Cor k) {X Y : Cor k} (α : X ⟶ Y)
    (β : Cor.mk (SmoothSite.product Y.toSmoothSite T) ⟶ Z) :
    transfer (contraction ((representableLarge k).obj Z)) α
        ((toContraction ((representableLarge k).obj Z)).hom.app (op Y) (ULift.up β)) =
      (toContraction ((representableLarge k).obj Z)).hom.app (op X)
        (ULift.up (Stacks.Chow.nativeExterior X.toSmoothSite Y.toSmoothSite T α ≫ β)) :=
  contraction_transfer_apply ((representableLarge k).obj Z) α (ULift.up β)

/-- Both negative integer coefficients survive until actual signed composition cancels them. -/
example (Z : Cor k) {X Y : Cor k} (α : X ⟶ Y)
    (β : Cor.mk (SmoothSite.product Y.toSmoothSite T) ⟶ Z) :
    transfer (contraction ((representableLarge k).obj Z)) (-α)
        ((toContraction ((representableLarge k).obj Z)).hom.app (op Y) (ULift.up (-β))) =
      (toContraction ((representableLarge k).obj Z)).hom.app (op X)
        (ULift.up (Stacks.Chow.nativeExterior X.toSmoothSite Y.toSmoothSite T α ≫ β)) := by
  rw [contraction_transfer_apply]
  change (toContraction ((representableLarge k).obj Z)).hom.app (op X)
      (ULift.up (Stacks.Chow.nativeExterior X.toSmoothSite Y.toSmoothSite T (-α) ≫ (-β))) = _
  apply congrArg ((toContraction ((representableLarge k).obj Z)).hom.app (op X))
  apply congrArg ULift.up
  rw [map_neg]
  exact Preadditive.neg_comp_neg (C := Cor k) _ β

/-- Restriction of a negative affine-cylinder cycle is killed by the actual quotient. -/
example (Z : Cor k) (X : SmoothSite S)
    (β : Cor.mk (SmoothSite.product X A) ⟶ Z) :
    (toContraction ((representableLarge k).obj Z)).hom.app (op (Cor.mk X))
        (ULift.up ((Cor.graphFunctor k).map
          (SmoothSite.Contraction.openInclusion.app X) ≫ (-β))) = 0 := by
  have h := congrArg (fun η => η.hom.app (op (Cor.mk X)))
    (contractionRestriction_toContraction ((representableLarge k).obj Z))
  exact ConcreteCategory.congr_hom h (ULift.up (-β))

/-- The ordinary graph restriction is the precise quotient, preserving a negative class. -/
example (Z : Cor k) (X : SmoothSite S)
    (β : Cor.mk (SmoothSite.product X T) ⟶ Z) :
    (contractionUnderlyingIso ((representableLarge k).obj Z)).hom.app (op X)
        ((toContraction ((representableLarge k).obj Z)).hom.app
          (op (Cor.mk X)) (ULift.up (-β))) =
      (SmoothSite.Contraction.quotient
        ((toPresheaf k).obj ((representableLarge k).obj Z))).app (op X) (ULift.up (-β)) :=
  contractionUnderlyingIso_quotient_apply ((representableLarge k).obj Z) X (ULift.up (-β))

end TransferContractionTest
