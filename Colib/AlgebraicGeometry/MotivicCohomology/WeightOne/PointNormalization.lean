/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.FieldComponent
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.NormCoordinates

/-!
# The actual norm formula for represented weight-one classes

The comparison is the fixed geometric sheaf map, not a chosen equivalence.
Its raw degree-one component and the original zero-simplex pullback give the
literal whole-support norm on every signed correspondence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicSimplex

universe u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers NativeTorusPolynomial

variable (k : Type u) [Field k]

/-- The fixed cohomological map sends each actual signed point cycle to its determinant norm. -/
theorem rawComparisonNorm_cycleClass (z : point k ⟶ pointTarget k) :
    rawComparisonNorm k (cycleClass k z) = pointCycleNorm k z := by
  change rawComparisonNorm k (rawClass k ((motivicRawBaseComplexXIso k 1 0).inv
    ((toReducedTorus k 1).hom.app (op (Cor.simplexProduct (point k) 0))
      (ULift.up (zeroSimplexProjection k ≫ z))))) = _
  rw [rawComparisonNorm_rawClass]
  have hq := reducedTorus_transfer_apply k 1 (zeroSimplexProjection k) z
  change (rawReducedTorus k).map
      (productFst (base (Spec (.of k))) (smoothSiteObj k 0)).op
        ((toReducedTorus k 1).hom.app (op (point k)) (ULift.up z)) =
    (toReducedTorus k 1).hom.app (op (Cor.simplexProduct (point k) 0))
      (ULift.up (zeroSimplexProjection k ≫ z)) at hq
  rw [← hq, rawWeightOneComparison_zero_pullback]
  exact congrArg ULift.down (reducedNorm_point_toReduced k z)

/-- The literal graph of a unit maps to that unit, without inversion. -/
@[simp] theorem rawComparisonNorm_graphUnitClass (a : kˣ) :
    rawComparisonNorm k (graphUnitClass k a) = Additive.ofMul a := by
  rw [graphUnitClass, rawComparisonNorm_cycleClass, pointCycleNorm_graph]

/-- The actual signed generator retains the determinant of its whole support algebra. -/
theorem rawComparisonNorm_generator (Z : PrimePoint (𝟙 (Spec (.of k)))) (m : ℤ) :
    rawComparisonNorm k (cycleClass k (pointGenerator k Z m)) =
      m • Additive.ofMul Z.coordinateNorm := by
  rw [rawComparisonNorm_cycleClass, pointCycleNorm_generator]

/-- The already proved geometric comparison identifies every cycle class with its norm graph. -/
theorem cycleClass_eq_graphUnitClass_norm (z : point k ⟶ pointTarget k) :
    cycleClass k z = graphUnitClass k (pointCycleNorm k z).toMul := by
  apply (rawComparisonNorm_bijective k).injective
  rw [rawComparisonNorm_cycleClass, rawComparisonNorm_graphUnitClass]
  rfl

/-- Signed multiplicities remain visible in the actual norm graph representative. -/
theorem cycleClass_pointGenerator (Z : PrimePoint (𝟙 (Spec (.of k)))) (m : ℤ) :
    cycleClass k (pointGenerator k Z m) = graphUnitClass k (Z.coordinateNorm ^ m) := by
  rw [cycleClass_eq_graphUnitClass_norm, pointCycleNorm_generator_toMul]

end AlgebraicGeometry.MotivicCohomology.WeightOne
