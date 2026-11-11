/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.PointNormalization

/-!
# The normalized weight-one equivalence over the original field

The forward map is the actual geometric cochain comparison in its fixed units
coordinates. Its inverse is the literal rational graph class. The norm formula
on signed cycles was proved before choosing the equivalence structure.

This is a reconstruction of the mathematical endpoints of
Motivic/Cohomology/WeightOne/Equivalence.lean at revision
a6805c4a87cdfd7717dd7a94039246a167f15380, through the actual sheaf comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The norm of the actual geometric comparison, now identified on every represented cycle. -/
abbrev homologyNorm : (motivicRawBaseComplex k 1).homology 1 →+ Additive kˣ :=
  rawComparisonNorm k

/-- The original field's raw weight-one homology, in the specified norm coordinates. -/
def homologyEquiv : (motivicRawBaseComplex k 1).homology 1 ≃+ Additive kˣ :=
  AddEquiv.ofBijective (homologyNorm k) (rawComparisonNorm_bijective k)

@[simp] theorem homologyEquiv_apply (x : (motivicRawBaseComplex k 1).homology 1) :
    homologyEquiv k x = homologyNorm k x := rfl

/-- The inverse is the genuine rational graph class, not an arbitrarily chosen section. -/
theorem homologyEquiv_symm_apply (a : Additive kˣ) :
    (homologyEquiv k).symm a = graphUnitClass k a.toMul := by
  apply (homologyEquiv k).injective
  rw [AddEquiv.apply_symm_apply, homologyEquiv_apply, homologyNorm,
    rawComparisonNorm_graphUnitClass]
  rfl

/-- The actual norm on every signed correspondence is the pre-existing support determinant. -/
theorem homologyNorm_cycleClass (z : point k ⟶ pointTarget k) :
    homologyNorm k (cycleClass k z) = pointCycleNorm k z :=
  rawComparisonNorm_cycleClass k z

/-- The rational graph class of the identity unit vanishes in the actual reduced complex. -/
@[simp] theorem graphUnitClass_one : graphUnitClass k 1 = 0 := by
  apply (rawComparisonNorm_bijective k).injective
  rw [rawComparisonNorm_graphUnitClass, map_zero]
  rfl

/-- Multiplication of units is addition of their actual rational graph classes. -/
theorem graphUnitClass_mul (a b : kˣ) :
    graphUnitClass k (a * b) = graphUnitClass k a + graphUnitClass k b := by
  apply (rawComparisonNorm_bijective k).injective
  rw [map_add, rawComparisonNorm_graphUnitClass, rawComparisonNorm_graphUnitClass,
    rawComparisonNorm_graphUnitClass]
  rfl

/-- The inverse norm homomorphism is defined by the actual graph representatives. -/
def graphUnitHom : Additive kˣ →+ (motivicRawBaseComplex k 1).homology 1 where
  toFun a := graphUnitClass k a.toMul
  map_zero' := graphUnitClass_one k
  map_add' a b := graphUnitClass_mul k a.toMul b.toMul

/-- The genuine graph map is the inverse of the specified geometric norm. -/
theorem graphUnitHom_homologyNorm (x : (motivicRawBaseComplex k 1).homology 1) :
    graphUnitHom k (homologyNorm k x) = x := by
  apply (rawComparisonNorm_bijective k).injective
  exact rawComparisonNorm_graphUnitClass k (homologyNorm k x).toMul

end AlgebraicGeometry.MotivicCohomology.WeightOne
