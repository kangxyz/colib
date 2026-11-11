/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenModels
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.EquivalenceJoint

/-! # Original exact supported evaluation and transported joint data

This extracts only the actual exact evaluation and joint-cylinder inputs of the original
coefficient supported fibration. No K-zero quotient, cofinality, or grading theorem is copied.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedAboveFlatCoefficientSupportedEvaluation
  boundedAboveFlatCoefficientSupportedSectionEquivalence

/-- The literal forward supported equivalence is exact for the original fine structures. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:38"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
theorem boundedAboveFlatCoefficientSupportedSectionEquivalence_functor_exact
    {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] :
    IsExact (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).weq
      (boundedAboveFlatPerfectSupportedWaldhausen j).cof
        (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (boundedAboveFlatCoefficientSupportedSectionEquivalence j).functor := by
  rw [boundedAboveFlatCoefficientSupportedSectionEquivalence_functor]
  exact boundedAboveFlatCoefficientSupportedEvaluation_exact j

/-- Actual supported joint cylinders transport through the original evaluation inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenKZeroExact.lean:110"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
def boundedAboveFlatCoefficientSupportedSectionJointData {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] :
    Fibration.RowFactorization.JointData
      (Fibration.NestedWeakEquivalences.refl
        (boundedAboveFlatCoefficientSupportedSectionWaldhausen j)) :=
  Fibration.RowFactorization.JointData.ofExactEquivalence
    (boundedAboveFlatPerfectSupportedWaldhausen j)
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen j)
    (boundedAboveFlatCoefficientSupportedSectionEquivalence j).symm
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact j)
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_functor_exact j)
    (boundedAboveFlatPerfectSupportedJointData j)

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Supported coarse evaluation is exact by the proved correspondence of the original weak maps.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenCofinality.lean:96"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
theorem boundedAboveFlatCoefficientSupportedOpenEvaluation_coarse_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).cof
      (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).weq
      (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).cof
      (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).weq
      (boundedAboveFlatCoefficientSupportedEvaluation (boundedAboveFlatCoefficientSupportOpen Q T
        a).ι)
    where
  zero := (boundedAboveFlatCoefficientSupportedEvaluation_exact
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι).zero
  cofibration := (boundedAboveFlatCoefficientSupportedEvaluation_exact
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι).cofibration
  weak p hp := (boundedAboveFlatCoefficientSupportedOpenWaldhausen_weq_iff f T a p).mp hp
  pushout := (boundedAboveFlatCoefficientSupportedEvaluation_exact
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι).pushout

end AlgebraicGeometry.Scheme.Modules
