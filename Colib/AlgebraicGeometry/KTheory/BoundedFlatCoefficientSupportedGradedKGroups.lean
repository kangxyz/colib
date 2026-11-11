/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenGrading
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedEvaluationJoint
public import Colib.KTheory.Waldhausen.Cofinality.GeneralKZeroValue

/-! # Actual supported graded groups

Original positive graded K-vanishing and the injective actual K-zero value map. The existing
supported evaluation joint data are reused, not reconstructed. No cofinality or exact tail claim.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original graded section target has zero positive K-groups by its actual fine joint data. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenKZeroExact.lean:126"
  "adaptation" "Actual supported graded K-value and signed stable groups"]
theorem boundedAboveFlatCoefficientSupportedGradedOpen_K_succ_subsingleton (a : Under R) (n : ℕ) :
    Subsingleton ((boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.K (n +
      1)) :=
  (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarse_K_succ_subsingleton_general
    (boundedAboveFlatCoefficientSupportedSectionJointData
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι) n

/-- Original coarse K-zero values land in the unchanged actual raw-perfect image quotient. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenKZeroExact.lean:134"
  "adaptation" "Actual supported graded K-value and signed stable groups"]
def boundedAboveFlatCoefficientSupportedOpenKZeroValueMap (a : Under R) :
    (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.K 0 →*
      Multiplicative (BoundedAboveFlatCoefficientSupportedOpenImageQuotient f T a) :=
  (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseKZeroValueMap
    (boundedAboveFlatCoefficientSupportedSectionJointData
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).reflexiveAsSmall.sourceFactorization

/-- The original value map detects equality of the actual graded section K-zero classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenKZeroExact.lean:142"
  "adaptation" "Actual supported graded K-value and signed stable groups"]
theorem boundedAboveFlatCoefficientSupportedOpenKZeroValueMap_injective (a : Under R) :
    Function.Injective (boundedAboveFlatCoefficientSupportedOpenKZeroValueMap f T a) :=
  (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseKZeroValueMap_injective
    (boundedAboveFlatCoefficientSupportedSectionJointData
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).reflexiveAsSmall.sourceFactorization

end AlgebraicGeometry.Scheme.Modules
