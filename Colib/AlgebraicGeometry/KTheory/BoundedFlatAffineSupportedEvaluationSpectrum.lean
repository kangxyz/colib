/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedEvaluationComparison

/-!
# The actual supported evaluation prespectrum equivalence

The canonically normalized original evaluation admits an actual inverse and whole coherent
left and right inverse homotopies. All levels, including level zero, and all integer stable
homotopy groups are covered. No all-perfect or Bass localization comparison is claimed.
Adapted from Quillen `BoundedFlat/SupportedSectionSpectrumEquivalence.lean:31-109` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory Topology
open scoped unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual inverse model functor with its canonical chosen-zero normalization. -/
def boundedAboveFlatAffineSupportedSectionEvaluationInverseModelMap :
    asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen j) ⟶
      boundedAboveFlatAffineSupportedSectionModel j :=
  ExactModelEquivalence.backward
    (V := boundedAboveFlatAffineSupportedSectionModel j)
    (W := asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen j))
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact j)

/-- The named inverse of the actual normalized evaluation prespectrum map. -/
def boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap :
    originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j) ⟶ prespectrum
      (boundedAboveFlatAffineSupportedSectionModel j) :=
  prespectrumMap (boundedAboveFlatAffineSupportedSectionEvaluationInverseModelMap j)

/-- The actual coherent left inverse homotopy at every level and structure time. -/
def boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy :
    LoopPrespectrum.Homotopy
      (boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j ≫
        boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap j)
      (𝟙 (prespectrum (boundedAboveFlatAffineSupportedSectionModel j))) :=
  ExactModelEquivalence.leftHomotopy
    (V := boundedAboveFlatAffineSupportedSectionModel j)
    (W := asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen j))
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_exact j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_zero j)

/-- The actual coherent right inverse homotopy for the same canonical inverse. -/
def boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy :
    LoopPrespectrum.Homotopy
      (boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap j ≫
        boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j)
      (𝟙 (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j))) :=
  ExactModelEquivalence.rightHomotopy
    (V := boundedAboveFlatAffineSupportedSectionModel j)
    (W := asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen j))
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_exact j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_zero j)

/-- The named evaluation has an actual homotopy inverse at every level, including zero. -/
def boundedAboveFlatAffineSupportedSectionEvaluationLevelEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv ((prespectrum (boundedAboveFlatAffineSupportedSectionModel j)).space
      n)
      ((originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).space n) :=
  ExactModelEquivalence.levelHomotopyEquiv
    (V := boundedAboveFlatAffineSupportedSectionModel j)
    (W := asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen j))
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_exact j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_zero j) n

/-- Complete weak equivalence of the named original map includes the zeroth loop level. -/
theorem boundedAboveFlatAffineSupportedSectionEvaluation_level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap
      j).map n) :=
  ExactModelEquivalence.level_isWeakHomotopyEquivalence
    (V := boundedAboveFlatAffineSupportedSectionModel j)
    (W := asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen j))
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_exact j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_zero j) n

/-- The actual normalized evaluation is invertible on stable homotopy in every integer degree. -/
theorem boundedAboveFlatAffineSupportedSectionEvaluation_isStableEquivalence :
    LoopPrespectrum.IsStableEquivalence
      (boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j) :=
  ExactModelEquivalence.isStableEquivalence
    (V := boundedAboveFlatAffineSupportedSectionModel j)
    (W := asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen j))
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_exact j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact j)
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_zero j)

/-- The left inverse track starts at the actual composite. -/
theorem boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_at_zero (n : ℕ) (x :
  (prespectrum (boundedAboveFlatAffineSupportedSectionModel j)).space n) :
    (boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).level n (0, x) =
      (boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap j).map n
        ((boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j).map n x) :=
  (boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).at_zero n x

/-- The left inverse track ends at the original point. -/
theorem boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_at_one (n : ℕ) (x :
  (prespectrum (boundedAboveFlatAffineSupportedSectionModel j)).space n) :
    (boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).level n (1, x) = x :=
  (boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).at_one n x

/-- The left inverse track preserves the basepoint for every homotopy time. -/
theorem boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_at_point (n : ℕ) (s :
  unitInterval) :
    (boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).level n (s, (prespectrum
      (boundedAboveFlatAffineSupportedSectionModel j)).point n) = (prespectrum
      (boundedAboveFlatAffineSupportedSectionModel j)).point n :=
  (boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).at_point n s

/-- Structure compatibility retains independent level, homotopy time and loop time. -/
theorem boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_comm (n : ℕ) (s t :
  unitInterval) (x : (prespectrum (boundedAboveFlatAffineSupportedSectionModel j)).space n) :
    (boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).level (n + 1) (s, (prespectrum
      (boundedAboveFlatAffineSupportedSectionModel j)).structureMap n x t) =
      (prespectrum (boundedAboveFlatAffineSupportedSectionModel j)).structureMap n
        ((boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).level n (s, x)) t :=
  (boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).comm n s x t

/-- The right inverse track starts at the actual composite. -/
theorem boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_at_zero (n : ℕ) (x :
  (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).space n) :
    (boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).level n (0, x) =
      (boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j).map n
        ((boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap j).map n x) :=
  (boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).at_zero n x

/-- The right inverse track ends at the original point. -/
theorem boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_at_one (n : ℕ) (x :
  (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).space n) :
    (boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).level n (1, x) = x :=
  (boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).at_one n x

/-- The right inverse track preserves the basepoint for every homotopy time. -/
theorem boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_at_point (n : ℕ) (s :
  unitInterval) :
    (boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).level n (s,
      (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).point n) =
      (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).point n :=
  (boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).at_point n s

/-- Structure compatibility retains independent level, homotopy time and loop time. -/
theorem boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_comm (n : ℕ) (s t :
  unitInterval) (x : (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).space n) :
    (boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).level (n + 1) (s,
      (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).structureMap n x t) =
      (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).structureMap n
        ((boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).level n (s, x)) t :=
  (boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).comm n s x t

attribute [colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
      Support.lean:39-62"
    "adaptation" "Fixed-open supported bounded-flat section evaluation with its actual maps"]
  boundedAboveFlatPerfectSupported
  boundedAboveFlatPerfectSupported_containsZero
  boundedAboveFlatPerfectSupported_closedUnderIsomorphisms
  boundedAboveFlatPerfectSupported_extensionClosed
  boundedAboveFlatPerfectSupported_closedUnderFiniteProducts

attribute [colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
      SupportComparison.lean:45-48"
    "adaptation" "Fixed-open supported bounded-flat section evaluation with its actual maps"]
  boundedAboveFlatPerfectSupportedWaldhausen
  boundedAboveFlatPerfectSupportedWaldhausen_cof_iff
  boundedAboveFlatPerfectSupportedWaldhausen_weq_iff

attribute [colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
      SupportedSections.lean:33-55"
    "adaptation" "Fixed-open supported bounded-flat section evaluation with its actual maps"]
  boundedAboveFlatAffineSectionSupported
  BoundedAboveFlatAffineSupportedSections
  boundedAboveFlatAffineSupportedEvaluation
  boundedAboveFlatAffineSupportedEvaluation_obj

attribute [colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
      SupportedSectionEquivalence.lean:28-65"
    "adaptation" "Fixed-open supported bounded-flat section evaluation with its actual maps"]
  boundedAboveFlatAffineSupportedEvaluation_property
  boundedAboveFlatAffineSupportedSectionEquivalence
  boundedAboveFlatAffineSupportedSectionEquivalence_functor
  boundedAboveFlatAffineSupportedEvaluation_isEquivalence
  boundedAboveFlatAffineSupportedEvaluationCounit

attribute [colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
      SupportedSectionZero.lean:31-49"
    "adaptation" "Fixed-open supported bounded-flat section evaluation with its actual maps"]
  boundedAboveFlatAffineSectionZero_supported
  boundedAboveFlatAffineSupportedSectionZero
  isZero_boundedAboveFlatAffineSupportedSectionZero

attribute [colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
      SupportedSectionWaldhausen.lean:34-90"
    "adaptation" "Fixed-open supported bounded-flat section evaluation with its actual maps"]
  boundedAboveFlatAffineSupportedEvaluation_sectionZero_isZero
  boundedAboveFlatAffineSupportedSectionWaldhausen
  boundedAboveFlatAffineSupportedSectionWaldhausen_zero
  boundedAboveFlatAffineSupportedSectionWaldhausen_cof_iff
  boundedAboveFlatAffineSupportedSectionWaldhausen_weq_iff
  boundedAboveFlatAffineSupportedEvaluation_exact
  boundedAboveFlatAffineSupportedSectionEquivalence_inverse_exact

attribute [colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
      SupportedSectionComparison.lean:35-120"
    "adaptation" "Fixed-open supported bounded-flat section evaluation with its actual maps"]
  boundedAboveFlatAffineSupportedSectionSmallEquivalence
  boundedAboveFlatAffineSupportedSectionSmallEquivalence_exact
  boundedAboveFlatAffineSupportedSectionSmallEquivalence_inverse_exact
  boundedAboveFlatAffineSupportedSectionEvaluationNormalizationIso
  boundedAboveFlatAffineSupportedSectionNormalizedEquivalence
  boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_exact
  boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact
  boundedAboveFlatAffineSupportedSectionEvaluationModelMap
  boundedAboveFlatAffineSupportedSectionEvaluationModelIso
  boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap
  boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_zero

attribute [colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
      SupportedSectionSpectrumEquivalence.lean:31-109"
    "adaptation" "Fixed-open supported bounded-flat section evaluation with its actual maps"]
  boundedAboveFlatAffineSupportedSectionEvaluationInverseModelMap
  boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap
  boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy
  boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy
  boundedAboveFlatAffineSupportedSectionEvaluationLevelEquiv
  boundedAboveFlatAffineSupportedSectionEvaluation_level_isWeakHomotopyEquivalence
  boundedAboveFlatAffineSupportedSectionEvaluation_isStableEquivalence
  boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_at_zero
  boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_at_one
  boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_at_point
  boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_comm
  boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_at_zero
  boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_at_one
  boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_at_point
  boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_comm

attribute [colib_tag "COL-0380"]
  boundedAboveFlatAffineSupportedSectionEquivalence
  boundedAboveFlatAffineSupportedSectionWaldhausen
  boundedAboveFlatAffineSupportedSectionEvaluationNormalizationIso
  boundedAboveFlatAffineSupportedSectionEvaluationModelMap
  boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap
  boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy
  boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy
  boundedAboveFlatAffineSupportedSectionEvaluationLevelEquiv
  boundedAboveFlatAffineSupportedSectionEvaluation_level_isWeakHomotopyEquivalence
  boundedAboveFlatAffineSupportedSectionEvaluation_isStableEquivalence

attribute [colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedSectionModel.lean:32-33"
    "adaptation" "The actual supported section small model with its original pointwise zero"]
  boundedAboveFlatAffineSupportedSectionModel

end AlgebraicGeometry.Scheme.Modules
