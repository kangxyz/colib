/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassEvaluationTopology
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationLevelWeakEquivalence
public import Colib.Topology.Prespectrum.PushoutHomotopySquareEquivalence
public import Colib.Topology.Prespectrum.ConeSquareLevelWeakEquivalence
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.WeakEquivalence


/-!
# Genuine weak and stable equivalence of the original one-step Bass evaluation

The actual polynomial and Laurent evaluation maps are complete weak equivalences at every
level. Original point HEP and the proved whole evaluation filler therefore preserve the original
span, cone and parameter-looped step. The target is the unchanged raw bounded-flat construction,
whose coefficient maps remain homotopy-natural. No strict target diagram or seed compatibility
is assumed, and no new stable-excision hypothesis is introduced.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace Topology
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u})

/-- The unchanged whole-track polynomial-span evaluation is completely weak at every level. -/
theorem boundedAboveFlatAffineSectionBassSpanEvaluation_level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedAboveFlatAffineSectionBassSpanEvaluation R).map n) :=
  HomotopyPushout.mapOfHomotopies_level_isWeakHomotopyEquivalence
    (boundedAboveFlatAffineSectionPrespectrumFunctor.map
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
    (boundedAboveFlatAffineSectionPrespectrumFunctor.map
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
    (boundedAboveFlatAffineEvaluationPrespectrumMap R)
    (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R)))
    (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R)))
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) n
    (prespectrum_point_homotopyExtensionProperty (boundedAboveFlatAffineSectionModel R) n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatAffineSectionModel (.of (Polynomial R))) n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatAffineSectionModel (.of (Polynomial R))) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen (Spec (.of (Polynomial R))).toRingedSpace) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen (Spec (.of (Polynomial R))).toRingedSpace) n)
    (boundedAboveFlatAffineEvaluation_level_isWeakHomotopyEquivalence R n)
    (boundedAboveFlatAffineEvaluation_level_isWeakHomotopyEquivalence (.of (Polynomial R)) n)
    (boundedAboveFlatAffineEvaluation_level_isWeakHomotopyEquivalence (.of (Polynomial R)) n)

/-- The original actual span evaluation is stable in every signed degree. -/
theorem boundedAboveFlatAffineSectionBassSpanEvaluation_isStableEquivalence :
    IsStableEquivalence (boundedAboveFlatAffineSectionBassSpanEvaluation R) :=
  isStableEquivalence_of_levelwise _
    (boundedAboveFlatAffineSectionBassSpanEvaluation_level_isWeakHomotopyEquivalence R)

/-- The exact cone map with the proved original filler is completely weak at every level. -/
theorem boundedAboveFlatAffineSectionBassConeEvaluation_level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedAboveFlatAffineSectionBassConeEvaluation R).map n) :=
  mappingConeSquareMap_level_isWeakHomotopyEquivalence
    (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R))
    (boundedAboveFlatBassSquareComparison R) (boundedAboveFlatAffineSectionBassSpanEvaluation R)
    (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
    (boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy R) n
    (boundedAboveFlatAffineSectionBassSpan_point_homotopyExtensionProperty R n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatAffineSectionModel (.of (LaurentPolynomial R))) n)
    (boundedAboveFlatBassSpan_point_homotopyExtensionProperty R n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))).toRingedSpace) n)
    (boundedAboveFlatAffineSectionBassSpanEvaluation_level_isWeakHomotopyEquivalence R n)
    (boundedAboveFlatAffineEvaluation_level_isWeakHomotopyEquivalence
      (.of (LaurentPolynomial R)) n)

/-- The unchanged original cone evaluation is a genuine signed stable equivalence. -/
theorem boundedAboveFlatAffineSectionBassConeEvaluation_isStableEquivalence :
    IsStableEquivalence (boundedAboveFlatAffineSectionBassConeEvaluation R) :=
  isStableEquivalence_of_levelwise _
    (boundedAboveFlatAffineSectionBassConeEvaluation_level_isWeakHomotopyEquivalence R)

/-- Actual parameter looping preserves every component at every original level, including zero. -/
theorem boundedAboveFlatAffineSectionBassStepEvaluation_level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedAboveFlatAffineSectionBassStepEvaluation R).map n) :=
  basedLoopMap_isWeakHomotopyEquivalence
    ((boundedAboveFlatAffineSectionBassConeEvaluation R).map n)
    ((boundedAboveFlatAffineSectionBassConeEvaluation R).map_point n)
    (boundedAboveFlatAffineSectionBassConeEvaluation_level_isWeakHomotopyEquivalence R n)

/-- The original strict-section Bass stage maps stably to the unchanged raw geometric Bass step. -/
theorem boundedAboveFlatAffineSectionBassStepEvaluation_isStableEquivalence :
    IsStableEquivalence (boundedAboveFlatAffineSectionBassStepEvaluation R) :=
  isStableEquivalence_of_levelwise _
    (boundedAboveFlatAffineSectionBassStepEvaluation_level_isWeakHomotopyEquivalence R)

attribute [colib_tag "COL-0510", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationEquivalence.lean:37-62"
  "adaptation" "Weak or stable equivalence of the original actual affine Bass evaluation map"]
  boundedAboveFlatAffineSectionBassSpanEvaluation_level_isWeakHomotopyEquivalence

attribute [colib_tag "COL-0510", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationEquivalence.lean:65-68"
  "adaptation" "Weak or stable equivalence of the original actual affine Bass evaluation map"]
  boundedAboveFlatAffineSectionBassSpanEvaluation_isStableEquivalence

attribute [colib_tag "COL-0510", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationEquivalence.lean:71-86"
  "adaptation" "Weak or stable equivalence of the original actual affine Bass evaluation map"]
  boundedAboveFlatAffineSectionBassConeEvaluation_level_isWeakHomotopyEquivalence

attribute [colib_tag "COL-0510", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationEquivalence.lean:89-92"
  "adaptation" "Weak or stable equivalence of the original actual affine Bass evaluation map"]
  boundedAboveFlatAffineSectionBassConeEvaluation_isStableEquivalence

attribute [colib_tag "COL-0510", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationEquivalence.lean:95-100"
  "adaptation" "Weak or stable equivalence of the original actual affine Bass evaluation map"]
  boundedAboveFlatAffineSectionBassStepEvaluation_level_isWeakHomotopyEquivalence

attribute [colib_tag "COL-0510", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationEquivalence.lean:103-106"
  "adaptation" "Weak or stable equivalence of the original actual affine Bass evaluation map"]
  boundedAboveFlatAffineSectionBassStepEvaluation_isStableEquivalence

end AlgebraicGeometry.Scheme.Modules
