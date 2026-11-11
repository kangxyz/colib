/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionOpenConeComparison

/-! Actual original support, null-track and signed-boundary consumers. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
universe u
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

-- All integer degrees, not merely nonnegative or connected components.
example (d : ℤ) : IsIso ((stableHomotopyFunctor d).map
    (boundedAboveFlatAffineSupportedSectionOpenConeMap j)) :=
  boundedAboveFlatAffineSupportedSectionOpenConeMap_isStableEquivalence j d

example : IsIso ((stableHomotopyFunctor (-1)).map
    (boundedAboveFlatAffineSupportedSectionOpenConeMap j)) :=
  boundedAboveFlatAffineSupportedSectionOpenConeMap_isStableEquivalence j (-1)

-- The original target face is literal, not replaced by an unspecified equivalent map.
example : mappingConeInclusion (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j) ≫
    boundedAboveFlatAffineSupportedSectionOpenConeMap j =
      boundedAboveFlatAffineSectionOpenPrespectrumMap j :=
  boundedAboveFlatAffineSupportedSectionOpenConeMap_inclusion j

-- Every specified time slice is preserved, including the original degree-zero based loops.
example (n : ℕ) (s : unitInterval)
    (x : (prespectrum (boundedAboveFlatAffineSupportedSectionModel j)).space n) :
    (boundedAboveFlatAffineSectionOpenEvaluationPrespectrumMap j).map n
        ((boundedAboveFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, x)) =
      (Fibration.acyclicPrespectrumNullhomotopy (boundedAboveFlatPerfectOpenNested j)).level n
        (s, (boundedAboveFlatAffineSupportedSectionAcyclicPrespectrumMap j).map n x) :=
  boundedAboveFlatAffineSupportedSectionOpenNullHomotopy_evaluation j n s x

-- Both faces and the full original cone cylinder commute under actual evaluation.
example : mappingConeMap (boundedAboveFlatAffineSupportedSectionOpenInclusionSquare j) ≫
    boundedAboveFlatPerfectOpenConeComparison j =
      boundedAboveFlatAffineSupportedSectionOpenConeMap j ≫
        boundedAboveFlatAffineSectionOpenEvaluationPrespectrumMap j :=
  boundedAboveFlatAffineSupportedSectionOpenConeMap_evaluation j

-- The signed connecting map uses exactly the original null track's fiber lift.
example (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (boundedAboveFlatAffineSupportedSectionOpenConeMap j) ≫
        stableFiberConnecting (boundedAboveFlatAffineSectionOpenPrespectrumMap j) d =
      stableMappingConeConnecting (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j)
          (prespectrum_mappingConeFiberComparison_isStableEquivalence
            (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j)) d ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberLift (boundedAboveFlatAffineSectionOpenPrespectrumMap j)
            (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j)
            (boundedAboveFlatAffineSupportedSectionOpenNullHomotopy j)) :=
  boundedAboveFlatAffineSupportedSectionOpenConeMap_connecting j d
