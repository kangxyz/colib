/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionOpenNullNaturality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenConeComparison
public import Colib.Topology.Prespectrum.ConeDescNaturality
public import Colib.Topology.Prespectrum.ConeStableNaturality

/-!
# The original supported-section cone comparison

The actual supported-section evaluation and inherited-zero inclusion square identify the
original whole null track with the geometric acyclic track. Genuine S-model excision and
both actual evaluation equivalences therefore prove stability of the unchanged section
cone descent. Its target is the relative-open coarse section model; the full-open K₀-image
endpoint remains separate. The signed boundary retains the specified original fiber lift.
-/
@[expose] public section

open CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS

noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry.RingedSpace Topology
open Waldhausen Waldhausen.Fibration Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual supported evaluation square between the original inclusion arrows. -/
def boundedAboveFlatAffineSupportedSectionOpenInclusionSquare :
    Arrow.mk (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j) ⟶
      Arrow.mk (acyclicInclusionPrespectrumMap (boundedAboveFlatPerfectOpenNested j)) :=
  Arrow.homMk (boundedAboveFlatAffineSupportedSectionAcyclicPrespectrumMap j)
    (boundedAboveFlatAffineEvaluationPrespectrumMap R)
    (boundedAboveFlatAffineSupportedSectionAcyclicPrespectrumMap_inclusion j).symm

/-- The original section cone descent commutes with evaluation on both faces and the whole track. -/
theorem boundedAboveFlatAffineSupportedSectionOpenConeMap_evaluation :
    mappingConeMap (boundedAboveFlatAffineSupportedSectionOpenInclusionSquare j) ≫
        boundedAboveFlatPerfectOpenConeComparison j =
      boundedAboveFlatAffineSupportedSectionOpenConeMap j ≫
        boundedAboveFlatAffineSectionOpenEvaluationPrespectrumMap j :=
  mappingConeDesc_naturality (boundedAboveFlatAffineSupportedSectionOpenInclusionSquare j)
    (boundedAboveFlatAffineSectionOpenPrespectrumMap j)
    (changeWeakPrespectrumMap (boundedAboveFlatPerfectOpenNested j))
    (boundedAboveFlatAffineSectionOpenEvaluationPrespectrumMap j)
    (boundedAboveFlatAffineSupportedSectionOpenNullHomotopy j)
    (acyclicPrespectrumNullhomotopy (boundedAboveFlatPerfectOpenNested j))
    (boundedAboveFlatAffineSectionOpenEvaluation_changeWeak j).symm
    (boundedAboveFlatAffineSupportedSectionOpenNullHomotopy_evaluation j)

/-- Original S-model excision and the actual evaluation equivalences prove cone-map stability. -/
theorem boundedAboveFlatAffineSupportedSectionOpenInclusionSquare_cone_isStableEquivalence :
    IsStableEquivalence (mappingConeMap
      (boundedAboveFlatAffineSupportedSectionOpenInclusionSquare j)) :=
  mappingConeMap_isStableEquivalence_of_excision
    (boundedAboveFlatAffineSupportedSectionOpenInclusionSquare j)
    (prespectrum_mappingConeFiberComparison_isStableEquivalence
      (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j))
    (originalPrespectrum_mappingConeFiberComparison_isStableEquivalence _ _ _)
    (boundedAboveFlatAffineSupportedSectionAcyclic_isStableEquivalence j)
    (boundedAboveFlatAffineEvaluationPrespectrumMap_isStableEquivalence R)

/-- The unchanged supported-section cone descent is an equivalence in every signed stable degree. -/
theorem boundedAboveFlatAffineSupportedSectionOpenConeMap_isStableEquivalence :
    IsStableEquivalence (boundedAboveFlatAffineSupportedSectionOpenConeMap j) := by
  have hc :=
    (boundedAboveFlatAffineSupportedSectionOpenInclusionSquare_cone_isStableEquivalence j).comp
    (boundedAboveFlatPerfectOpenConeComparison_isStableEquivalence j)
  rw [boundedAboveFlatAffineSupportedSectionOpenConeMap_evaluation] at hc
  intro d
  let := boundedAboveFlatAffineSectionOpenEvaluation_isStableEquivalence j d
  have hd := hc d
  rw [Functor.map_comp] at hd
  exact (isIso_comp_right_iff _ _).mp hd

/-- The original signed cone boundary equals the actual relative-open fiber boundary. -/
theorem boundedAboveFlatAffineSupportedSectionOpenConeMap_connecting (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (boundedAboveFlatAffineSupportedSectionOpenConeMap j) ≫
        stableFiberConnecting (boundedAboveFlatAffineSectionOpenPrespectrumMap j) d =
      stableMappingConeConnecting (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j)
          (prespectrum_mappingConeFiberComparison_isStableEquivalence
            (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j)) d ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberLift (boundedAboveFlatAffineSectionOpenPrespectrumMap j)
            (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j)
            (boundedAboveFlatAffineSupportedSectionOpenNullHomotopy j)) :=
  mappingConeDesc_connecting _ _ _ _ d

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    SupportedSectionOpenConeComparison.lean:36-92"
  "adaptation" "Actual supported-section comparison with its specified entire null track"]
  boundedAboveFlatAffineSupportedSectionOpenInclusionSquare
  boundedAboveFlatAffineSupportedSectionOpenConeMap_evaluation
  boundedAboveFlatAffineSupportedSectionOpenInclusionSquare_cone_isStableEquivalence
  boundedAboveFlatAffineSupportedSectionOpenConeMap_isStableEquivalence
  boundedAboveFlatAffineSupportedSectionOpenConeMap_connecting

attribute [colib_tag "COL-0509"]
  boundedAboveFlatAffineSupportedSectionOpenConeMap_evaluation
  boundedAboveFlatAffineSupportedSectionOpenConeMap_isStableEquivalence
  boundedAboveFlatAffineSupportedSectionOpenConeMap_connecting

end AlgebraicGeometry.Scheme.Modules
