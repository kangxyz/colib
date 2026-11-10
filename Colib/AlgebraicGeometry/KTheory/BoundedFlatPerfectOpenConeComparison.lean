/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenFibration
public import Colib.KTheory.Waldhausen.Fibration.ConeComparison

/-!
# The original bounded-flat relative-open cone comparison

The actual acyclic support model, its original inclusion and its entire null track give a
stable equivalence to the original relative-open coarse S-prespectrum. All fibration and
point-set hypotheses are discharged by the existing geometric constructions. This endpoint
is the genuine relative-open model: its comparison with all perfect complexes on the open
still retains the honest K₀-image obstruction. Transport to original supported sections is
separate from this acyclic-model statement.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
open Waldhausen Fibration IteratedS
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The original bounded-flat support-acyclic cone descends along its specified null cylinder. -/
def boundedAboveFlatPerfectOpenConeComparison :
    mappingCone (acyclicInclusionPrespectrumMap (boundedAboveFlatPerfectOpenNested j)) ⟶
      originalPrespectrum (boundedAboveFlatPerfectOpenWaldhausen j) :=
  canonicalConePrespectrumMap (boundedAboveFlatPerfectOpenNested j)

/-- Genuine geometric fibration and S-model excision discharge the original stable comparison. -/
theorem boundedAboveFlatPerfectOpenConeComparison_isStableEquivalence :
    IsStableEquivalence (boundedAboveFlatPerfectOpenConeComparison j) :=
  canonicalConePrespectrumMap_isStableEquivalence_of_weak (boundedAboveFlatPerfectOpenNested j)
    (boundedAboveFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j)

/-- The original ambient-to-relative map is the unchanged target face of this cone comparison. -/
theorem boundedAboveFlatPerfectOpenConeComparison_inclusion :
    mappingConeInclusion (acyclicInclusionPrespectrumMap (boundedAboveFlatPerfectOpenNested j)) ≫
        boundedAboveFlatPerfectOpenConeComparison j =
      changeWeakPrespectrumMap (boundedAboveFlatPerfectOpenNested j) :=
  canonicalConePrespectrumMap_inclusion (boundedAboveFlatPerfectOpenNested j)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/OpenConeComparison.lean:31-50"
  "adaptation" "The actual acyclic-model cone comparison, target face and stable equivalence"]
  boundedAboveFlatPerfectOpenConeComparison
  boundedAboveFlatPerfectOpenConeComparison_isStableEquivalence
  boundedAboveFlatPerfectOpenConeComparison_inclusion

end AlgebraicGeometry.Scheme.Modules
