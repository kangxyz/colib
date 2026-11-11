/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenWeak
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenModel
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetModel
public import Colib.KTheory.Waldhausen.Iterated.ZeroMap
public import Colib.Topology.Prespectrum.MappingCone

/-!
# The original supported-section to relative-open null track

The actual section category with open-detected weak equivalences retains the original chosen
section zero. The literal support inclusion followed by the original change of weaknesses
has the whole nullhomotopy from the actual weak zero-to-section transformation. It descends
to a specified cone map with unchanged target face and cylinder values. Stability of this
section-level descent and comparison with the full open endpoint are separate obligations.
-/
@[expose] public section

open CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS

noncomputable section
open CategoryTheory AlgebraicGeometry Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
open Waldhausen Waldhausen.Fibration Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The entire original weak transformation gives a coherent null track of support restriction. -/
def boundedAboveFlatAffineSupportedSectionOpenNullHomotopy : LoopPrespectrum.Homotopy
    (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j ≫
      boundedAboveFlatAffineSectionOpenPrespectrumMap j)
    (LoopPrespectrum.zeroHom (prespectrum (boundedAboveFlatAffineSupportedSectionModel j))
      (prespectrum (boundedAboveFlatAffineSectionOpenModel j))) := by
  have H := (prespectrumTransformationHomotopy
    (F := zeroHom (boundedAboveFlatAffineSupportedSectionModel j)
      (boundedAboveFlatAffineSectionOpenModel j))
    (G := boundedAboveFlatAffineSupportedSectionForgetModelMap j ≫
      boundedAboveFlatAffineSectionOpenModelMap j)
    (boundedAboveFlatAffineSupportedSectionZeroToOpen j)
    (boundedAboveFlatAffineSupportedSectionZeroToOpen_weak j)).symm
  have he : prespectrumMap (boundedAboveFlatAffineSupportedSectionForgetModelMap j ≫
      boundedAboveFlatAffineSectionOpenModelMap j) =
      boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j ≫
        boundedAboveFlatAffineSectionOpenPrespectrumMap j := prespectrumFunctor.map_comp _ _
  exact {
    level := H.level
    at_zero n x := (H.at_zero n x).trans (congrArg (fun f ↦ f.map n x) he)
    at_one n x := (H.at_one n x).trans (congrArg (fun f ↦ f.map n x)
      (prespectrumMap_zeroHom (boundedAboveFlatAffineSupportedSectionModel j)
        (boundedAboveFlatAffineSectionOpenModel j)))
    at_point := H.at_point
    comm := H.comm }

/-- The original support cone descends to the relative-open section model along this same track. -/
def boundedAboveFlatAffineSupportedSectionOpenConeMap :
    LoopPrespectrum.mappingCone (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j) ⟶
      prespectrum (boundedAboveFlatAffineSectionOpenModel j) :=
  LoopPrespectrum.mappingConeDesc (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j)
    (boundedAboveFlatAffineSectionOpenPrespectrumMap j)
    (boundedAboveFlatAffineSupportedSectionOpenNullHomotopy j)

/-- The original ambient section map is the unchanged target face of the actual cone descent. -/
theorem boundedAboveFlatAffineSupportedSectionOpenConeMap_inclusion :
    LoopPrespectrum.mappingConeInclusion
        (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j) ≫
        boundedAboveFlatAffineSupportedSectionOpenConeMap j =
      boundedAboveFlatAffineSectionOpenPrespectrumMap j :=
  LoopPrespectrum.mappingConeInclusion_desc _ _ _

/-- Every original cone-cylinder value is the specified original section null track. -/
theorem boundedAboveFlatAffineSupportedSectionOpenConeMap_cylinder
    (n : ℕ) (s : unitInterval)
    (x : (prespectrum (boundedAboveFlatAffineSupportedSectionModel j)).space n) :
    (boundedAboveFlatAffineSupportedSectionOpenConeMap j).map n
        (ReducedMappingCone.cylinder
          ((prespectrum (boundedAboveFlatAffineSupportedSectionModel j)).point n)
          ((boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n)
          ((boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j).map n) (s, x)) =
      (boundedAboveFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, x) := rfl

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedSectionOpenNull.lean:54-103"
  "adaptation" "The original reversed weak zero track and its entire cone descent"]
  boundedAboveFlatAffineSupportedSectionOpenNullHomotopy
  boundedAboveFlatAffineSupportedSectionOpenConeMap
  boundedAboveFlatAffineSupportedSectionOpenConeMap_inclusion
  boundedAboveFlatAffineSupportedSectionOpenConeMap_cylinder

end AlgebraicGeometry.Scheme.Modules
