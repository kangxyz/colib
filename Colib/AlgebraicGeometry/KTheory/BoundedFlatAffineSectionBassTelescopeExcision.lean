/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassConeExcision
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassTelescopeCone
public import Colib.Topology.Prespectrum.TelescopeConeExcision

/-!
# Genuine signed cone exactness of the original section Bass telescope

Finite-stage growth and genuine excision, actual cone/telescope interchange, compact stable
representability and filtered exactness prove stable excision for the unchanged telescope
coefficient map. Its boundary is the existing original signed fiber boundary transported by
that same canonical comparison. Every finite-stage boundary is retained by its original cone
inclusion. No uniform telescope connectivity, replacement map or remaining excision premise
appears in these concrete conclusions.
-/
/-! Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassTelescopeExcision.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The original coefficient-map cone-to-fiber comparison of the actual Bass telescope is stable.
-/
theorem boundedAboveFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence :
    IsStableEquivalence
      (mappingConeFiberComparison (boundedAboveFlatAffineSectionBassTelescopeMap f)) :=
  Telescope.coneFiberComparison_isStableEquivalence
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).naturality f)
    (fun i ↦ boundedAboveFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i f)

/-- The unchanged original signed cone boundary, now justified for the actual Bass telescope. -/
def boundedAboveFlatAffineSectionBassTelescopeConeConnecting (d : ℤ) :
    stableHomotopyGroup (mappingCone (boundedAboveFlatAffineSectionBassTelescopeMap f)) (d + 1) ⟶
      stableHomotopyGroup (boundedAboveFlatAffineSectionBassTelescope R) d :=
  stableMappingConeConnecting (boundedAboveFlatAffineSectionBassTelescopeMap f)
    (boundedAboveFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence f) d

/-- Every original finite coefficient-cone stage retains exactly its existing signed boundary.
-/
@[reassoc] theorem boundedAboveFlatAffineSectionBassTelescopeConeConnecting_stage (d : ℤ) (i : ℕ) :
    (stableHomotopyFunctor (d + 1)).map (boundedAboveFlatAffineSectionBassConeStageMap f i) ≫
      boundedAboveFlatAffineSectionBassTelescopeConeConnecting f d =
        stableMappingConeConnecting ((boundedAboveFlatAffineSectionBassDiagram i).map f)
          (boundedAboveFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i f) d ≫
            (stableHomotopyFunctor d).map
              ((boundedAboveFlatAffineSectionBassTelescopeInclusion i).app R) := by
  have he := Telescope.coneStableConnecting_eq_original
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).naturality f)
    (fun i ↦ boundedAboveFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i f) d
  refine (congrArg (fun δ ↦
    (stableHomotopyFunctor (d + 1)).map (boundedAboveFlatAffineSectionBassConeStageMap f i) ≫ δ)
    he).symm.trans ?_
  exact Telescope.coneStableConnecting_stage
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).naturality f)
    (fun i ↦ boundedAboveFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i f) d i

/-- All recurring original cone-sequence positions are exact in every integer degree. -/
theorem boundedAboveFlatAffineSectionBassTelescopeConeLongExactSequence (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d + 1)).map
      (mappingConeInclusion (boundedAboveFlatAffineSectionBassTelescopeMap f)))
      (boundedAboveFlatAffineSectionBassTelescopeConeConnecting f d) ∧
    Function.Exact (boundedAboveFlatAffineSectionBassTelescopeConeConnecting f d)
      ((stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassTelescopeMap f)) ∧
    Function.Exact ((stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassTelescopeMap f))
      ((stableHomotopyFunctor d).map
        (mappingConeInclusion (boundedAboveFlatAffineSectionBassTelescopeMap f))) :=
  stableMappingConeLongExactSequence (boundedAboveFlatAffineSectionBassTelescopeMap f)
    (boundedAboveFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence f) d


attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/\
    SectionBassTelescopeExcision.lean:31-89" "adaptation"
  "Actual telescope cone interchange, signed boundary and exactness with unchanged maps"]
  boundedAboveFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence
  boundedAboveFlatAffineSectionBassTelescopeConeConnecting
  boundedAboveFlatAffineSectionBassTelescopeConeConnecting_stage
  boundedAboveFlatAffineSectionBassTelescopeConeLongExactSequence

attribute [colib_tag "COL-0376"]
  boundedAboveFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence
  boundedAboveFlatAffineSectionBassTelescopeConeConnecting
  boundedAboveFlatAffineSectionBassTelescopeConeConnecting_stage
  boundedAboveFlatAffineSectionBassTelescopeConeLongExactSequence

end AlgebraicGeometry.Scheme.Modules
