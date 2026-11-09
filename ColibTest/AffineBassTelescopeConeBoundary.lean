/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassTelescopeNaturality

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
open scoped unitInterval
noncomputable section
universe u

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (d : ℤ) (i : ℕ)

example : (stableHomotopyFunctor (d + 1)).map
    (boundedAboveFlatAffineSectionBassConeStageMap f i) ≫
    boundedAboveFlatAffineSectionBassTelescopeConeConnecting f d =
    stableMappingConeConnecting ((boundedAboveFlatAffineSectionBassDiagram i).map f)
      (boundedAboveFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i f) d ≫
      (stableHomotopyFunctor d).map
        ((boundedAboveFlatAffineSectionBassTelescopeInclusion i).app R) :=
  boundedAboveFlatAffineSectionBassTelescopeConeConnecting_stage f d i

example : colimit.ι (Telescope.stageStableDiagram
    (fun i ↦ mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f))
    (boundedAboveFlatAffineSectionBassConeTransition f) d) i ≫
    (boundedAboveFlatAffineSectionBassTelescopeConeStableColimitIso f d).hom =
    (stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassConeStageMap f i) :=
  boundedAboveFlatAffineSectionBassTelescopeConeStableColimitIso_ι_hom f d i

example (x : stableHomotopyGroup
    (mappingCone (boundedAboveFlatAffineSectionBassTelescopeMap f)) d) :
    ∃ i : ℕ, ∃ z : stableHomotopyGroup
      (mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f)) d,
      (stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassConeStageMap f i) z = x :=
  boundedAboveFlatAffineSectionBassTelescopeCone_exists_stable_representative f d x
