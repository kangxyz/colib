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

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (d : ℤ)

example : IsStableEquivalence
    (mappingConeFiberComparison (boundedAboveFlatAffineSectionBassTelescopeMap f)) :=
  boundedAboveFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence f

example : Function.Exact ((stableHomotopyFunctor (d + 1)).map
    (mappingConeInclusion (boundedAboveFlatAffineSectionBassTelescopeMap f)))
    (boundedAboveFlatAffineSectionBassTelescopeConeConnecting f d) :=
  (boundedAboveFlatAffineSectionBassTelescopeConeLongExactSequence f d).1

example : Function.Exact (boundedAboveFlatAffineSectionBassTelescopeConeConnecting f d)
    ((stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassTelescopeMap f)) :=
  (boundedAboveFlatAffineSectionBassTelescopeConeLongExactSequence f d).2.1

example : Function.Exact
    ((stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassTelescopeMap f))
    ((stableHomotopyFunctor d).map
      (mappingConeInclusion (boundedAboveFlatAffineSectionBassTelescopeMap f))) :=
  (boundedAboveFlatAffineSectionBassTelescopeConeLongExactSequence f d).2.2

example : IsIso ((stableHomotopyFunctor (-1)).map
    (mappingConeFiberComparison (boundedAboveFlatAffineSectionBassTelescopeMap f))) :=
  boundedAboveFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence f (-1)

example : IsIso ((stableHomotopyFunctor 0).map
    (mappingConeFiberComparison (boundedAboveFlatAffineSectionBassTelescopeMap f))) :=
  boundedAboveFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence f 0

example : IsIso ((stableHomotopyFunctor 1).map
    (mappingConeFiberComparison (boundedAboveFlatAffineSectionBassTelescopeMap f))) :=
  boundedAboveFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence f 1

example (k i : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :
    (((mappingConeFiberComparison (boundedAboveFlatAffineSectionBassTelescopeMap f)).map k
      (Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k i (t, x))).1.2 s) =
      ReducedMappingCone.cylinder
        ((boundedAboveFlatAffineSectionBassTelescope R).point k)
        ((boundedAboveFlatAffineSectionBassTelescope S).point k)
        ((boundedAboveFlatAffineSectionBassTelescopeMap f).map k)
        (s, Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
          (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k i (t, x)) := rfl
