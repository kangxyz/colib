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

variable {A B : Arrow CommRingCat.{u}} (sq : A ⟶ B) (d : ℤ)

example : (stableHomotopyFunctor (d + 1)).map
    (boundedAboveFlatAffineSectionBassTelescopeConeMap sq) ≫
    boundedAboveFlatAffineSectionBassTelescopeConeConnecting B.hom d =
    boundedAboveFlatAffineSectionBassTelescopeConeConnecting A.hom d ≫
      (stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassTelescopeMap sq.left) :=
  boundedAboveFlatAffineSectionBassTelescopeConeConnecting_naturality sq d

example (hl : IsStableEquivalence (boundedAboveFlatAffineSectionBassTelescopeMap sq.left))
    (hr : IsStableEquivalence (boundedAboveFlatAffineSectionBassTelescopeMap sq.right)) :
    IsStableEquivalence (boundedAboveFlatAffineSectionBassTelescopeConeMap sq) :=
  boundedAboveFlatAffineSectionBassTelescopeConeMap_isStableEquivalence sq hl hr

example (k : ℕ)
    (x : (boundedAboveFlatAffineSectionBassTelescope A.left).space k)
    (s : unitInterval) :
    (boundedAboveFlatAffineSectionBassTelescopeConeMap sq).map k
      (ReducedMappingCone.cylinder
        ((boundedAboveFlatAffineSectionBassTelescope A.left).point k)
        ((boundedAboveFlatAffineSectionBassTelescope A.right).point k)
        ((boundedAboveFlatAffineSectionBassTelescopeMap A.hom).map k) (s, x)) =
      ReducedMappingCone.cylinder
        ((boundedAboveFlatAffineSectionBassTelescope B.left).point k)
        ((boundedAboveFlatAffineSectionBassTelescope B.right).point k)
        ((boundedAboveFlatAffineSectionBassTelescopeMap B.hom).map k)
        (s, (boundedAboveFlatAffineSectionBassTelescopeMap sq.left).map k x) := rfl

-- The target face uses the right side of the square and preserves its telescope height.
example (k i : ℕ) (t : unitInterval)
    (y : ((boundedAboveFlatAffineSectionBassDiagram i).obj A.right).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeConeMap sq).map k
      ((mappingConeInclusion (boundedAboveFlatAffineSectionBassTelescopeMap A.hom)).map k
        (Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj A.right)
          (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app A.right) k i (t, y))) =
      (mappingConeInclusion (boundedAboveFlatAffineSectionBassTelescopeMap B.hom)).map k
        (Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj B.right)
          (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app B.right) k i
          (t, ((boundedAboveFlatAffineSectionBassDiagram i).map sq.right).map k y)) := rfl

-- The source double cylinder retains independent cone time and telescope height.
example (k i : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj A.left).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeConeMap sq).map k
      (ReducedMappingCone.cylinder
        ((boundedAboveFlatAffineSectionBassTelescope A.left).point k)
        ((boundedAboveFlatAffineSectionBassTelescope A.right).point k)
        ((boundedAboveFlatAffineSectionBassTelescopeMap A.hom).map k)
        (s, Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj A.left)
          (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app A.left) k i (t, x))) =
      ReducedMappingCone.cylinder
        ((boundedAboveFlatAffineSectionBassTelescope B.left).point k)
        ((boundedAboveFlatAffineSectionBassTelescope B.right).point k)
        ((boundedAboveFlatAffineSectionBassTelescopeMap B.hom).map k)
        (s, Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj B.left)
          (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app B.left) k i
          (t, ((boundedAboveFlatAffineSectionBassDiagram i).map sq.left).map k x)) := rfl
