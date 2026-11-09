/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassTelescope

/-! Independent cylinder and structure times, including actual level-zero path inputs. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u

open CategoryTheory.Waldhausen.IteratedS
variable (R : CommRingCat.{u}) (i k : ℕ) (s t : unitInterval)

example (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :
    (boundedAboveFlatAffineSectionBassTelescope R).structureMap k
      (Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k i (s, x)) t =
    Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
      (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) (k + 1) i
      (s, ((boundedAboveFlatAffineSectionBassDiagram i).obj R).structureMap k x t) := rfl

-- Only the original level-zero input is evaluated as a path, never a quotient point.
example (x : Path (stagePoint 0 (boundedAboveFlatAffineSectionModel R))
    (stagePoint 0 (boundedAboveFlatAffineSectionModel R))) (r : unitInterval) :
    (boundedAboveFlatAffineSectionBassTelescope R).structureMap 0
      (Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) 0 0 (s, x)) r =
    Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
      (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) 1 0 (s, x r) := rfl

example (x : Path (stagePoint 0 (boundedAboveFlatAffineSectionModel R))
    (stagePoint 0 (boundedAboveFlatAffineSectionModel R))) :
    (boundedAboveFlatAffineSectionBassTelescopeInitial.app R).map 0 x =
      Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) 0 0 (0, x) := rfl
