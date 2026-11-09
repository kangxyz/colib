/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassTelescope

/-! Literal quotient endpoints, collapsed rays and original inclusion homotopies. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u

variable (R : CommRingCat.{u}) (i k : ℕ) (s : unitInterval)

example (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :
    Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k i (1, x) =
      Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k (i + 1)
        (0, ((boundedAboveFlatAffineSectionBassTransition i).app R).map k x) :=
  Telescope.cylinder_one
    (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
    (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k i x

example :
    Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k i
        (s, ((boundedAboveFlatAffineSectionBassDiagram i).obj R).point k) =
      (boundedAboveFlatAffineSectionBassTelescope R).point k :=
  Telescope.cylinder_point
    (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
    (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k i s

example (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :
    ((boundedAboveFlatAffineSectionBassTelescopeInclusion i).app R).map k x =
      Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k i (0, x) := rfl

example (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy R i).level k (s, x) =
      Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k i (s, x) := rfl

example (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy R i).level k (0, x) =
      ((boundedAboveFlatAffineSectionBassTelescopeInclusion i).app R).map k x :=
  (boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy R i).at_zero k x

example (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy R i).level k (1, x) =
      ((boundedAboveFlatAffineSectionBassTelescopeInclusion (i + 1)).app R).map k
        (((boundedAboveFlatAffineSectionBassTransition i).app R).map k x) :=
  (boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy R i).at_one k x

example : (boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy R i).level k
      (s, ((boundedAboveFlatAffineSectionBassDiagram i).obj R).point k) =
    (boundedAboveFlatAffineSectionBassTelescope R).point k :=
  (boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy R i).at_point k s
