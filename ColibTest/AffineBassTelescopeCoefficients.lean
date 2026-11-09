/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassTelescope

/-! Whole coefficient laws, cylinder maps and same-time inclusion-homotopy naturality. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u

variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
  (i k : ℕ) (s : unitInterval)

example : boundedAboveFlatAffineSectionBassTelescopeMap (𝟙 R) =
    𝟙 (boundedAboveFlatAffineSectionBassTelescope R) :=
  boundedAboveFlatAffineSectionBassTelescopeMap_id R

example : boundedAboveFlatAffineSectionBassTelescopeMap (f ≫ g) =
    boundedAboveFlatAffineSectionBassTelescopeMap f ≫
      boundedAboveFlatAffineSectionBassTelescopeMap g :=
  boundedAboveFlatAffineSectionBassTelescopeMap_comp f g

example : (boundedAboveFlatAffineSectionBassDiagram i).map f ≫
      (boundedAboveFlatAffineSectionBassTelescopeInclusion i).app S =
    (boundedAboveFlatAffineSectionBassTelescopeInclusion i).app R ≫
      boundedAboveFlatAffineSectionBassTelescopeMap f :=
  (boundedAboveFlatAffineSectionBassTelescopeInclusion i).naturality f

example (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeMap f).map k
      (Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k i (s, x)) =
    Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj S)
      (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app S) k i
      (s, ((boundedAboveFlatAffineSectionBassDiagram i).map f).map k x) :=
  boundedAboveFlatAffineSectionBassTelescopeMap_cylinder f k i s x

example (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeMap f).map k
        ((boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy R i).level k (s, x)) =
      (boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy S i).level k
        (s, ((boundedAboveFlatAffineSectionBassDiagram i).map f).map k x) :=
  Telescope.diagramInclusionHomotopy_naturality_apply _ _ f i k s x
