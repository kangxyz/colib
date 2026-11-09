/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassTelescopeCone

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
open scoped unitInterval
noncomputable section
universe u

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (k i : ℕ) (s t r : unitInterval)

private abbrev sourceTower (R : CommRingCat.{u}) (i : ℕ) :=
  (boundedAboveFlatAffineSectionBassDiagram i).obj R
private abbrev sourceTransition (R : CommRingCat.{u}) (i : ℕ) :=
  (boundedAboveFlatAffineSectionBassTransition i).app R

example (x : (sourceTower R i).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeConeIso f).hom.map k
      (ReducedMappingCone.cylinder
        ((boundedAboveFlatAffineSectionBassTelescope R).point k)
        ((boundedAboveFlatAffineSectionBassTelescope S).point k)
        ((boundedAboveFlatAffineSectionBassTelescopeMap f).map k)
        (s, Telescope.cylinder (sourceTower R) (sourceTransition R) k i (t, x))) =
      Telescope.cylinder (fun i ↦ mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f))
        (boundedAboveFlatAffineSectionBassConeTransition f) k i
        (t, ReducedMappingCone.cylinder ((sourceTower R i).point k) ((sourceTower S i).point k)
          (((boundedAboveFlatAffineSectionBassDiagram i).map f).map k) (s, x)) := rfl

example (x : (sourceTower R i).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeConeIso f).inv.map k
      (Telescope.cylinder (fun i ↦ mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f))
        (boundedAboveFlatAffineSectionBassConeTransition f) k i
        (t, ReducedMappingCone.cylinder ((sourceTower R i).point k) ((sourceTower S i).point k)
          (((boundedAboveFlatAffineSectionBassDiagram i).map f).map k) (s, x))) =
      ReducedMappingCone.cylinder
        ((boundedAboveFlatAffineSectionBassTelescope R).point k)
        ((boundedAboveFlatAffineSectionBassTelescope S).point k)
        ((boundedAboveFlatAffineSectionBassTelescopeMap f).map k)
        (s, Telescope.cylinder (sourceTower R) (sourceTransition R) k i (t, x)) := rfl

example (y : (sourceTower S i).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeConeIso f).inv.map k
      (Telescope.cylinder (fun i ↦ mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f))
        (boundedAboveFlatAffineSectionBassConeTransition f) k i
        (t, (mappingConeInclusion ((boundedAboveFlatAffineSectionBassDiagram i).map f)).map k y)) =
      (mappingConeInclusion (boundedAboveFlatAffineSectionBassTelescopeMap f)).map k
        (Telescope.cylinder (sourceTower S) (sourceTransition S) k i (t, y)) := rfl

example (y : (sourceTower S i).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeConeIso f).hom.map k
      ((mappingConeInclusion (boundedAboveFlatAffineSectionBassTelescopeMap f)).map k
        (Telescope.cylinder (sourceTower S) (sourceTransition S) k i (t, y))) =
      Telescope.cylinder (fun i ↦ mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f))
        (boundedAboveFlatAffineSectionBassConeTransition f) k i
        (t, (mappingConeInclusion ((boundedAboveFlatAffineSectionBassDiagram i).map f)).map k y) := rfl

example (q : (mappingCone (boundedAboveFlatAffineSectionBassTelescopeMap f)).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeConeIso f).inv.map k
      ((boundedAboveFlatAffineSectionBassTelescopeConeIso f).hom.map k q) = q :=
  congrArg (fun a ↦ a.map k q) (boundedAboveFlatAffineSectionBassTelescopeConeIso f).hom_inv_id

example (q : (Telescope.prespectrum
    (fun i ↦ mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f))
    (boundedAboveFlatAffineSectionBassConeTransition f)).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeConeIso f).hom.map k
      ((boundedAboveFlatAffineSectionBassTelescopeConeIso f).inv.map k q) = q :=
  congrArg (fun a ↦ a.map k q) (boundedAboveFlatAffineSectionBassTelescopeConeIso f).inv_hom_id

-- Three independent coordinates: cone time s, telescope height t, and structure-loop time r.
example (x : (sourceTower R i).space k) :
    (mappingCone (boundedAboveFlatAffineSectionBassTelescopeMap f)).structureMap k
      (ReducedMappingCone.cylinder
        ((boundedAboveFlatAffineSectionBassTelescope R).point k)
        ((boundedAboveFlatAffineSectionBassTelescope S).point k)
        ((boundedAboveFlatAffineSectionBassTelescopeMap f).map k)
        (s, Telescope.cylinder (sourceTower R) (sourceTransition R) k i (t, x))) r =
      ReducedMappingCone.cylinder
        ((boundedAboveFlatAffineSectionBassTelescope R).point (k + 1))
        ((boundedAboveFlatAffineSectionBassTelescope S).point (k + 1))
        ((boundedAboveFlatAffineSectionBassTelescopeMap f).map (k + 1))
        (s, Telescope.cylinder (sourceTower R) (sourceTransition R) (k + 1) i
          (t, (sourceTower R i).structureMap k x r)) := rfl

open CategoryTheory.Waldhausen.IteratedS
example (x : Path (stagePoint 0 (boundedAboveFlatAffineSectionModel R))
    (stagePoint 0 (boundedAboveFlatAffineSectionModel R))) :
    (mappingCone (boundedAboveFlatAffineSectionBassTelescopeMap f)).structureMap 0
      (ReducedMappingCone.cylinder
        ((boundedAboveFlatAffineSectionBassTelescope R).point 0)
        ((boundedAboveFlatAffineSectionBassTelescope S).point 0)
        ((boundedAboveFlatAffineSectionBassTelescopeMap f).map 0)
        (s, Telescope.cylinder (sourceTower R) (sourceTransition R) 0 0 (t, x))) r =
      ReducedMappingCone.cylinder
        ((boundedAboveFlatAffineSectionBassTelescope R).point 1)
        ((boundedAboveFlatAffineSectionBassTelescope S).point 1)
        ((boundedAboveFlatAffineSectionBassTelescopeMap f).map 1)
        (s, Telescope.cylinder (sourceTower R) (sourceTransition R) 1 0 (t, x r)) := rfl
