/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassTower

/-! Actual tower identities and arbitrary coefficient maps; no supplied seed or flatness. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u

variable (n k : ℕ) {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)

example : boundedAboveFlatAffineSectionBassDiagram.{u} 0 =
    boundedAboveFlatAffineSectionPrespectrumFunctor := rfl

example : boundedAboveFlatAffineSectionBassDiagram.{u} 1 =
    KTheory.Bass.strictRingDiagramFunctor.obj
      boundedAboveFlatAffineSectionPrespectrumFunctor := rfl

example : boundedAboveFlatAffineSectionBassDiagram.{u} (n + 1) =
    (KTheory.Bass.strictRingDiagramIterate n).obj
      (KTheory.Bass.strictRingDiagramFunctor.obj
        boundedAboveFlatAffineSectionPrespectrumFunctor) := rfl

example : boundedAboveFlatAffineSectionBassTransition.{u} 0 =
    boundedAboveFlatAffineSectionBassSeed := rfl

example : boundedAboveFlatAffineSectionBassTransition.{u} n =
    (KTheory.Bass.strictRingDiagramIterate n).map
      boundedAboveFlatAffineSectionBassSeed := rfl

example : (boundedAboveFlatAffineSectionBassDiagram n).map (𝟙 R) =
    𝟙 ((boundedAboveFlatAffineSectionBassDiagram n).obj R) :=
  (boundedAboveFlatAffineSectionBassDiagram n).map_id R

example : (boundedAboveFlatAffineSectionBassDiagram n).map (f ≫ g) =
    (boundedAboveFlatAffineSectionBassDiagram n).map f ≫
      (boundedAboveFlatAffineSectionBassDiagram n).map g :=
  (boundedAboveFlatAffineSectionBassDiagram n).map_comp f g

example : (boundedAboveFlatAffineSectionBassDiagram n).map f ≫
      (boundedAboveFlatAffineSectionBassTransition n).app S =
    (boundedAboveFlatAffineSectionBassTransition n).app R ≫
      (boundedAboveFlatAffineSectionBassDiagram (n + 1)).map f :=
  boundedAboveFlatAffineSectionBassTransition_naturality n f

example (x : ((boundedAboveFlatAffineSectionBassDiagram n).obj R).space k) :
    ((boundedAboveFlatAffineSectionBassTransition n).app S).map k
      (((boundedAboveFlatAffineSectionBassDiagram n).map f).map k x) =
    ((boundedAboveFlatAffineSectionBassDiagram (n + 1)).map f).map k
      (((boundedAboveFlatAffineSectionBassTransition n).app R).map k x) :=
  boundedAboveFlatAffineSectionBassTransition_naturality_apply n k f x
