/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageSquare
public import Colib.Topology.Prespectrum.TelescopeDiagramMap

/-! # The actual current-stage to normalized telescope map

The whole commuting stage square gives the same telescope map on each original cylinder,
including its full height. Stability of this map is a separate original result, not assumed here.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open scoped unitInterval
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap FiniteConeTopology
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The actual finite Bass objects with their current-stage seeds. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeCurrentStageTelescope.lean:28"
  "adaptation" "Original actual telescope map retaining full cylinder height."]
def currentTelescope (A : Track laurent.op coefficient F) :
    Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w} :=
  Telescope.diagramFunctor (fun i => (strictDiagramIterate squareFunctor i).obj F)
    (currentTransition A)

/-- The unpermuted cone-normalized objects with their literal looped current cone seeds. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeCurrentStageTelescope.lean:34"
  "adaptation" "Original actual telescope map retaining full cylinder height."]
def normalizedTelescope (A : Track laurent.op coefficient F) :
    Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w} :=
  Telescope.diagramFunctor (fun i => normalized squareFunctor i F) (normalizedTransition A)

/-- The existing finite stage maps descend to a natural map of these two actual telescopes. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeCurrentStageTelescope.lean:39"
  "adaptation" "Original actual telescope map retaining full cylinder height."]
def telescopeMap (A : Track laurent.op coefficient F) :
    currentTelescope A ⟶ normalizedTelescope A :=
  Telescope.diagramMap (fun i => (strictDiagramIterate squareFunctor i).obj F)
    (fun i => normalized squareFunctor i F) (currentTransition A) (normalizedTransition A)
    (fun i => stageMap squareFunctor i F) (fun i => (currentTransition_stageMap A i).symm)

/-- Every original telescope cylinder keeps its stage and entire height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeCurrentStageTelescope.lean:46"
  "adaptation" "Original actual telescope map retaining full cylinder height."]
theorem telescopeMap_cylinder (A : Track laurent.op coefficient F)
    (X : Scheme.{u}ᵒᵖ) (n i : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj F).obj X).space n) :
    ((telescopeMap A).app X).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj F).obj X)
        (fun j => (currentTransition A j).app X) n i (s, x)) =
    Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
      (fun j => (normalizedTransition A j).app X) n i
      (s, ((stageMap squareFunctor i F).app X).map n x) :=
  Telescope.diagramMap_cylinder
    (fun j => (strictDiagramIterate squareFunctor j).obj F)
    (fun j => normalized squareFunctor j F) (currentTransition A) (normalizedTransition A)
    (fun j => stageMap squareFunctor j F)
    (fun j => (currentTransition_stageMap A j).symm) X n i s x

/-- Original finite-stage inclusions commute with the same telescope map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeCurrentStageTelescope.lean:62"
  "adaptation" "Original actual telescope map retaining full cylinder height."]
theorem telescopeMap_inclusion (A : Track laurent.op coefficient F) (i : ℕ) :
    Telescope.diagramInclusion (fun j => (strictDiagramIterate squareFunctor j).obj F)
        (currentTransition A) i ≫ telescopeMap A =
      stageMap squareFunctor i F ≫
        Telescope.diagramInclusion (fun j => normalized squareFunctor j F)
          (normalizedTransition A) i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

end KTheory.Bass.SchemeNaturalSeed
