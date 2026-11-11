/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageTelescope
noncomputable section
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

example (A : Track laurent.op coefficient F) :
    Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w} :=
  currentTelescope A

example (A : Track laurent.op coefficient F) :
    Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w} :=
  normalizedTelescope A

example (A : Track laurent.op coefficient F) :
    currentTelescope A ⟶ normalizedTelescope A :=
  telescopeMap A

example (A : Track laurent.op coefficient F)
    (X : Scheme.{u}ᵒᵖ) (n i : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj F).obj X).space n) :
    ((telescopeMap A).app X).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj F).obj X)
        (fun j => (currentTransition A j).app X) n i (s, x)) =
    Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
      (fun j => (normalizedTransition A j).app X) n i
      (s, ((stageMap squareFunctor i F).app X).map n x) :=
  telescopeMap_cylinder A X n i s x

example (A : Track laurent.op coefficient F) (i : ℕ) :
    Telescope.diagramInclusion (fun j => (strictDiagramIterate squareFunctor j).obj F)
        (currentTransition A) i ≫ telescopeMap A =
      stageMap squareFunctor i F ≫
        Telescope.diagramInclusion (fun j => normalized squareFunctor j F)
          (normalizedTransition A) i :=
  telescopeMap_inclusion A i

end KTheory.Bass.SchemeNaturalSeed
end
