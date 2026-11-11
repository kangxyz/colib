/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorBoundaryRecognition

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition.Tests
open GlobalSectionChangeIndex ModelDiagramRowInterchange ParameterTensorEvaluationRow
open GlobalSupportedSection GeometricSquareInterchange

example (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    ModelRowZigzagSequentialization.backward squareFunctor (ParameterModels.ambient Q) X i =
      eqToHom (ModelDiagramSuspension.successor_obj squareFunctor i (ParameterModels.ambient Q) X) ≫
        parameterLoopingMap
          (ModelDiagramRowRefinement.comparison squareFunctor i (ParameterModels.ambient Q) X) :=
  tensorStage_backward_eq Q i X

example (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    Homotopy (strictifiedNormalizedForward Q i X)
      ((SchemeNaturalSeed.currentTransition
        (NaturalTrack.ofModelUnits laurent.op coefficient (ParameterModels.ambient Q)
          (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q))
          i).app X ≫
        ModelRowZigzagSequentialization.backward squareFunctor (ParameterModels.ambient Q) X i) :=
  tensorStageBoundaryCurrentHomotopy Q i X

end AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition.Tests
