/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorGeneratedTrace
import Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorRecursiveCoordinates
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition
open AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open ModelDiagramRowInterchange GeometricSquareInterchange TensorGeneratedRecipe
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
noncomputable section

example (Q : Scheme.{u}) (i : ℕ) :
    GeneratedTrace laurent.op coefficient squareFunctor
      (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
        (.of (ULift.{u} ℤ))))
      (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
        (.of (ULift.{u} ℤ)))) i (ParameterModels.ambient Q ⋙ prespectrumFunctor)
      (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
      (initial_naturality (ParameterModels.ambient Q))
      (initial_structure (ParameterModels.ambient Q))
      (NaturalTrack.ofModelUnits laurent.op coefficient (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q))
      (tensorFamily Q) (strictifiedIteratedCell Q i) :=
  tensor_generated_trace Q i

example (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (tensorStageFamily Q i).val X = strictifiedIteratedCell Q i X :=
  tensorStageFamily_cell Q i X

example (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ)
    (K : Homotopy _ _)
    (h : StrictSquare.MapHomotopy.ConeGeneratorLaw (tensorStageSquare Q i X) K) :
    ((K.postcomp (tensorStageTransport Q i X)).parameterLooping).postcomp
        (tensorStageLoopRowInverse Q i X) =
      tensorStageRawBass Q i X :=
  tensorStage_successor_unique Q i X K h

example (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (tensorStageFamily Q (i + 1)).val X = (tensorTailFamily Q i).val X :=
  tensorStage_leftRecursion Q i X

example (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ)
    (k : ℕ) (r s t : unitInterval) (γ : Path _ _) :
    Path.toContinuousMap (Path.toContinuousMap
      ((tensorStageRawBass Q i X).level (k + 1) (r, γ)) s) t =
    Path.toContinuousMap
      (((tensorStageSquare Q i X).cone.postcomp (tensorStageTransport Q i X)).level
        (k + 1) (r, γ t)) s :=
  tensorStage_rawBass_succ Q i X k r s t γ

example (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ)
    (u r s t : unitInterval) (γ : Path _ _) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      ((tensorStageRawBass Q i X).level 0 (u, γ)) r) s) t =
    Path.toContinuousMap (Path.toContinuousMap
      (((tensorStageSquare Q i X).cone.postcomp (tensorStageTransport Q i X)).level
        0 (u, γ t)) r) s :=
  tensorStage_rawBass_zero Q i X u r s t γ
