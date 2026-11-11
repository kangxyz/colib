/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.KTheory.Bass.GeneratedTensorTraceProof
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorGenerators

/-! The actual returned tensor input generates every original finite cell by the recipe. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition
open GlobalSectionChangeIndex ParameterTensorEvaluationRow ModelDiagramRowInterchange
open GlobalSupportedSection GeometricSquareInterchange TensorGeneratedRecipe

/-- Every actual tensor-started finite cell has a generator-defined trace.
All naturality, endpoint, index and row data are instantiated, not hypotheses. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorGeneratedTrace.lean:24-36"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
theorem tensor_generated_trace (Q : Scheme.{u}) (i : ℕ) :
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
  iterateFamily_generated _ _ _ _ _ _ _ _ _ _ _ _ _

end AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition

namespace AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition

attribute [colib_tag "COL-0558"] tensor_generated_trace

end AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition
