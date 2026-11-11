/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorRecursiveCoordinates
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowCurrentBoundary

/-! The original whole tensor boundary comparison and specified backward transport. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition
open GlobalSectionChangeIndex ModelDiagramRowInterchange ParameterTensorEvaluationRow
open GlobalSupportedSection GeometricSquareInterchange
/-- The original normalization and Laurent boundary give the whole current forward homotopy
at every tensor-rooted stage; its cone null is the original one, not a replacement. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveRecognition.lean:103-106"
  "adaptation" "Original whole boundary homotopy and specified successor transport."]
def tensorStageBoundaryCurrentHomotopy (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  (SchemeModelRowSeed.normalizedBoundaryCurrentHomotopy (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    i X).cast (strictifiedNormalizedForward_eq Q i X).symm rfl


/-- The precise successor transport and looped row comparison in the boundary target.
The underlying backward map is the suspension unit followed by the counit/row refinement. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveCoordinates.lean:74-79"
  "adaptation" "Original whole boundary homotopy and specified successor transport."]
theorem tensorStage_backward_eq (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    ModelRowZigzagSequentialization.backward squareFunctor (ParameterModels.ambient Q) X i =
      eqToHom (ModelDiagramSuspension.successor_obj squareFunctor i (ParameterModels.ambient Q) X) ≫
        parameterLoopingMap
          (ModelDiagramRowRefinement.comparison squareFunctor i (ParameterModels.ambient Q) X) :=
  ModelRowZigzagSequentialization.backward_eq _ _ _ _


end AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition

namespace AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition

attribute [colib_tag "COL-0558"] tensorStageBoundaryCurrentHomotopy
attribute [colib_tag "COL-0558"] tensorStage_backward_eq

end AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition
