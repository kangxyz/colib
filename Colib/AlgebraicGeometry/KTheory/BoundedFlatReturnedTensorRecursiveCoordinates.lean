/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorRecursiveRecognition

/-! Actual left-recursive stage binding and independent loop/row coordinates. -/
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

/-- Continue the same constructor after its actual first tensor-rooted step. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveCoordinates.lean:23-41"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
def tensorTailFamily (Q : Scheme.{u}) (i : ℕ) :=
  DiagramRowCell.iterateFamily laurent.op coefficient squareFunctor
    (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ))))
    (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ)))) i
    ((strictDiagramFunctor squareFunctor).obj (ParameterModels.ambient Q ⋙ prespectrumFunctor))
    (stage squareFunctor (ParameterModels.ambient Q) 1)
    (stage_point squareFunctor (ParameterModels.ambient Q) 1)
    (stage_naturality squareFunctor (ParameterModels.ambient Q) 1)
    (stage_structure squareFunctor (ParameterModels.ambient Q) 1)
    ((NaturalTrack.ofModelUnits laurent.op coefficient (ParameterModels.ambient Q)
      (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)).bass
      squareFunctor
      (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
        (.of (ULift.{u} ℤ))))
      (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
        (.of (ULift.{u} ℤ)))))
    (tensorStageFamily Q 1)

/-- The chosen next stage is literally the existing left-recursive construction.
This is not a claim that right-associated rawBass at stage i is definitionally stage i+1. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveCoordinates.lean:45-46"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
theorem tensorStage_leftRecursion (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (tensorStageFamily Q (i + 1)).val X = (tensorTailFamily Q i).val X := rfl

/-- The first family passed to that recursion retains the raw successor's full level map;
only endpoint witnesses were changed by the existing step constructor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveCoordinates.lean:50-52"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
theorem tensorStage_firstStep_level (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (n : ℕ) :
    ((tensorStageFamily Q 1).val X).level n =
      (tensorStageRawBass Q 0 X).level n := rfl

/-- At positive levels, the old loop is moved inside the distinguished row, not discarded. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveCoordinates.lean:55-61"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
theorem tensorStage_rawBass_succ (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ)
    (k : ℕ) (r s t : unitInterval) (γ : Path _ _) :
    Path.toContinuousMap (Path.toContinuousMap
      ((tensorStageRawBass Q i X).level (k + 1) (r, γ)) s) t =
    Path.toContinuousMap
      (((tensorStageSquare Q i X).cone.postcomp (tensorStageTransport Q i X)).level
        (k + 1) (r, γ t)) s := rfl

/-- Degree zero retains both row coordinates and the independent original loop coordinate. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveCoordinates.lean:64-70"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
theorem tensorStage_rawBass_zero (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ)
    (u r s t : unitInterval) (γ : Path _ _) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      ((tensorStageRawBass Q i X).level 0 (u, γ)) r) s) t =
    Path.toContinuousMap (Path.toContinuousMap
      (((tensorStageSquare Q i X).cone.postcomp (tensorStageTransport Q i X)).level
        0 (u, γ t)) r) s := rfl

end AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition

namespace AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition

attribute [colib_tag "COL-0558"] tensorStage_leftRecursion
attribute [colib_tag "COL-0558"] tensorStage_firstStep_level
attribute [colib_tag "COL-0558"] tensorStage_rawBass_succ
attribute [colib_tag "COL-0558"] tensorStage_rawBass_zero

end AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition
