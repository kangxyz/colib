/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorCell
public import Colib.KTheory.Bass.ModelUnitRowCell
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationSpectrumNaturality

/-! # The literal ambient parameter first-row cell and its evaluation

The internal cell is independently realized from the actual Model unit. Exact evaluation
identifies its whole image with the internal edge of the genuine tensor-unitor prism.
That prism retains the evaluation pseudonaturality path and both zero normalizations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open KTheory.Bass Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex GlobalSupportedSection

/-- The original ambient parameter Model's independently realized first-row cell. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorInitialCell.lean:32"
  "adaptation" "Original full first-row cell and exact evaluation at unchanged time."]
def initialCell (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  ModelDiagramRowInterchange.initialCell laurent.op coefficient (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) X

/-- Its whole comparison uses the original ambient track without changing its time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorInitialCell.lean:37"
  "adaptation" "Original full first-row cell and exact evaluation at unchanged time."]
theorem initialCell_eq (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    initialCell Q X = ((ParameterLaurentTrack.ambientTrack Q).homotopy X).postcomp
      (RowRefinement.comparison
        (prespectrum ((ParameterModels.ambient Q).obj (laurent.op.obj X)))
        (ModelDiagramRowInterchange.initial (ParameterModels.ambient Q) (laurent.op.obj X))
        (ModelDiagramRowInterchange.initial_point (ParameterModels.ambient Q) (laurent.op.obj X))
        (ModelDiagramRowInterchange.initial_structure
          (ParameterModels.ambient Q) (laurent.op.obj X))) :=
  ModelDiagramRowInterchange.initialCell_eq laurent.op coefficient (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) X

/-- Exact evaluation identifies the complete internal edge of the tensor comparison prism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorInitialCell.lean:49"
  "adaptation" "Original full first-row cell and exact evaluation at unchanged time."]
theorem internalCell_evaluation_at (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (t : unitInterval) :
    (rowTransformationSpectrumHomotopy (internalModelUnit Q X)
      (internalModelUnit_weak Q X)).at t =
    (initialCell Q X).at t ≫
      rowLoopMap (evaluationModel (op (scheme Q (laurent.op.obj X)))) := by
  exact rowTransformationSpectrumHomotopy_postcomp_at
    (onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op).hom.toFunctor
      (boundedAboveFlatGlobalSectionUnit (op (scheme Q (laurent.op.obj X)))
        (ParameterLaurentUnit.projectedLaurentScalar Q X))).hom
    (fun _ => (boundedAboveFlatGlobalSectionModelFunctor.obj
      (op (scheme Q (laurent.op.obj X)))).obj.waldhausen.weq_iso _ inferInstance)
    (evaluationModel (op (scheme Q (laurent.op.obj X)))) t

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

attribute [colib_tag "COL-0550"] internalCell_evaluation_at

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
