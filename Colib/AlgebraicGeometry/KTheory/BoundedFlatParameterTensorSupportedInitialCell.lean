/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorSupportedRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatTensorUnitSupportedCell
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricSeedCospan
public import Colib.KTheory.Bass.ModelUnitRowCell
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationSpectrumNaturality

/-!
# The literal supported parameter first-row cell and its genuine tensor comparison

Exact supported evaluation identifies the internal edge of the original tensor-unitor prism.
The actual supported Model, its two chosen-zero transports, and all row/unit times are retained.
-/
@[expose] public section
noncomputable section
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open KTheory.Bass Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorSupportedRow
open GlobalSectionChangeIndex GeometricSeedCospan
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original supported parameter Model's independent first-row cell. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedInitialC\
    ell.lean:35"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def initialCell (X : Scheme.{u}ᵒᵖ) :=
  ModelDiagramRowInterchange.initialCell laurent.op coefficient (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f) X

/-- The whole first-row comparison keeps the original supported track at the same time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedInitialC\
    ell.lean:40"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem initialCell_eq (X : Scheme.{u}ᵒᵖ) :
    initialCell f X = ((ParameterLaurentTrack.supportedTrack f).homotopy X).postcomp
      (RowRefinement.comparison
        (prespectrum ((ParameterModels.supported f).obj (laurent.op.obj X)))
        (ModelDiagramRowInterchange.initial (ParameterModels.supported f) (laurent.op.obj X))
        (ModelDiagramRowInterchange.initial_point (ParameterModels.supported f) (laurent.op.obj X))
        (ModelDiagramRowInterchange.initial_structure
          (ParameterModels.supported f) (laurent.op.obj X))) :=
  ModelDiagramRowInterchange.initialCell_eq laurent.op coefficient (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f)
    (ParameterLaurentTrack.supportedUnit_naturality f) X

/-- The genuine supported tensor endpoint-relative prism on the literal parameter input. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedInitialC\
    ell.lean:53"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def firstRowPasting (X : Scheme.{u}ᵒᵖ) :=
  SupportedTensorEvaluation.tensorRowPasting (coefficientPair f X)
    (ParameterLaurentUnit.projectedLaurentScalar Q X)

/-- Actual supported evaluation identifies the entire internal edge of this genuine prism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedInitialC\
    ell.lean:58"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem internalCell_evaluation_at (X : Scheme.{u}ᵒᵖ) (t : unitInterval) :
    (rowTransformationSpectrumHomotopy
      (SupportedTensorEvaluation.internalModelUnit (coefficientPair f X)
        (ParameterLaurentUnit.projectedLaurentScalar Q X))
      (SupportedTensorEvaluation.internalModelUnit_weak (coefficientPair f X)
        (ParameterLaurentUnit.projectedLaurentScalar Q X))).at t =
    (initialCell f X).at t ≫
      rowLoopMap (SupportedTensorEvaluation.evaluationModel
        (X := op (pair f (laurent.op.obj X)).right)
        (pair f (laurent.op.obj X)).hom) := by
  exact rowTransformationSpectrumHomotopy_postcomp_at
    (onFunctor (boundedAboveFlatGlobalSupportedPairModelMap (coefficientPair f X)).hom.toFunctor
      (SupportedTensorEvaluation.unit
        (X := op (pair f (laurent.op.obj X)).right)
        (pair f (laurent.op.obj X)).hom
        (ParameterLaurentUnit.projectedLaurentScalar Q X))).hom
    (fun _ => ((ParameterModels.supported f).obj
      (laurent.op.obj X)).obj.waldhausen.weq_iso _ inferInstance)
    (SupportedTensorEvaluation.evaluationModel
      (X := op (pair f (laurent.op.obj X)).right)
      (pair f (laurent.op.obj X)).hom) t

end AlgebraicGeometry.Scheme.Modules.ParameterTensorSupportedRow
