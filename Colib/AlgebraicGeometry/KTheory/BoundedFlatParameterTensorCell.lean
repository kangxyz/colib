/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorRowPasting
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientStages
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationInputNaturality
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationRealization

/-! # Independent genuine tensor cells on the literal parameter ambient Model

First apply actual source evaluation to the input finite S-diagram, then the original tensor
coefficient cell. This construction precedes identification with any internal identity-unit cell.
Both cylinder directions and the genuine stage-zero tensor row remain explicit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex GlobalSupportedSection
open AlgebraicGeometry.RingedSpace

/-- Evaluate the original finite input, retaining both independent tensor-cell cylinders. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorCell.lean:32"
  "adaptation" "Original evaluated finite tensor cell and ordered realization coordinates."]
def tensorCellCylinder (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ) :=
  (((stages k).map (evaluationModel (op (scheme Q X))) ▷ Δ[1]) ▷ Δ[1]) ≫
    tensorUnitPullbackCoefficientStageCylinder (coefficientMap Q X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X) k

/-- The initial cell is the independently built original tensor coefficient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorCell.lean:38"
  "adaptation" "Original evaluated finite tensor cell and ordered realization coordinates."]
theorem tensorCellCylinder_zero (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    tensorCellCylinder Q X 0 =
      (((stages 0).map (evaluationModel (op (scheme Q X))) ▷ Δ[1]) ▷ Δ[1]) ≫
        tensorUnitPullbackSmallCoefficientCylinder (coefficientMap Q X)
          (ParameterLaurentUnit.projectedLaurentScalar Q X) := by
  unfold tensorCellCylinder
  rw [tensorUnitPullbackCoefficientStageCylinder_zero]

/-- The original full input-map law identifies every finite tensor cell before realization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorCell.lean:47"
  "adaptation" "Original evaluated finite tensor cell and ordered realization coordinates."]
theorem tensorCellCylinder_eq (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ) :
    tensorCellCylinder Q X k =
      rowTransformationCylinder
        (F := tensorModelMap Q X) (G := tensorModelMap Q X)
        (whiskerLeft (evaluationModel (op (scheme Q X))).hom.toFunctor
          (tensorUnitPullbackModelTransformation (coefficientMap Q X)
            (ParameterLaurentUnit.projectedLaurentScalar Q X)))
        (fun A => tensorUnitPullbackModelTransformation_weak (coefficientMap Q X)
          (ParameterLaurentUnit.projectedLaurentScalar Q X)
          ((evaluationModel (op (scheme Q X))).hom.toFunctor.obj A)) k :=
  (rowTransformationCylinder_precomp
    (tensorUnitPullbackModelTransformation (coefficientMap Q X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X))
    (tensorUnitPullbackModelTransformation_weak (coefficientMap Q X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X))
    (evaluationModel (op (scheme Q X))) k).symm

/-- Realization of the independent tensor cell, before the internal-unit comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorCell.lean:65"
  "adaptation" "Original evaluated finite tensor cell and ordered realization coordinates."]
def tensorCellRealization (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ) :
    C(unitInterval × (unitInterval × stageSpace k ((ParameterModels.ambient Q).obj X)),
      stageSpace (k + 1)
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (scheme Q (laurent.op.obj
      X)).toRingedSpace))) :=
  ⟨fun z => SSet.toTop.map (tensorCellCylinder Q X k)
    ((SSet.realizationCylinderIso
      ((stages k).obj ((ParameterModels.ambient Q).obj X) ⊗ Δ[1])).inv
      ((SSet.realizationCylinderIso ((stages k).obj ((ParameterModels.ambient Q).obj X))).inv
        (z.2.2, ULift.up z.2.1), ULift.up z.1)), by fun_prop⟩

/-- The complete realized double cylinder is the genuine tensor Model transformation cell. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorCell.lean:76"
  "adaptation" "Original evaluated finite tensor cell and ordered realization coordinates."]
theorem tensorCellRealization_eq (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ) :
    tensorCellRealization Q X k =
      rowTransformationRealization (tensorModelUnit Q X) (tensorModelUnit_weak Q X) k := by
  apply ContinuousMap.ext
  intro z
  change SSet.toTop.map (tensorCellCylinder Q X k) _ = _
  rw [tensorCellCylinder_eq]
  rfl

/-- Every positive spectrum level retains both independent realized tensor-cell times. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorCell.lean:86"
  "adaptation" "Original evaluated finite tensor cell and ordered realization coordinates."]
theorem tensorCell_succ (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ) (t s : unitInterval)
    (x : stageSpace k ((ParameterModels.ambient Q).obj X)) :
    Path.toContinuousMap
      ((rowTransformationSpectrumHomotopy (tensorModelUnit Q X)
        (tensorModelUnit_weak Q X)).level (k + 1) (t, x)) s =
      tensorCellRealization Q X k (s, (t, x)) := by
  rw [tensorCellRealization_eq]
  exact rowTransformationSpectrumHomotopy_succ _ _ k t s x

/-- Degree zero retains the additional original input-loop coordinate. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorCell.lean:96"
  "adaptation" "Original evaluated finite tensor cell and ordered realization coordinates."]
theorem tensorCell_zero (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (t a s : unitInterval)
    (γ : Path (stagePoint 0 ((ParameterModels.ambient Q).obj X))
      (stagePoint 0 ((ParameterModels.ambient Q).obj X))) :
    Path.toContinuousMap (Path.toContinuousMap
      ((rowTransformationSpectrumHomotopy (tensorModelUnit Q X)
        (tensorModelUnit_weak Q X)).level 0 (t, γ)) a) s =
      tensorCellRealization Q X 0 (s, (t, γ a)) := by
  rw [tensorCellRealization_eq]
  exact rowTransformationSpectrumHomotopy_zero _ _ t a s γ

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

attribute [colib_tag "COL-0550"] tensorCellRealization_eq
attribute [colib_tag "COL-0550"] tensorCell_succ
attribute [colib_tag "COL-0550"] tensorCell_zero

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
