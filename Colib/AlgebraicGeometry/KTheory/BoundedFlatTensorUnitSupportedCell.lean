/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatTensorUnitSupportedRowPasting
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatTensorUnitSupportedCoefficientSpectrum
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationInputNaturality
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationRealization

/-! # Independent genuine tensor cells on the actual supported Model

First apply actual source evaluation to the input finite S-diagram, then the original tensor
coefficient cell. This construction precedes identification with any internal identity-unit cell.
Both cylinder directions and the genuine stage-zero tensor row remain explicit.
-/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
open GlobalSectionChangeIndex
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) (r : (Γ(A.right, ⊤))ˣ)

/-- Evaluate the original finite input, retaining both independent tensor-cell cylinders. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCell.lean:34"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def tensorCellCylinder (k : ℕ) :=
  (((stages k).map (evaluationModel (X := op B.right) B.hom) ▷ Δ[1]) ▷ Δ[1]) ≫
    tensorSupportedPairCoefficientStageCylinder p r k

/-- The initial cell is the independently built original tensor coefficient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCell.lean:39"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem tensorCellCylinder_zero :
    tensorCellCylinder p r 0 =
      (((stages 0).map (evaluationModel (X := op B.right) B.hom) ▷ Δ[1]) ▷ Δ[1]) ≫
        tensorSupportedPairSmallCoefficientCylinder p r := by
  unfold tensorCellCylinder
  rw [tensorSupportedPairCoefficientStageCylinder_zero]

/-- The original full input-map law identifies every finite tensor cell before realization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCell.lean:47"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem tensorCellCylinder_eq (k : ℕ) :
    tensorCellCylinder p r k =
      rowTransformationCylinder
        (F := tensorModelMap p) (G := tensorModelMap p)
        (whiskerLeft (evaluationModel (X := op B.right) B.hom).hom.toFunctor
          (tensorSupportedPairModelTransformation p r))
        (fun A => tensorSupportedPairModelTransformation_weak p r
          ((evaluationModel (X := op B.right) B.hom).hom.toFunctor.obj A)) k :=
  (rowTransformationCylinder_precomp
    (tensorSupportedPairModelTransformation p r)
    (tensorSupportedPairModelTransformation_weak p r)
    (evaluationModel (X := op B.right) B.hom) k).symm

/-- Realization of the independent tensor cell, before the internal-unit comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCell.lean:61"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def tensorCellRealization (k : ℕ) :
    C(unitInterval ×
        (unitInterval × stageSpace k (boundedAboveFlatGlobalSupportedSectionModel (X := op
          B.right) B.hom)),
      stageSpace (k + 1)
        (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen A.hom))) :=
  ⟨fun z => SSet.toTop.map (tensorCellCylinder p r k)
    ((SSet.realizationCylinderIso
      ((stages k).obj (boundedAboveFlatGlobalSupportedSectionModel (X := op B.right) B.hom) ⊗
        Δ[1])).inv
      ((SSet.realizationCylinderIso
        ((stages k).obj (boundedAboveFlatGlobalSupportedSectionModel (X := op B.right) B.hom))).inv
        (z.2.2, ULift.up z.2.1), ULift.up z.1)), by fun_prop⟩

/-- The complete realized double cylinder is the genuine tensor Model transformation cell. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCell.lean:74"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem tensorCellRealization_eq (k : ℕ) :
    tensorCellRealization p r k =
      rowTransformationRealization (tensorModelUnit p r) (tensorModelUnit_weak p r) k := by
  apply ContinuousMap.ext
  intro z
  change SSet.toTop.map (tensorCellCylinder p r k) _ = _
  rw [tensorCellCylinder_eq]
  rfl

/-- Every positive spectrum level retains both independent realized tensor-cell times. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCell.lean:84"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem tensorCell_succ (k : ℕ) (t s : unitInterval)
    (x : stageSpace k (boundedAboveFlatGlobalSupportedSectionModel (X := op B.right) B.hom)) :
    Path.toContinuousMap
      ((rowTransformationSpectrumHomotopy (tensorModelUnit p r)
        (tensorModelUnit_weak p r)).level (k + 1) (t, x)) s =
      tensorCellRealization p r k (s, (t, x)) := by
  rw [tensorCellRealization_eq]
  exact rowTransformationSpectrumHomotopy_succ _ _ k t s x

/-- Degree zero retains the additional original input-loop coordinate. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCell.lean:94"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem tensorCell_zero (t a s : unitInterval)
    (γ : Path (stagePoint 0 (boundedAboveFlatGlobalSupportedSectionModel (X := op B.right) B.hom))
      (stagePoint 0 (boundedAboveFlatGlobalSupportedSectionModel (X := op B.right) B.hom))) :
    Path.toContinuousMap (Path.toContinuousMap
      ((rowTransformationSpectrumHomotopy (tensorModelUnit p r)
        (tensorModelUnit_weak p r)).level 0 (t, γ)) a) s =
      tensorCellRealization p r 0 (s, (t, γ a)) := by
  rw [tensorCellRealization_eq]
  exact rowTransformationSpectrumHomotopy_zero _ _ t a s γ

end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
