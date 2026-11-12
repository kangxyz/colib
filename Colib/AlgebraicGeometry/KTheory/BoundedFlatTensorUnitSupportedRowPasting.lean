/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatTensorUnitSupportedModelUnit
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationPasting

/-! # The actual supported tensor/evaluation endpoint-relative first-row prism -/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
  CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
open GlobalSectionChangeIndex
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) (r : (Γ(A.right, ⊤))ˣ)

/-- The original internal supported scalar after actual target evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedRowPasting.lean:25"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def internalModelUnit : (internalModelMap p).hom.toFunctor ⟶ (internalModelMap p).hom.toFunctor :=
  whiskerRight
    (onFunctor (GlobalSupportedSection.boundedAboveFlatGlobalSupportedPairModelMap p).hom.toFunctor
      (unit (X := op A.right) A.hom r)).hom
    (evaluationModel (X := op A.right) A.hom).hom.toFunctor

/-- The genuine supported tensor crossing after original source evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedRowPasting.lean:32"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def tensorModelUnit : (tensorModelMap p).hom.toFunctor ⟶ (tensorModelMap p).hom.toFunctor :=
  whiskerLeft (evaluationModel (X := op B.right) B.hom).hom.toFunctor
    (tensorSupportedPairModelTransformation p r)

/-- Exact supported evaluation retains the internal unit's original weak equivalence. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedRowPasting.lean:37"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem internalModelUnit_weak
    (K : (boundedAboveFlatGlobalSupportedSectionModel (X := op B.right) B.hom).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen A.hom)).obj.waldhausen.weq
      ((internalModelUnit p r).app K) :=
  (evaluationModel (X := op A.right) A.hom).hom.isExact.weak _
    ((boundedAboveFlatGlobalSupportedSectionModel (X := op A.right)
      A.hom).obj.waldhausen.weq_iso _ inferInstance)

/-- Actual supported source evaluation retains the genuine tensor weak crossing. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedRowPasting.lean:45"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem tensorModelUnit_weak
    (K : (boundedAboveFlatGlobalSupportedSectionModel (X := op B.right) B.hom).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen A.hom)).obj.waldhausen.weq
      ((tensorModelUnit p r).app K) :=
  tensorSupportedPairModelTransformation_weak p r
    ((evaluationModel (X := op B.right) B.hom).hom.toFunctor.obj K)

/-- The complete supported first-row prism retains its real endpoint comparison paths. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedRowPasting.lean:53"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def tensorRowPasting :=
  rowTransformationPasting
    (F := internalModelMap p) (G := internalModelMap p)
    (G' := tensorModelMap p) (H := tensorModelMap p)
    (internalModelUnit p r) (internalTensorModelIso p).hom
    (internalTensorModelIso p).hom (tensorModelUnit p r)
    (internalModelUnit_weak p r)
    (fun _ => (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen
      A.hom)).obj.waldhausen.weq_iso
      _ inferInstance)
    (fun _ => (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen
      A.hom)).obj.waldhausen.weq_iso
      _ inferInstance)
    (tensorModelUnit_weak p r) (internalTensorModelIso_unit p r)

end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
