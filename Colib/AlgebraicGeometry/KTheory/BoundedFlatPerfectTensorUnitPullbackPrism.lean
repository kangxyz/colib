/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitIteratedPrism

/-!
# The restricted tensor prism on original pullback grids

Every raw pullback S-grid is tensored with the original coefficient edge. The comparison with
the raw nerve cylinder retains all original entries and chain maps. The normalized iterated
construction has its literal quotient-row successor equation, rather than an assumed tower
compatibility. Together with the explicit normalization and structure formulas, this identifies
the restricted tensor-edge action at the original iterated-S levels.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.RingedSpace MonoidalCategory
open Stacks.RegularSequence (globalSmulCenter)
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The native sheaf-of-modules monoidal structure on the scheme. -/
local instance tensorUnitPullbackPrismMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace

/-- On every raw geometric pullback grid, the original tensor-unit nerve cylinder is the
independently constructed actual coefficient tensor edge times the pulled-back input. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitPullbackPrism.lean:31"
  "adaptation" "Original tensor coefficient prism and independent structure parameter"]
theorem boundedAboveFlatPerfectTensorUnitPullbackPrism_original {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) {n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      Y.toRingedSpace).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram
      (whiskerLeft A (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom) τ ⋙
        (boundedAboveFlatPerfectComplex X.toRingedSpace).ι =
      complexTensorUnitPrism X r
        (A ⋙ boundedAboveFlatPerfectPullback f ⋙ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).ι) τ := by
  rw [← iteratedNerveCylinderDiagram_postcomp, complexTensorUnitPrism_eq_nerve]
  congr 1
  apply NatTrans.ext
  funext p
  change (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
    ((boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom.app
      ((boundedAboveFlatPerfectPullback f).obj (A.obj p))) = _
  exact boundedAboveFlatPerfectTensorUnitAutomorphism_hom_original X r
    ((boundedAboveFlatPerfectPullback f).obj (A.obj p))

/-- The independent tensor-edge construction preserves the actual quotient-grid conditions
after arbitrary geometric pullback, with no flatness assumption on the scheme map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitPullbackPrism.lean:51"
  "adaptation" "Original tensor coefficient prism and independent structure parameter"]
theorem boundedAboveFlatPerfectTensorUnitPullbackPrism_isSimplex₂ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) {n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      Y.toRingedSpace).FullSubcategory)
    (hA : IsSimplex₂ (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq A) (τ : m ⟶ ⦋1⦌) :
    IsSimplex₂ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
      (nerveCylinderDiagram
        (whiskerLeft A (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom) τ) :=
  nerveCylinderDiagram_isSimplex₂ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) _
    (fun _ ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)
    (hA.postcomp _ _ (boundedAboveFlatPerfectTensorUnitPullback_exact f))
    (hA.postcomp _ _ (boundedAboveFlatPerfectTensorUnitPullback_exact f)) τ

/-- The normalized iterated tensor prism is prolonged by the actual quotient-row action at
each successor, with no separately chosen higher compatibility. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitPullbackPrism.lean:65"
  "adaptation" "Original tensor coefficient prism and independent structure parameter"]
theorem tensorUnitPullback_prism_succ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages (k + 1)).obj (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      Y.toRingedSpace))).obj n)
    (τ : (Δ[1]).obj n) :
    stageTransformationFunction (k + 1) (tensorUnitPullbackModelTransformation f r)
      (tensorUnitPullbackModelTransformation_weak f r) n A τ =
    stageTransformationFunction k (rowsTransformation (tensorUnitPullbackModelTransformation f r)
      n.unop) (rowsTransformation_weak (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) n.unop) n A τ := rfl

end AlgebraicGeometry.Scheme.Modules
