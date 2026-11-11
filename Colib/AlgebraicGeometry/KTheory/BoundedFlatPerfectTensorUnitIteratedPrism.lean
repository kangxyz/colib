/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitNervePrism

/-!
# Original normalization and structure operators of the restricted tensor prism

The coefficient crossing is written in every original complex degree, with the two canonical
zero-normalization isomorphisms retained. Original small-model transport and quotient-row
prolongation then give the actual iterated-S cylinder. Its original structure parameter is
independent of the coefficient-edge parameter, including at level zero.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.RingedSpace MonoidalCategory
open Stacks.RegularSequence (globalSmulCenter)
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules

local instance tensorUnitIteratedPrismMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace

/-- The actual coefficient tensor on each term of every original pulled-back complex. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitIteratedPrism.lean:30"
  "adaptation" "Original tensor coefficient prism and independent structure parameter"]
theorem boundedAboveFlatPerfectTensorUnitPullbackAutomorphism_hom_f {X Y : Scheme.{u}}
    (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) (K : (boundedAboveFlatPerfectComplex
      Y.toRingedSpace).FullSubcategory) (n : ℤ) :
    ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
      ((boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom.app K)).f n =
      ((MonoidalCategory.curriedTensor X.Modules).map (tensorCoefficientUnitIso X r).hom).app
        (((boundedAboveFlatPerfectPullback f).obj K).obj.X n) := by
  change ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
    ((boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom.app
      ((boundedAboveFlatPerfectPullback f).obj K))).f n = _
  rw [boundedAboveFlatPerfectTensorUnitAutomorphism_hom_original,
    complexTensorUnitAutomorphism_hom_f]
  rfl

/-- The fixed original zero normalization of genuine tensor-unit pullback. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitIteratedPrism.lean:43"
  "adaptation" "Original tensor coefficient prism and independent structure parameter"]
def tensorUnitPullbackNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  CategoryTheory.rebaseFunctorIso (boundedAboveFlatPerfectTensorUnitPullback f)
    (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).zero (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace).zero
    (((boundedAboveFlatPerfectTensorUnitPullback_exact f).zero
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).isZero).iso
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero)

/-- Every normalized grid crossing retains the actual tensor coefficient between the two
original zero-normalization components. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitIteratedPrism.lean:51"
  "adaptation" "Original tensor coefficient prism and independent structure parameter"]
theorem tensorUnitPullbackNormalized_crossing_f {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (K : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) (n :
      ℤ) :
    ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
      ((normalizedWeakTransformation (boundedAboveFlatPerfectTensorUnitPullback_exact f)
        (boundedAboveFlatPerfectTensorUnitPullback_exact f)
        (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom).app K)).f n =
      ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map ((tensorUnitPullbackNormalization
      f).inv.app K)).f n ≫
        ((MonoidalCategory.curriedTensor X.Modules).map (tensorCoefficientUnitIso X r).hom).app
          (((boundedAboveFlatPerfectPullback f).obj K).obj.X n) ≫
        ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map ((tensorUnitPullbackNormalization
      f).hom.app K)).f n := by
  simp only [normalizedWeakTransformation, NatTrans.comp_app, CategoryTheory.Functor.map_comp,
    HomologicalComplex.comp_f, boundedAboveFlatPerfectTensorUnitPullbackAutomorphism_hom_f]
  rfl

/-- The original canonically based model map underlying the unchanged exact tensor spectrum map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitIteratedPrism.lean:66"
  "adaptation" "Original tensor coefficient prism and independent structure parameter"]
def tensorUnitPullbackModelMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace) ⟶ asSmallCategory
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) :=
  asSmallCategoryMap _ _ (boundedAboveFlatPerfectTensorUnitPullback_exact f).rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)

/-- The actual coefficient crossing with precisely the existing small-model and zero transports. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitIteratedPrism.lean:72"
  "adaptation" "Original tensor coefficient prism and independent structure parameter"]
def tensorUnitPullbackModelTransformation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    (tensorUnitPullbackModelMap f).hom.toFunctor ⟶ (tensorUnitPullbackModelMap f).hom.toFunctor :=
  whiskerLeft AsSmall.down (whiskerRight
    (normalizedWeakTransformation (boundedAboveFlatPerfectTensorUnitPullback_exact f)
      (boundedAboveFlatPerfectTensorUnitPullback_exact f)
      (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom) AsSmall.up)

/-- Weak equivalences of the original tensor edge survive the specified canonical transports. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitIteratedPrism.lean:81"
  "adaptation" "Original tensor coefficient prism and independent structure parameter"]
theorem tensorUnitPullbackModelTransformation_weak {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (A : (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      Y.toRingedSpace)).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).obj.waldhausen.weq
      ((tensorUnitPullbackModelTransformation f r).app A) :=
  normalizedWeakTransformation_weak (boundedAboveFlatPerfectTensorUnitPullback_exact f)
    (boundedAboveFlatPerfectTensorUnitPullback_exact f)
    (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom
    (fun _ ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)
      (AsSmall.down.obj A)

/-- Prolongation acts on each original quotient-row entry by that same coefficient crossing. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitIteratedPrism.lean:91"
  "adaptation" "Original tensor coefficient prism and independent structure parameter"]
theorem tensorUnitPullback_rows_component {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (n : SimplexCategory)
    (A : ((rows n).obj (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      Y.toRingedSpace))).obj.Obj) (p : Interval n) :
    ((rowsTransformation (tensorUnitPullbackModelTransformation f r) n).app A).hom.app p =
      (tensorUnitPullbackModelTransformation f r).app (A.obj.obj p) := rfl

/-- Every finite tensor prism commutes with the original suspension-row structure operator;
the coefficient edge and structure simplex parameters remain independent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitIteratedPrism.lean:99"
  "adaptation" "Original tensor coefficient prism and independent structure parameter"]
theorem tensorUnitPullback_prism_structure {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages k).obj (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      Y.toRingedSpace))).obj n)
    (τ θ : (Δ[1]).obj n) :
    stageTransformationFunction (k + 1) (tensorUnitPullbackModelTransformation f r)
      (tensorUnitPullbackModelTransformation_weak f r) n
      ((stageCylinder k (asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace))).app
      n (A, τ)) θ =
    (stageCylinder k (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))).app n
      (stageTransformationFunction k (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) n A θ, τ) :=
  stageTransformationFunction_structure k (tensorUnitPullbackModelTransformation f r)
    (tensorUnitPullbackModelTransformation_weak f r) n A τ θ

/-- The realized positive levels are literally the unchanged iterated-S tensor prisms. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitIteratedPrism.lean:113"
  "adaptation" "Original tensor coefficient prism and independent structure parameter"]
theorem tensorUnitPullback_homotopy_succ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (k : ℕ) (s : unitInterval)
    (x : stageSpace k (asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace))) :
    (boundedAboveFlatPerfectTensorUnitHomotopy f r).level (k + 1) (s, x) =
      stageTransformationTopHomotopy k (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) (s, x) := rfl

/-- Level zero retains the original loop coordinate, independently of coefficient-edge time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitIteratedPrism.lean:121"
  "adaptation" "Original tensor coefficient prism and independent structure parameter"]
theorem tensorUnitPullback_homotopy_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (s t : unitInterval)
    (x : Path (stagePoint 0 (asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)))
      (stagePoint 0 (asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)))) :
    (show Path (stagePoint 0 (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))
      (stagePoint 0 (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))) from
        (boundedAboveFlatPerfectTensorUnitHomotopy f r).level 0 (s, x)) t =
      stageTransformationTopHomotopy 0 (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) (s, x t) := rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0543"] tensorUnitPullback_prism_structure
attribute [colib_tag "COL-0543"] tensorUnitPullback_homotopy_succ
attribute [colib_tag "COL-0543"] tensorUnitPullback_homotopy_zero

end AlgebraicGeometry.Scheme.Modules
