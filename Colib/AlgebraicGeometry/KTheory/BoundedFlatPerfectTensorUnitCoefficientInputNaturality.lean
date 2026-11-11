/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedForgetModel

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientSpectrum
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportHomotopy
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationInputNaturality

/-! # The genuine first coefficient cell on original supported inputs

Precomposition acts before both original cell directions. The supported input map
uses the actual support inclusion and its canonical zero normalization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.RingedSpace
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- The whole first coefficient cell preserves any actual exact based input map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientInputNaturality.\
    lean:30"
  "adaptation" "Original supported input double cylinder and whole binary normalization prism."]
theorem tensorUnitPullbackCoefficientStageCylinder_precomp
    {V : WideSubcategory preservesZero.{u + 1}}
    (J : V ⟶ asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)) (k : ℕ) :
    rowTransformationCylinder
        (F := J ≫ tensorUnitPullbackModelMap f) (G := J ≫ tensorUnitPullbackModelMap f)
        (whiskerLeft J.hom.toFunctor (tensorUnitPullbackModelTransformation f r))
        (fun A => tensorUnitPullbackModelTransformation_weak f r (J.hom.toFunctor.obj A)) k =
      (((stages k).map J ▷ Δ[1]) ▷ Δ[1]) ≫
        tensorUnitPullbackCoefficientStageCylinder f r k :=
  rowTransformationCylinder_precomp (tensorUnitPullbackModelTransformation f r)
    (tensorUnitPullbackModelTransformation_weak f r) J k

variable {U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- On supported inputs the first-row construction retains both original time coordinates. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientInputNaturality.\
    lean:65"
  "adaptation" "Original supported input double cylinder and whole binary normalization prism."]
theorem tensorUnitSupportedCoefficientStageCylinder_eq (k : ℕ) :
    rowTransformationCylinder
        (F := tensorCoefficientSupportedForgetModel j ≫ tensorUnitPullbackModelMap f)
        (G := tensorCoefficientSupportedForgetModel j ≫ tensorUnitPullbackModelMap f)
        (whiskerLeft (tensorCoefficientSupportedForgetModel j).hom.toFunctor
          (tensorUnitPullbackModelTransformation f r))
        (fun A => tensorUnitPullbackModelTransformation_weak f r
          ((tensorCoefficientSupportedForgetModel j).hom.toFunctor.obj A)) k =
      (((stages k).map (tensorCoefficientSupportedForgetModel j) ▷ Δ[1]) ▷ Δ[1]) ≫
        tensorUnitPullbackCoefficientStageCylinder f r k :=
  tensorUnitPullbackCoefficientStageCylinder_precomp f r
    (tensorCoefficientSupportedForgetModel j) k

end AlgebraicGeometry.Scheme.Modules
