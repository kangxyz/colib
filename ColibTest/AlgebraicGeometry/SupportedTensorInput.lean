/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedInputNormalization
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry.RingedSpace
open scoped Simplicial
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorInputTest
variable {U X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)
  (j : U ⟶ Y) [IsOpenImmersion j]

example
    {V : WideSubcategory preservesZero.{u + 1}}
    (J : V ⟶ asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)) (k : ℕ) :
    rowTransformationCylinder
        (F := J ≫ tensorUnitPullbackModelMap f) (G := J ≫ tensorUnitPullbackModelMap f)
        (whiskerLeft J.hom.toFunctor (tensorUnitPullbackModelTransformation f r))
        (fun A => tensorUnitPullbackModelTransformation_weak f r (J.hom.toFunctor.obj A)) k =
      (((stages k).map J ▷ Δ[1]) ▷ Δ[1]) ≫
        tensorUnitPullbackCoefficientStageCylinder f r k :=
  tensorUnitPullbackCoefficientStageCylinder_precomp f r J k

example (k : ℕ) :
    rowTransformationCylinder
        (F := tensorCoefficientSupportedForgetModel j ≫ tensorUnitPullbackModelMap f)
        (G := tensorCoefficientSupportedForgetModel j ≫ tensorUnitPullbackModelMap f)
        (whiskerLeft (tensorCoefficientSupportedForgetModel j).hom.toFunctor
          (tensorUnitPullbackModelTransformation f r))
        (fun A => tensorUnitPullbackModelTransformation_weak f r
          ((tensorCoefficientSupportedForgetModel j).hom.toFunctor.obj A)) k =
      (((stages k).map (tensorCoefficientSupportedForgetModel j) ▷ Δ[1]) ▷ Δ[1]) ≫
        tensorUnitPullbackCoefficientStageCylinder f r k :=
  tensorUnitSupportedCoefficientStageCylinder_eq f r j k

example :
    Homotopy (tensorSupportedCompositePrespectrumMap j f)
      (tensorSupportedCompositePrespectrumMap j f) :=
  tensorSupportedCompositeHomotopy j f r

example :
    ((tensorSupportedCompositeHomotopy j f r).trans
      (tensorSupportedInputNormalization j f)).RelHomotopy
      ((tensorSupportedInputNormalization j f).trans
        (Homotopy.precomp (tensorSupportedInputPrespectrumMap j)
          (boundedAboveFlatPerfectTensorUnitHomotopy f r))) :=
  tensorSupportedInputNormalizationPasting j f r

end AlgebraicGeometry.Scheme.Modules.SupportedTensorInputTest
