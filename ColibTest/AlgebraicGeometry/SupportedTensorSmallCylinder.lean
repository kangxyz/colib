/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientSmallCylinder
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Simplicial
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorSmallCylinderTest
variable {S T : Scheme.OpenPairs.{u}} (p : S ⟶ T) (r : (Γ(S.right, ⊤))ˣ)

example :
    tensorSupportedPairCoefficientCylinder p r =
      (tensorSupportedPairNormalizedCylinder p r ▷ Δ[1]) ≫
        suspensionCylinder (boundedAboveFlatPerfectSupportedWaldhausen S.hom) :=
  tensorSupportedPairCoefficientCylinder_eq p r

example :
    tensorSupportedPairSmallCoefficientCylinder p r =
      (stageTransformationCylinder 0 (tensorSupportedPairModelTransformation p r)
        (tensorSupportedPairModelTransformation_weak p r) ▷ Δ[1]) ≫
        stageCylinder 0 (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen S.hom)) :=
  tensorSupportedPairSmallCoefficientCylinder_eq p r

example :
    tensorSupportedPairSmallCoefficientCylinder p r =
      rowTransformationCylinder (tensorSupportedPairModelTransformation p r)
        (tensorSupportedPairModelTransformation_weak p r) 0 :=
  tensorSupportedPairSmallCoefficientCylinder_row p r

end AlgebraicGeometry.Scheme.Modules.SupportedTensorSmallCylinderTest
