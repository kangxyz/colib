/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateChartRatio
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardOverlapLaurentScalar
public import Colib.AlgebraicGeometry.ProjectiveLine.IntegralChartCoordinate

/-! # The affine scalar of the original homogeneous coordinate -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Stacks.SectionsToProjectiveSpace Stacks.TwistPullbackPinned
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The polynomial factor of a relative standard chart is its integral chart projection. -/
theorem standardChartPolynomialIso_hom_snd (X : QuasiCompactSchemes.{u}) (i : Fin 2) :
    (standardChartPolynomialIso X i).hom ≫ pullback.snd _ _ =
      (projectiveSpaceOver.toIntegralAtUniverse 1 X.obj ∣_ integralChart i) ≫
        (integralChartPolynomialIso i).hom := by
  rw [← standardOpenIntegralPullbackIso_hom_snd]
  unfold standardChartPolynomialIso
  simp only [Iso.trans_hom, asIso_hom, Category.assoc, pullback.map, pullback.lift_snd]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The scalar (T₀/T₁) on the relative negative chart is its actual polynomial coordinate. -/
theorem negativeChartCoordinate_eq_chartRatio (X : QuasiCompactSchemes.{u}) :
    negativeChartCoordinate X =
      (negativeChart X.obj).topIso.inv
        ((projectiveSpaceOver.toIntegralAtUniverse 1 X.obj).app (integralChart 1)
          ((Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X 1)).hom
            (coordFrac.{u} 1 0))) := by
  let f := projectiveSpaceOver.toIntegralAtUniverse 1 X.obj
  let D := integralChart.{u} 1
  let z := (Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X 1)).hom (coordFrac.{u} 1 0)
  rw [negativeChartCoordinate, standardChartPolynomialIso_hom_snd,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, integralNegativeChart_coordinate]
  have h : (f ∣_ D).appTop = D.topIso.hom ≫ f.app D ≫ (f ⁻¹ᵁ D).topIso.inv := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    simp [Scheme.Hom.appLE]
  change (f ∣_ D).appTop (D.topIso.inv z) = (f ⁻¹ᵁ D).topIso.inv (f.app D z)
  rw [h]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]

end AlgebraicGeometry.Scheme.ProjectiveLine
