/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.IntegralOverlapGeometry

/-! # The chart coordinate as an actual global function -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "Z" => ULift ℤ
local notation "𝒜" => polyGrading Z 1

set_option backward.isDefEq.respectTransparency false in
/-- On the integral negative chart, the native polynomial section is the ratio `T₀/T₁`. -/
theorem integralNegativeChart_coordinate :
    (integralChartPolynomialIso.{u} 1).hom.appTop (polynomialCoordinate (.of Z)) =
      (integralChart.{u} 1).topIso.inv
        ((Proj.awayToSection 𝒜 (MvPolynomial.X 1))
          (chartCoord Z 1 1 ⟨0, by decide⟩)) := by
  let f := CommRingCat.ofHom (inverseCoordinateEquiv Z).toRingHom
  have hspec := (ConcreteCategory.congr_hom (ΓSpecIso_inv_naturality f) Polynomial.X).symm
  rw [integralChartPolynomialIso_hom]
  change ((Proj.basicOpenToSpec 𝒜 (MvPolynomial.X 1)) ≫ Spec.map f).appTop
    (polynomialCoordinate (.of Z)) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, polynomialCoordinate]
  change (Proj.basicOpenToSpec 𝒜 (MvPolynomial.X 1)).appTop
    ((Spec.map f).appTop ((ΓSpecIso (.of (Polynomial Z))).inv Polynomial.X)) = _
  change (Spec.map f).appTop ((ΓSpecIso (.of (Polynomial Z))).inv Polynomial.X) =
    (ΓSpecIso _).inv (f Polynomial.X) at hspec
  rw [hspec]
  have htop : (Proj.basicOpenToSpec 𝒜 (MvPolynomial.X 1)).appTop =
      (ΓSpecIso _).hom ≫ Proj.awayToSection 𝒜 (MvPolynomial.X 1) ≫
        (integralChart.{u} 1).topIso.inv :=
    Proj.basicOpenToSpec_app_top 𝒜 (MvPolynomial.X 1)
  rw [htop]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  exact congrArg (fun x => (integralChart.{u} 1).topIso.inv
    ((Proj.awayToSection 𝒜 (MvPolynomial.X 1)) x)) (inverseCoordinateEquiv_X Z)

end AlgebraicGeometry.Scheme.ProjectiveLine
