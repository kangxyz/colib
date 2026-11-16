/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardOverlapLaurent
public import Colib.AlgebraicGeometry.Scheme.LaurentInverseCoordinate

/-! # The negative chart coordinate on the canonical overlap -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

/-- The actual polynomial coordinate section on the negative standard chart. -/
def negativeChartCoordinate (X : QuasiCompactSchemes.{u}) :
    Γ((negativeChart X.obj).toScheme, ⊤) :=
  ((standardChartPolynomialIso X 1).hom ≫ pullback.snd _ _).appTop
    (polynomialCoordinate (.of (ULift.{u} ℤ)))

/-- The forward Laurent unit pulled back to the actual intersection. -/
def overlapCoordinateUnit (X : QuasiCompactSchemes.{u}) :
    (Γ((chartOverlap X.obj).toScheme, ⊤))ˣ :=
  Units.map (((standardOverlapLaurentIso X).hom ≫ pullback.snd _ _).appTop.hom.toMonoidHom)
    (laurentCoordinate (.of (ULift.{u} ℤ)))

/-- The actual negative coordinate restricts to the inverse of the actual Laurent unit. -/
theorem negativeChartCoordinate_restrict (X : QuasiCompactSchemes.{u}) :
    (overlapToNegative X.obj).appTop (negativeChartCoordinate X) =
      ↑((overlapCoordinateUnit X)⁻¹) := by
  let R := CommRingCat.of (ULift.{u} ℤ)
  let a : (negativeChart X.obj).toScheme ⟶ (Relative.polynomialFunctor.obj X).obj :=
    (standardChartPolynomialIso X 1).hom
  let b := (standardOverlapLaurentIso X).hom
  let p := pullback.snd (specULiftZIsTerminal.from X.obj) (polynomialProjection R)
  let l := pullback.snd (specULiftZIsTerminal.from X.obj) (laurentProjection R)
  have hm : (Relative.minus.app X).hom ≫ p = l ≫ laurentMinus R := by
    dsimp only [p, l, R, Relative.minus, qcBaseProductTransformation,
      baseProductTransformation, baseProductFunctor, pullback.map]
    exact pullback.lift_snd _ _ _
  have h : overlapToNegative X.obj ≫ (a ≫ p) = b ≫ (l ≫ laurentMinus R) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ p) (overlapToNegative_polynomial X)).trans
        ((Category.assoc _ _ _).trans (congrArg (fun k => b ≫ k) hm)))
  have hh := congrArg (fun f => f.appTop (polynomialCoordinate R)) h
  change (overlapToNegative X.obj).appTop ((a ≫ p).appTop (polynomialCoordinate R)) =
    (b ≫ l).appTop ((laurentMinus R).appTop (polynomialCoordinate R)) at hh
  rw [laurentMinus_appTop_coordinate] at hh
  change (overlapToNegative X.obj).appTop ((a ≫ p).appTop (polynomialCoordinate R)) =
    (b ≫ l).appTop.hom ↑((laurentCoordinate R)⁻¹)
  exact hh

end AlgebraicGeometry.Scheme.ProjectiveLine
