/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardOverlapLaurent

/-! # The projective-line projection on the actual standard charts -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

set_option backward.isDefEq.respectTransparency false in
/-- The relative polynomial chart commutes with the projections to the base. -/
theorem standardChartPolynomialIso_projection (X : QuasiCompactSchemes.{u}) (i : Fin 2) :
    (standardChartPolynomialIso X i).hom ≫ (Relative.polynomialProjection.app X).hom =
      (standardChart X.obj i).ι ≫ (projectiveSpaceOver 1 X.obj ↘ X.obj) := by
  have h := standardOpenIntegralPullbackIso_hom_fst X.obj (integralChart i)
  change (standardChartIntegralPullbackIso X.obj i).hom ≫ pullback.fst _ _ =
    (standardChart X.obj i).ι ≫ (projectiveSpaceOver 1 X.obj ↘ X.obj) at h
  unfold standardChartPolynomialIso Relative.polynomialProjection
  change ((standardChartIntegralPullbackIso X.obj i).hom ≫ _) ≫ pullback.fst _ _ = _
  simp only [asIso_hom, Category.assoc, pullback.map, pullback.lift_fst, Category.comp_id]
  exact h

end AlgebraicGeometry.Scheme.ProjectiveLine
