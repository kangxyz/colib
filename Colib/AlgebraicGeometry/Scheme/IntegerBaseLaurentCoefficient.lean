/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseLaurentParameter

/-! # Original integral Spec and coefficient comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow

/-- The whole Laurent comparison commutes with the original coefficient projection. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseLaurentCoefficient.lean:36"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem laurentParameterIso_coefficient
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (laurentParameterIso Q a).hom ≫
        (baseProductFunctor (specULiftZIsTerminal.from Q.left)).map
          ((baseProductProjection (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u}
            ℤ)))).app
            (Spec a.right)) =
      laurentProjection Q a ≫ (canonicalRowIso Q a).hom := by
  simp only [laurentParameterIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp]
  dsimp only [baseProductProjection]
  rw [laurentSpecIso_hom_fst]
  exact (canonicalRowIso_coefficient Q ((laurentUnderCoefficient _).app a)).symm

end AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow

