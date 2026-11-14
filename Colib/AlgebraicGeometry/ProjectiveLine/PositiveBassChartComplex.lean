/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateChartExactness
public import Colib.AlgebraicGeometry.ProjectiveLine.PositiveBassAdditiveCokernel
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # The exact positive Bass middle row as a short complex -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] Waldhausen.Additivity.KCommGroup

/-- The original difference annihilates the common coefficient map. -/
theorem positiveBassMiddle_comp (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) :
    AddCommGrpCat.ofHom (relativePolynomialPair X n).toAdditive ≫
      positiveBassDifferenceHom X n = 0 := by
  apply AddCommGrpCat.ext
  intro x
  change relativeLaurentDifference X n (relativePolynomialPair X n x.toMul) = 1
  have h : relativePolynomialPair X n x.toMul ∈ (relativeLaurentDifference X n).ker := by
    rw [← relativePolynomialPair_range_eq_ker X n]
    exact ⟨x.toMul, rfl⟩
  exact h

/-- The actual two-chart middle complex, in additive notation. -/
def positiveBassChartComplex (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj] (n : ℕ) :
    ShortComplex AddCommGrpCat.{u + 1} :=
  ShortComplex.mk (AddCommGrpCat.ofHom (relativePolynomialPair X n).toAdditive)
    (positiveBassDifferenceHom X n) (positiveBassMiddle_comp X n)

/-- Exactness of the literal original polynomial–Laurent chart row in every connective degree. -/
theorem positiveBassChartComplex_exact (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) : (positiveBassChartComplex X n).Exact := by
  apply (ShortComplex.ab_exact_iff_function_exact _).mpr
  intro y
  change relativeLaurentDifference X n y.toMul = 1 ↔
    ∃ x, relativePolynomialPair X n x = y.toMul
  change y.toMul ∈ (relativeLaurentDifference X n).ker ↔
    y.toMul ∈ (relativePolynomialPair X n).range
  rw [relativePolynomialPair_range_eq_ker X n]

end AlgebraicGeometry.Scheme.ProjectiveLine
