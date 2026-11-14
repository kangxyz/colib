/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateBoundaryKernel
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The original positive Bass quotient -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] Waldhausen.Additivity.KCommGroup

local notation "W" Y =>
  RingedSpace.perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace
    (Scheme.toLocallyRingedSpace Y))

/-- The first-coordinate Bass boundary identifies the quotient by the two chart images with
the original coefficient group. The inverse sends a coefficient to its inverse Laurent unit. -/
def positiveBassQuotientEquiv (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj] (n : ℕ) :
    (W(Relative.laurentFunctor.obj X).obj).K (n + 1) ⧸
        (relativeLaurentDifference X (n + 1)).range ≃* (W X.obj).K n :=
  (QuotientGroup.quotientMulEquivOfEq (relativeLaurentDifference_range_eq_ker X n)).trans
    (QuotientGroup.quotientKerEquivOfRightInverse (positiveBassBoundary X n)
      (positiveBassUnitSection X n)
      (DFunLike.congr_fun (positiveBassBoundary_comp_unitSection X n)))

/-- The quotient equivalence evaluates on Laurent representatives by the original boundary. -/
theorem positiveBassQuotientEquiv_mk (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) (x : (W(Relative.laurentFunctor.obj X).obj).K (n + 1)) :
    positiveBassQuotientEquiv X n (QuotientGroup.mk x) = positiveBassBoundary X n x := by
  simp only [positiveBassQuotientEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- The inverse equivalence sends a coefficient to the class of the actual inverse unit. -/
theorem positiveBassQuotientEquiv_symm_apply (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) (x : (W X.obj).K n) :
    (positiveBassQuotientEquiv X n).symm x = QuotientGroup.mk (positiveBassUnitSection X n x) := by
  apply (positiveBassQuotientEquiv X n).injective
  rw [MulEquiv.apply_symm_apply, positiveBassQuotientEquiv_mk]
  exact (DFunLike.congr_fun (positiveBassBoundary_comp_unitSection X n) x).symm

end AlgebraicGeometry.Scheme.ProjectiveLine
