/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.DifferenceSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass

/-!
# Invertibility and Picard class of a divisor difference

These declarations retain the section-divisor convention from
`Colib.AlgebraicGeometry.EtaleCohomology.ClosedCurveDivisorRoot`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D E : X.IdealSheafData)

/-- The difference module of two effective Cartier divisors is invertible. -/
theorem isInvertible_differenceSheaf [IsEffectiveCartierDivisor D]
    [IsEffectiveCartierDivisor E] :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf (differenceSheaf D E) := by
  have hD : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      (invertibleSheaf' D) := isInvertible_invertibleSheaf_picard D
  have hE : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      (negativeTwist' E) := isInvertible_negativeTwist_picard E
  exact @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ X.presheaf
    X.ringCatIsSheaf _ _ _ _ hD hE

/-- The class of the chosen module is the positive divisor class minus the negative one. -/
theorem picardClass_differenceSheaf [IsEffectiveCartierDivisor D]
    [IsEffectiveCartierDivisor E] :
    X.picardClass (differenceSheaf D E) (isInvertible_differenceSheaf D E) =
      picardClass D - picardClass E := by
  have h := (X.picardClass_tensorSheaf (invertibleSheaf' D) (negativeTwist' E)
    (isInvertible_invertibleSheaf_picard D) (isInvertible_negativeTwist_picard E)
    (isInvertible_differenceSheaf D E)).symm
  have hsum : X.picardClass (differenceSheaf D E) (isInvertible_differenceSheaf D E) =
      picardClass D + negativeTwistPicardClass E := h
  rw [hsum, negativeTwistPicardClass_eq_neg, sub_eq_add_neg]

end Stacks.Divisors
