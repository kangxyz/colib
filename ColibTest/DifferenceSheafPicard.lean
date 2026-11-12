/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.DifferenceSheafPicard

/-!
# Tests for invertibility and signs of divisor-difference Picard classes
-/

open AlgebraicGeometry Stacks.Divisors

universe u

variable {X : Scheme.{u}} (D E : X.IdealSheafData)
  [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]

example : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
    (differenceSheaf D E) :=
  isInvertible_differenceSheaf D E

example : X.picardClass (differenceSheaf D E) (isInvertible_differenceSheaf D E) =
    picardClass D - picardClass E :=
  picardClass_differenceSheaf D E

example : X.picardClass (differenceSheaf D D) (isInvertible_differenceSheaf D D) = 0 := by
  rw [picardClass_differenceSheaf, sub_self]

example : X.picardClass (differenceSheaf E D) (isInvertible_differenceSheaf E D) =
    -X.picardClass (differenceSheaf D E) (isInvertible_differenceSheaf D E) := by
  rw [picardClass_differenceSheaf, picardClass_differenceSheaf, neg_sub]

#print axioms Stacks.Divisors.isInvertible_differenceSheaf
#print axioms Stacks.Divisors.picardClass_differenceSheaf
