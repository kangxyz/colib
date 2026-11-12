/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.IntegralAffine
import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.FiniteField.Coefficient
import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.InfiniteField

/-!
# Integral-affine local vanishing over an arbitrary field

The finite-field descent and the infinite-field presentation prove the
same original-target local-zero property.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

/-- The finite and infinite geometric arguments supply the original zero neighborhoods. -/
theorem integralAffineLocalZero_of_field (k : Type u) [Field k] : IntegralAffineLocalZero k := by
  cases finite_or_infinite k
  · exact integralAffineLocalZero_of_finite k
  · exact integralAffineLocalZero_of_infinite k

end AlgebraicGeometry.PresheafWithTransfers
