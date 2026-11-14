/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.AdjoinRoot.LinearFactorNorm
public import Mathlib.Algebra.Ring.GeomSum

/-!
# The unit-valued norm witness for the Steinberg norm argument

In the full algebra `R[t]/(t^n-a)`, the element `1-t` is a unit whenever `1-a` is a unit.
Its actual unit norm is the prescribed unit `1-a`. This does not assert a cohomological
projection formula or Steinberg cup vanishing.
-/

@[expose] public noncomputable section
open Polynomial
namespace AdjoinRoot
variable {R : Type*} [CommRing R]

/-- The literal root satisfies its defining power equation. -/
theorem root_X_pow_sub_C_pow (n : ℕ) (a : R) :
    root (X ^ n - C a) ^ n = algebraMap R (AdjoinRoot (X ^ n - C a)) a := by
  have h := mk_self (f := X ^ n - C a)
  rwa [← aeval_eq, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h

/-- The geometric-sum identity makes `1-t` a unit without any field assumption. -/
theorem isUnit_one_sub_root_X_pow_sub_C (n : ℕ) (a : R) (ha : IsUnit (1 - a)) :
    IsUnit (1 - root (X ^ n - C a : R[X])) := by
  apply isUnit_of_mul_isUnit_left
    (y := ∑ i ∈ Finset.range n, root (X ^ n - C a : R[X]) ^ i)
  rw [mul_neg_geom_sum, root_X_pow_sub_C_pow, ← map_one (algebraMap R _), ← map_sub]
  exact ha.map (algebraMap R (AdjoinRoot (X ^ n - C a)))

/-- The genuine unit `1-t` in the complete root algebra. -/
def oneSubRootUnit (n : ℕ) (a : R) (ha : IsUnit (1 - a)) :
    (AdjoinRoot (X ^ n - C a : R[X]))ˣ :=
  (isUnit_one_sub_root_X_pow_sub_C n a ha).unit

/-- Its underlying element is the literal `1-t`. -/
@[simp]
theorem oneSubRootUnit_val (n : ℕ) (a : R) (ha : IsUnit (1 - a)) :
    (oneSubRootUnit n a ha : AdjoinRoot (X ^ n - C a : R[X])) =
      1 - root (X ^ n - C a : R[X]) := IsUnit.unit_spec _

/-- The norm of the actual unit `1-t` is the actual unit `1-a`. -/
@[colib_tag "COL-1230"]
theorem norm_oneSubRootUnit (n : ℕ) (hn : 0 < n) (a : R) (ha : IsUnit (1 - a)) :
    Units.map (Algebra.norm R) (oneSubRootUnit n a ha) = ha.unit := by
  apply Units.ext
  change Algebra.norm R (oneSubRootUnit n a ha : AdjoinRoot (X ^ n - C a)) = _
  rw [oneSubRootUnit_val, norm_one_sub_root_X_pow_sub_C n hn a]
  exact (IsUnit.unit_spec ha).symm

end AdjoinRoot
end
