/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The determinant of a rank-one update

Adapted from `Motivic/Aglib/LinearAlgebra/Determinant/RankOne.lean` at
a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

namespace LinearMap

/-- The determinant of a rank-one update of the identity on a finite free module. -/
theorem det_id_add_smulRight
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Free R M] (f : M →ₗ[R] R) (v : M) :
    LinearMap.det (LinearMap.id + f.smulRight v) = 1 + f v := by
  classical
  let b := Module.Free.chooseBasis R M
  rw [← det_toMatrix b, map_add, toMatrix_id, toMatrix_smulRight,
    Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simpa only [dotProduct, Function.comp_apply, map_sum, map_smul, smul_eq_mul, mul_comm] using
    congrArg f (b.sum_repr v)

end LinearMap
