/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.UnitNorm
public import Colib.Util.References

/-!
# Norms of linear factors in the complete monic root algebra

The norm of `a - t` in the full finite free algebra `R[t]/(p)` is `p(a)`. In particular,
`Norm(1 - t) = 1 - a` in `R[t]/(t^n - a)`, without an irreducibility assumption. This is the
finite-algebra identity needed by the norm argument for the Steinberg relation; no étale
cohomological projection formula or Steinberg vanishing is asserted here.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R]

/-- Norm of a linear factor in the actual complete monic polynomial quotient. -/
@[colib_tag "COL-1230",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/RingTheory/Norm/Defs.lean:82"
    "ingredient" "Native determinant norm in the actual power basis",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean:144"
    "ingredient" "Evaluation of the characteristic polynomial as a scalar-minus-matrix determinant",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/LinearAlgebra/Matrix/Charpoly/Minpoly.lean:71"
    "ingredient" "The power-basis characteristic polynomial equals the minimal polynomial",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksCore/RingTheory/Polynomial/FreeQuotient.lean:51"
    "ingredient" "The monic polynomial is the minimal polynomial of its literal quotient root"]
theorem norm_algebraMap_sub_root_of_monic (p : R[X]) (hp : p.Monic) (a : R) :
    Algebra.norm R (algebraMap R (AdjoinRoot p) a - root p) = p.eval a := by
  let b := powerBasis' hp
  rw [Algebra.norm_eq_matrix_det b.basis, map_sub, AlgHom.commutes]
  change (Matrix.scalar _ a - Algebra.leftMulMatrix b.basis b.gen).det = _
  rw [← Matrix.eval_charpoly, charpoly_leftMulMatrix b]
  exact congrArg (Polynomial.eval a) hp.minpoly_adjoinRoot

/-- The full root algebra has the norm identity used in the Steinberg argument. -/
theorem norm_one_sub_root_X_pow_sub_C (n : ℕ) (hn : 0 < n) (a : R) :
    Algebra.norm R (1 - root (X ^ n - C a : R[X])) = 1 - a := by
  simpa only [map_one, eval_sub, eval_pow, eval_X, one_pow, eval_C] using
    norm_algebraMap_sub_root_of_monic (X ^ n - C a) (monic_X_pow_sub_C a (Nat.ne_of_gt hn)) 1

end AdjoinRoot
