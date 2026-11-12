/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.LinearAlgebra.Determinant.RankOne
public import StacksFrontier.RingTheory.Norm.BaseChangeProduct

/-!
# Norms on a split marked factor

The determinant on a finite free algebra split as a scalar factor and
a residual factor computes the marked scalar when the residual value is one.
The residual algebra can be nonreduced.

Adapted from `Motivic/Aglib/RingTheory/Norm/FiniteFree/MarkedFiber.lean` at
a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

/-- On a finite free product, a scalar on the marked factor and one on the
residual factor have norm equal to the marked scalar. -/
theorem norm_prod_mk_one
    {R E : Type*} [CommRing R] [CommRing E] [Algebra R E]
    [Module.Finite R (R × E)] [Module.Free R (R × E)] (a : R) :
    norm R (a, (1 : E)) = a := by
  have h : lmul R (R × E) (a, 1) =
      LinearMap.id + (LinearMap.fst R R E).smulRight (a - 1, 0) := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply Prod.ext
    · change a * x = x + x * (a - 1)
      ring
    · change 1 * y = y + x • (0 : E)
      simp
  rw [norm_apply, h, LinearMap.det_id_add_smulRight]
  simp

/-- Arbitrary scalar base change of a finite free norm can be evaluated on
the marked component of the actual base-changed algebra. -/
theorem norm_eq_marked_value_of_split_baseChange
    {R Q S E : Type*} [CommRing R] [CommRing Q] [CommRing S] [CommRing E]
    [Algebra R Q] [Algebra R S] [Algebra Q E]
    [Module.Finite R S] [Module.Free R S]
    (e : (Q ⊗[R] S) ≃ₐ[Q] (Q × E)) (s : S) (a : Q)
    (h : e ((1 : Q) ⊗ₜ[R] s) = (a, 1)) :
    algebraMap R Q (norm R s) = a := by
  let : Module.Finite Q (Q × E) := Module.Finite.equiv e.toLinearEquiv
  let : Module.Free Q (Q × E) := Module.Free.of_equiv e.toLinearEquiv
  rw [← Stacks.Norm.norm_tmul_one, ← norm_eq_of_algEquiv e, h, norm_prod_mk_one]

end Algebra
