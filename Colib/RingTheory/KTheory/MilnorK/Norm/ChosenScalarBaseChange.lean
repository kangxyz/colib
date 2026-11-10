/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenComparison
public import Colib.RingTheory.KTheory.MilnorK.Norm.SeparableScalarFactors

import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Ring.CharZero

/-!
# Scalar base change for the original chosen finite Milnor norm

An actual polynomial presentation identifies the original chosen norm with the
original simple norm. Its complete scalar-factor formula then becomes a sum
of original chosen norms on the literal target quotients. Each branch map is
the actual quotient map composed with the supplied presentation.

The factor enumeration and target finiteness come from the existing native
coefficient-factor subtype and monic power bases. Characteristic zero of the
target follows from the injective field map. No target algebra structure over
the source, extra finiteness witness, or replacement norm is assumed.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k L] [FiniteDimensional k L] [CharZero k]

/-- In any actual polynomial presentation, scalar base change of the original
chosen norm is the sum of original chosen norms over all literal scalar factors. -/
theorem milnorKNormRing_map_eq_sum_scalarFactors_of_algEquiv
    (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] AdjoinRoot (poly p)) (x : MilnorKRing L) :
    let _ := coefficientFactorFintype φ (poly p) (ne_zero p)
    let _ : ∀ q : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
        poly r.2 ∣ (poly p).map φ}, FiniteDimensional K (AdjoinRoot (poly q.1.2)) :=
      fun q => (AdjoinRoot.powerBasis' (monic q.1.2)).finite
    milnorKRingMap φ (milnorKNormRing k L x) =
      ∑ q : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
          poly r.2 ∣ (poly p).map φ},
        milnorKNormRing K (AdjoinRoot (poly q.1.2))
          (milnorKRingMap
            ((AdjoinRoot.map φ (poly p) (poly q.1.2) q.2).comp f.toRingHom) x) := by
  intro hFactors hFinite
  let hCharZero : CharZero K := (RingHom.charZero_iff φ.injective).mp inferInstance
  rw [milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv p f]
  refine (simpleMilnorNorm_map_eq_sum_scalarFactors φ p
    (milnorKRingMap f.toRingHom x)).trans ?_
  apply Finset.sum_congr rfl
  intro q _
  rw [milnorKNormRing_eq_simpleMilnorNorm, milnorKRingMap_comp_apply]

/-- The same complete scalar-factor formula holds in every original homogeneous
Milnor group, using the original transport along each composite branch map. -/
theorem milnorKNorm_map_eq_sum_scalarFactors_of_algEquiv
    (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] AdjoinRoot (poly p)) (n : ℕ) (x : MilnorKTheory L n) :
    let _ := coefficientFactorFintype φ (poly p) (ne_zero p)
    let _ : ∀ q : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
        poly r.2 ∣ (poly p).map φ}, FiniteDimensional K (AdjoinRoot (poly q.1.2)) :=
      fun q => (AdjoinRoot.powerBasis' (monic q.1.2)).finite
    milnorKTransport φ n (milnorKNorm k L n x) =
      ∑ q : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
          poly r.2 ∣ (poly p).map φ},
        milnorKNorm K (AdjoinRoot (poly q.1.2)) n
          (milnorKTransport
            ((AdjoinRoot.map φ (poly p) (poly q.1.2) q.2).comp f.toRingHom) n x) := by
  intro hFactors hFinite
  apply Subtype.ext
  simpa only [milnorKTransport_coe, coe_milnorKNorm,
    AddSubmonoidClass.coe_finsetSum] using
    milnorKNormRing_map_eq_sum_scalarFactors_of_algEquiv φ p f (x : MilnorKRing L)

end Stacks.Chow

end
