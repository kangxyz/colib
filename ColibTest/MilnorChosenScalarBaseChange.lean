/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenScalarBaseChange
import Colib.RingTheory.KTheory.MilnorK.Norm.FieldPresentation

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k L] [FiniteDimensional k L] [CharZero k]

/-- The consumer supplies no target characteristic, algebra action, or finite witness. -/
example (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
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
            ((AdjoinRoot.map φ (poly p) (poly q.1.2) q.2).comp f.toRingHom) x) :=
  milnorKNormRing_map_eq_sum_scalarFactors_of_algEquiv φ p f x

/-- Native tuple symbols retain the actual coordinatewise composite branch map. -/
example (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] AdjoinRoot (poly p)) (n : ℕ) (a : Fin n → Lˣ) :
    let _ := coefficientFactorFintype φ (poly p) (ne_zero p)
    let _ : ∀ q : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
        poly r.2 ∣ (poly p).map φ}, FiniteDimensional K (AdjoinRoot (poly q.1.2)) :=
      fun q => (AdjoinRoot.powerBasis' (monic q.1.2)).finite
    milnorKTransport φ n (milnorKNorm k L n (milnorKTupleSymbol a)) =
      ∑ q : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
          poly r.2 ∣ (poly p).map φ},
        milnorKNorm K (AdjoinRoot (poly q.1.2)) n
          (milnorKTupleSymbol
            (Units.map
              ((AdjoinRoot.map φ (poly p) (poly q.1.2) q.2).comp f.toRingHom).toMonoidHom
                ∘ a)) := by
  intro hFactors hFinite
  simpa only [milnorKTransport_tupleSymbol] using
    milnorKNorm_map_eq_sum_scalarFactors_of_algEquiv φ p f n (milnorKTupleSymbol a)

/-- Every finite extension admits a presentation in which the full formula holds
simultaneously for all whole-ring classes. -/
example (φ : k →+* K) :
    ∃ (d : ℕ) (p : MonicIrreducibleOfDegree k d)
      (f : L ≃ₐ[k] AdjoinRoot (poly p)),
      let _ := coefficientFactorFintype φ (poly p) (ne_zero p)
      let _ : ∀ q : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
          poly r.2 ∣ (poly p).map φ}, FiniteDimensional K (AdjoinRoot (poly q.1.2)) :=
        fun q => (AdjoinRoot.powerBasis' (monic q.1.2)).finite
      ∀ x : MilnorKRing L, milnorKRingMap φ (milnorKNormRing k L x) =
        ∑ q : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
            poly r.2 ∣ (poly p).map φ},
          milnorKNormRing K (AdjoinRoot (poly q.1.2))
            (milnorKRingMap
              ((AdjoinRoot.map φ (poly p) (poly q.1.2) q.2).comp f.toRingHom) x) := by
  obtain ⟨d, p, ⟨f⟩⟩ := exists_monicIrreducible_presentation k L
  refine ⟨d, p, f, ?_⟩
  intro hFactors hFinite x
  exact milnorKNormRing_map_eq_sum_scalarFactors_of_algEquiv φ p f x

end
