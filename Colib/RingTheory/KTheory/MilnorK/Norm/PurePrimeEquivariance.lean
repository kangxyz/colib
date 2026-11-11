/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenEquivariance
public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeInseparableChosenComparison

/-!
# Simultaneous equivariance in purely inseparable prime degree

The selected root presentation and its literal image under the coefficient
equivalence compute the native chosen norms.
-/

@[expose] public noncomputable section

open Polynomial Module

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

variable {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
  [Algebra k L] [Algebra k' L'] [FiniteDimensional k L] [FiniteDimensional k' L']
  [IsPurelyInseparable k L] [IsPurelyInseparable k' L']

/-- The original chosen norms in purely inseparable prime degree commute
with an actual simultaneous isomorphism of their field pairs. -/
theorem milnorKNormRing_map_ringEquiv_of_prime_of_isPurelyInseparable
    (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (x : MilnorKRing L) :
    milnorKRingMap σ.toRingHom (milnorKNormRing k L x) =
      milnorKNormRing k' L' (milnorKRingMap τ.toRingHom x) := by
  obtain ⟨a, _, f, hdegree, hchosen⟩ :=
    exists_selected_simpleMilnorNorm_presentation_of_prime hp
  let p := minpolyOfDegree k (Algebra.IsIntegral.isIntegral (R := k) a)
  obtain ⟨q, g, hq, hmap⟩ :=
    exists_monicIrreducible_presentation_ringEquiv σ τ hστ p f
  have hdegree' : finrank k' L' = (minpoly k a).natDegree := by
    rw [g.toLinearEquiv.finrank_eq, (AdjoinRoot.powerBasis (monic q).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, natDegree_eq]
  have hp' : Nat.Prime (finrank k' L') := by
    rw [hdegree', hdegree]
    exact hp
  have hleft := congrArg (milnorKRingMap σ.toRingHom) (hchosen x)
  have hsimple := simpleMilnorNorm_map_of_poly_eq_map σ.toRingHom p q hq
    (milnorKRingMap f.toRingHom x)
  have hcompLeft := milnorKRingMap_comp_apply f.toRingHom
    (AdjoinRoot.map σ.toRingHom (poly p) (poly q) (hq ▸ dvd_rfl)) x
  have hmaps := congrArg
    (fun ψ : L →+* AdjoinRoot (poly q) => milnorKRingMap ψ x) hmap
  have hcompRight := milnorKRingMap_comp_apply τ.toRingHom g.toRingHom x
  have hvalues := hcompLeft.trans (hmaps.trans hcompRight.symm)
  have hnorm := congrArg (simpleMilnorNorm q) hvalues
  have hright := milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_prime_of_isPurelyInseparable
    hp' q g (milnorKRingMap τ.toRingHom x)
  exact hleft.trans (hsimple.trans (hnorm.trans hright.symm))

/-- The simultaneous purely inseparable prime norm comparison on each
original homogeneous group. -/
theorem milnorKNorm_map_ringEquiv_of_prime_of_isPurelyInseparable
    (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTransport σ.toRingHom n (milnorKNorm k L n x) =
      milnorKNorm k' L' n (milnorKTransport τ.toRingHom n x) := by
  apply Subtype.ext
  exact milnorKNormRing_map_ringEquiv_of_prime_of_isPurelyInseparable hp σ τ hστ (x : MilnorKRing L)

end Stacks.Chow

end
