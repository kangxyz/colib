/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeChosenComparisonSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.FieldPresentationEquivariance

/-!
# Simultaneous equivariance of separable normal-prime chosen norms

The original algebra maps commute with the supplied base and extension ring
equivalences. Source normality, separability, and prime degree imply the target
properties through those actual equivalences. The actual polynomial presentation
square and the simple norm coefficient square then identify the native chosen
norms on the original fields.

This adapts `ChosenEquivariance` using only the normal-prime chosen comparison.
It does not use a general chosen-norm tower or presentation-independence theorem.
There is no transported scalar action, replacement norm, or norm-square premise.
The base is arbitrary, and the prime extension degree may equal its characteristic.
-/

@[expose] public noncomputable section

open Polynomial Module

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

local instance normalPrimeEquivarianceFactIrreducibleSeparable {k : Type u} [Field k] {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

variable {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
  [Algebra k L] [Algebra k' L'] [FiniteDimensional k L] [FiniteDimensional k' L']
  [hsep : Algebra.IsSeparable k L] [hnormal : Normal k L]

include hsep hnormal

/-- The native chosen norm in separable normal prime degree commutes with
simultaneous base and extension equivalences on the original algebra structures.
Only the source extension is assumed separable, normal, and of prime degree. -/
theorem milnorKNormRing_map_ringEquiv_of_normal_prime_of_separable
    (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (x : MilnorKRing L) :
    milnorKRingMap σ.toRingHom (milnorKNormRing k L x) =
      milnorKNormRing k' L' (milnorKRingMap τ.toRingHom x) := by
  let : Normal k' L' := Normal.of_equiv_equiv hστ.symm
  let : Algebra.IsSeparable k' L' :=
    (Algebra.IsSeparable.iff_of_equiv_equiv σ τ hστ.symm).mp hsep
  have hp' : Nat.Prime (finrank k' L') := by
    rw [← Algebra.finrank_eq_of_equiv_equiv σ τ hστ.symm]
    exact hp
  obtain ⟨d, p, ⟨f⟩⟩ := exists_monicIrreducible_presentation k L
  obtain ⟨q, g, hq, hmap⟩ :=
    exists_monicIrreducible_presentation_ringEquiv σ τ hστ p f
  have hleft := congrArg (milnorKRingMap σ.toRingHom)
    (milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime_of_separable hp p f x)
  have hsimple := simpleMilnorNorm_map_of_poly_eq_map σ.toRingHom p q hq
    (milnorKRingMap f.toRingHom x)
  have hcompLeft := milnorKRingMap_comp_apply f.toRingHom
    (AdjoinRoot.map σ.toRingHom (poly p) (poly q) (hq ▸ dvd_rfl)) x
  have hmaps := congrArg
    (fun ψ : L →+* AdjoinRoot (poly q) => milnorKRingMap ψ x) hmap
  have hcompRight := milnorKRingMap_comp_apply τ.toRingHom g.toRingHom x
  have hvalues := hcompLeft.trans (hmaps.trans hcompRight.symm)
  have hnorm := congrArg (simpleMilnorNorm q) hvalues
  have hright :=
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime_of_separable hp' q g
      (milnorKRingMap τ.toRingHom x)
  exact hleft.trans (hsimple.trans (hnorm.trans hright.symm))

/-- The simultaneous equivalence square as equality of the native additive maps. -/
theorem milnorKNormRing_comp_map_ringEquiv_of_normal_prime_of_separable
    (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) :
    (milnorKRingMap σ.toRingHom).toAddMonoidHom.comp (milnorKNormRing k L) =
      (milnorKNormRing k' L').comp (milnorKRingMap τ.toRingHom).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKNormRing_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ x

/-- Simultaneous equivariance on every native homogeneous Milnor group,
including homogeneous degree zero. -/
theorem milnorKNorm_map_ringEquiv_of_normal_prime_of_separable
    (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTransport σ.toRingHom n (milnorKNorm k L n x) =
      milnorKNorm k' L' n (milnorKTransport τ.toRingHom n x) := by
  apply Subtype.ext
  exact milnorKNormRing_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ
    (x : MilnorKRing L)

/-- Simultaneous equivariance as equality of the native homogeneous additive maps. -/
theorem milnorKNorm_comp_map_ringEquiv_of_normal_prime_of_separable
    (hp : Nat.Prime (finrank k L)) (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (n : ℕ) :
    (milnorKTransport σ.toRingHom n).comp (milnorKNorm k L n) =
      (milnorKNorm k' L' n).comp (milnorKTransport τ.toRingHom n) := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKNorm_map_ringEquiv_of_normal_prime_of_separable hp σ τ hστ n x

end Stacks.Chow

end
