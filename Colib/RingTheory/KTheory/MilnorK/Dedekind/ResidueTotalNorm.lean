/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Dedekind.ResiduePushforward
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# The actual finite sum of normed residues of a Dedekind model

The sum uses the proved finite support of the original residues. Each
coefficient is the actual finite field norm, in every Milnor degree.
-/

/-! Adapted from Aglib `Dedekind/ResidueTotalNorm.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`. Original models and hypotheses are
retained; native chosen norms and tame symbols replace the separate Milnor presentation. -/

@[expose] public noncomputable section

namespace Stacks.Chow.DedekindResidue

open IsLocalRing IsDedekindDomain

universe u

variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k S]
  [∀ q : HeightOneSpectrum S, FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal))]
  [Field E] [Algebra S E] [IsFractionRing S E]

open scoped Classical in
/-- The actual finite residue norms summed on the dependent finite support. -/
def totalNorm (n : ℕ) :
    (Π₀ q : HeightOneSpectrum S, MilnorKTheory (ResidueField (Localization.AtPrime q.asIdeal)) n)
      →ₗ[ℤ] MilnorKTheory k n :=
  DFinsupp.lsum ℤ fun q => (milnorKNorm k
    (ResidueField (Localization.AtPrime q.asIdeal)) n).toIntLinearMap

omit [CharZero k] [IsDedekindDomain S] in
open scoped Classical in
/-- The total norm is the literal sum over the actual residual support. -/
theorem totalNorm_eq_sum (n : ℕ)
    (y : Π₀ q : HeightOneSpectrum S,
      MilnorKTheory (ResidueField (Localization.AtPrime q.asIdeal)) n) :
    totalNorm k S n y = ∑ q ∈ y.support,
      milnorKNorm k (ResidueField (Localization.AtPrime q.asIdeal)) n (y q) := by
  simp only [totalNorm, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
    LinearMap.toAddMonoidHom_coe, AddMonoidHom.coe_toIntLinearMap, DFinsupp.sum]

omit [CharZero k] [IsDedekindDomain S] in
/-- The same actual total norm is the finitely supported sum over all points. -/
theorem totalNorm_eq_finsum (n : ℕ)
    (y : Π₀ q : HeightOneSpectrum S,
      MilnorKTheory (ResidueField (Localization.AtPrime q.asIdeal)) n) :
    totalNorm k S n y = ∑ᶠ q : HeightOneSpectrum S,
      milnorKNorm k (ResidueField (Localization.AtPrime q.asIdeal)) n (y q) := by
  classical
  rw [totalNorm_eq_sum]
  symm
  apply finsum_eq_sum_of_support_subset
  intro q hq
  apply DFinsupp.mem_support_iff.mpr
  intro hy
  exact hq (by
    change milnorKNorm k (ResidueField (Localization.AtPrime q.asIdeal)) n (y q) = 0
    rw [hy, map_zero])

/-- The original affine curve boundary sum, before adding its points at infinity. -/
def normedTotalResidue (n : ℕ) : MilnorKTheory E (n + 1) →ₗ[ℤ] MilnorKTheory k n :=
  (totalNorm k S n).comp (totalResidue S E n)

omit [CharZero k] in
open scoped Classical in
/-- Every term is an original local residue followed by its actual residue-field norm. -/
theorem normedTotalResidue_eq_sum (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    normedTotalResidue k S E n x =
      ∑ q ∈ (totalResidue S E n x).support,
        milnorKNorm k (ResidueField (Localization.AtPrime q.asIdeal)) n
          (dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n x) := by
  exact totalNorm_eq_sum k S n (totalResidue S E n x)

end Stacks.Chow.DedekindResidue
