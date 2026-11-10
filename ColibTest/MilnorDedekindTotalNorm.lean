/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Dedekind.ResidueNormPushforward

/-! Full-statement source consumers. These examples have not been compiled. -/

noncomputable section

open Stacks.Chow Stacks.Chow.DedekindResidue IsDedekindDomain IsLocalRing

universe u

section Sum

variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k S]
  [∀ q : HeightOneSpectrum S,
    FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal))]
  [Field E] [Algebra S E] [IsFractionRing S E]

open scoped Classical in
example (n : ℕ)
    (y : Π₀ q : HeightOneSpectrum S,
      MilnorKTheory (ResidueField (Localization.AtPrime q.asIdeal)) n) :
    totalNorm k S n y = ∑ q ∈ y.support,
      milnorKNorm k (ResidueField (Localization.AtPrime q.asIdeal)) n (y q) :=
  totalNorm_eq_sum k S n y

example (n : ℕ)
    (y : Π₀ q : HeightOneSpectrum S,
      MilnorKTheory (ResidueField (Localization.AtPrime q.asIdeal)) n) :
    totalNorm k S n y = ∑ᶠ q : HeightOneSpectrum S,
      milnorKNorm k (ResidueField (Localization.AtPrime q.asIdeal)) n (y q) :=
  totalNorm_eq_finsum k S n y

open scoped Classical in
example (x : MilnorKTheory E 1) :
    normedTotalResidue k S E 0 x =
      ∑ q ∈ (totalResidue S E 0 x).support,
        milnorKNorm k (ResidueField (Localization.AtPrime q.asIdeal)) 0
          (dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E 0 x) :=
  normedTotalResidue_eq_sum k S E 0 x

end Sum

section Pushforward

attribute [local instance] Classical.decEq

variable (k A S F E : Type u) [Field k] [CharZero k]
  [CommRing A] [IsDedekindDomain A] [CommRing S] [IsDedekindDomain S]
  [Algebra k A] [Algebra A S] [Algebra k S] [IsScalarTower k A S]
  [Module.Finite A S] [Module.IsTorsionFree A S]
  [∀ p : HeightOneSpectrum A, CharZero (ResidueField (Localization.AtPrime p.asIdeal))]
  [∀ p : HeightOneSpectrum A, FiniteDimensional k (ResidueField (Localization.AtPrime p.asIdeal))]
  [∀ q : HeightOneSpectrum S, FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal))]
  [Field F] [CharZero F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra A E] [IsScalarTower A S E]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]

example (n : ℕ) :
    (totalNorm k A n).comp (residuePushforward A S n) = totalNorm k S n :=
  totalNorm_comp_residuePushforward k A S n

example (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    normedTotalResidue k A F n (milnorKNorm F E (n + 1) x) =
      normedTotalResidue k S E n x :=
  normedTotalResidue_milnorKNorm k A S F E n x

example (x : MilnorKTheory E 1) :
    normedTotalResidue k A F 0 (milnorKNorm F E 1 x) =
      normedTotalResidue k S E 0 x :=
  normedTotalResidue_milnorKNorm k A S F E 0 x

end Pushforward
