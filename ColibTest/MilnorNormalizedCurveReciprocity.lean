/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Dedekind.NormalizedCurveReciprocity

/-! Consumers of the complete finite-model reciprocity formula. -/

noncomputable section

open Stacks.Chow Stacks.Chow.DedekindResidue Polynomial IsLocalRing IsDedekindDomain

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S] [Algebra k S] [IsScalarTower k k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

example (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    let : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := k[X])
      (inferInstanceAs (Algebra.FiniteType k k[X]))
      (inferInstanceAs (Algebra.FiniteType k[X] S))
    let : ∀ q : HeightOneSpectrum S,
        FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
      fun q => Localization.finiteType_localResidue_finite k S q.asIdeal
    normedTotalResidue k S E n x + infinityBranchResidueSum k E n x = 0 :=
  normalized_curve_reciprocity k S E n x

example (x : MilnorKTheory E 1) :
    let : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := k[X])
      (inferInstanceAs (Algebra.FiniteType k k[X]))
      (inferInstanceAs (Algebra.FiniteType k[X] S))
    let : ∀ q : HeightOneSpectrum S,
        FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
      fun q => Localization.finiteType_localResidue_finite k S q.asIdeal
    normedTotalResidue k S E 0 x + infinityBranchResidueSum k E 0 x = 0 :=
  normalized_curve_reciprocity k S E 0 x

example (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    let : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := k[X])
      (inferInstanceAs (Algebra.FiniteType k k[X]))
      (inferInstanceAs (Algebra.FiniteType k[X] S))
    let : ∀ q : HeightOneSpectrum S,
        FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
      fun q => Localization.finiteType_localResidue_finite k S q.asIdeal
    normedTotalResidue k S E n x +
      infinityResidue (k := k) n (milnorKNorm (RatFunc k) E (n + 1) x) = 0 :=
  affine_normed_reciprocity k S E n x
