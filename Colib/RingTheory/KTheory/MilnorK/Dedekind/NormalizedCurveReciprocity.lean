/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Dedekind.AffineCurveNormedReciprocity
public import Colib.RingTheory.KTheory.MilnorK.Norm.InfinityBranches

/-! # Reciprocity on the original finite model and every original infinity branch -/

/-! Adapted from Aglib `Dedekind/NormalizedCurveReciprocity.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`. Original models and hypotheses are
retained; native chosen norms and tame symbols replace the separate Milnor presentation. -/

@[expose] public noncomputable section

namespace Stacks.Chow.DedekindResidue

open Polynomial IsLocalRing IsDedekindDomain

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S] [Algebra k S] [IsScalarTower k k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

/-- Reciprocity for a finite Dedekind model of the affine line, including every
branch of its original function field above infinity. -/
theorem normalized_curve_reciprocity (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    let : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := k[X])
      (inferInstanceAs (Algebra.FiniteType k k[X]))
      (inferInstanceAs (Algebra.FiniteType k[X] S))
    let : ∀ q : HeightOneSpectrum S,
        FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
      fun q => Localization.finiteType_localResidue_finite k S q.asIdeal
    normedTotalResidue k S E n x + infinityBranchResidueSum k E n x = 0 := by
  rw [← infinityResidue_milnorKNorm]
  exact affine_normed_reciprocity k S E n x

end Stacks.Chow.DedekindResidue
