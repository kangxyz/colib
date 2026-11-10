/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Dedekind.ResiduePushforward

/-! The local chosen norm square, with every original ideal branch written out. -/

noncomputable section

open Stacks.Chow IsLocalRing IsDedekindDomain AdicCompletion

attribute [local instance] Classical.decEq

universe u

variable (A S F E : Type u) [CommRing A] [IsDedekindDomain A]
  [CommRing S] [IsDedekindDomain S] [Algebra A S] [Module.Finite A S]
  [Module.IsTorsionFree A S]
  [Field F] [CharZero F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra A E] [IsScalarTower A S E]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]
  (p : HeightOneSpectrum A) [CharZero (ResidueField (Localization.AtPrime p.asIdeal))]

example (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' (Localization.AtPrime p.asIdeal) F n
      (milnorKNorm F E (n + 1) x) =
      ∑ q : IdealBranch (p.asIdeal.map (algebraMap A S)),
        originalBranchResidueNorm A S E p n x q :=
  dvrMilnorTameSymbol'_milnorKNorm_atPrime A S F E p n x

example (q : IdealBranch (p.asIdeal.map (algebraMap A S))) :
    (Localization.originalIdealBranchEquivLocalizedBranches p q).val =
      q.val.map (algebraMap S
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))) :=
  Localization.originalIdealBranchEquivLocalizedBranches_apply p q

example (q : IdealBranch (p.asIdeal.map (algebraMap A S))) :
    letI := Localization.basePrimeLocalAlgebra p.asIdeal q.val
      (Localization.originalIdealBranch_under p q)
    Localization.AtPrime (Localization.originalIdealBranchEquivLocalizedBranches p q).val ≃ₐ[
      Localization.AtPrime p.asIdeal] Localization.AtPrime q.val :=
  Localization.originalIdealBranchLocalEquiv p q

end
