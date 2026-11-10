/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Dedekind.ResidueDirectSum

/-! Full-statement consumers of the actual finitely supported chosen norm square. -/

noncomputable section

open Stacks.Chow Stacks.Chow.DedekindResidue IsLocalRing IsDedekindDomain AdicCompletion

attribute [local instance] Classical.decEq

universe u

variable (A S : Type u) [CommRing A] [IsDedekindDomain A]
  [CommRing S] [IsDedekindDomain S] [Algebra A S] [Module.Finite A S]
  [Module.IsTorsionFree A S]
  [∀ p : HeightOneSpectrum A, CharZero (ResidueField (Localization.AtPrime p.asIdeal))]

example (n : ℕ) (q : HeightOneSpectrum S)
    (x : MilnorKTheory (ResidueField (Localization.AtPrime q.asIdeal)) n) :
    residuePushforward A S n (DFinsupp.single q x) =
      DFinsupp.single (q.under A) (pointResidueNorm A S n q x) :=
  residuePushforward_single A S n q x

example (p : HeightOneSpectrum A) (n : ℕ)
    (y : Π₀ q : HeightOneSpectrum S,
      MilnorKTheory (ResidueField (Localization.AtPrime q.asIdeal)) n) :
    residuePushforward A S n y p =
      ∑ q : IdealBranch (p.asIdeal.map (algebraMap A S)),
        branchCoordinateNorm A S p n q (y (branchPoint A S p q)) :=
  residuePushforward_apply A S p n y

variable (F E : Type u) [Field F] [CharZero F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra A E] [IsScalarTower A S E]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]

example (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    totalResidue A F n (milnorKNorm F E (n + 1) x) =
      residuePushforward A S n (totalResidue S E n x) :=
  totalResidue_milnorKNorm A S F E n x

example (n : ℕ) :
    (totalResidue A F n).comp (milnorKNorm F E (n + 1)).toIntLinearMap =
      (residuePushforward A S n).comp (totalResidue S E n) :=
  totalResidue_comp_milnorKNorm A S F E n

example (x : MilnorKTheory E 1) :
    totalResidue A F 0 (milnorKNorm F E 1 x) =
      residuePushforward A S 0 (totalResidue S E 0 x) :=
  totalResidue_milnorKNorm A S F E 0 x

end
