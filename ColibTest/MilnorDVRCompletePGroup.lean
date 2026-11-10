/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompletePGroup

/-! Direct consumers of the original chosen-norm DVR square migration. -/

noncomputable section

open Stacks.Chow IsLocalRing

universe u v

example
    {R S T : Type v} {F E L : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra R T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R T)]
    [CharZero (ResidueField R)]
    [FiniteDimensional (ResidueField R) (ResidueField S)]
    [FiniteDimensional (ResidueField R) (ResidueField T)]
    [Field F] [CharZero F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [FiniteDimensional F E] [FiniteDimensional F L]
    [Algebra R F] [IsFractionRing R F]
    [Algebra S E] [IsFractionRing S E] [Algebra T L] [IsFractionRing T L]
    (j : S ≃ₐ[R] T) (ε : E ≃ₐ[F] L)
    (hε : ∀ s : S, ε (algebraMap S E s) = algebraMap T L (j s))
    (n : ℕ)
    (hsource : ∀ y : MilnorKTheory E (n + 1),
      dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) y) =
        milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n y))
    (x : MilnorKTheory L (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F L (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField T) n (dvrMilnorTameSymbol' T L n x) := by
  exact dvrMilnorTameSymbol'_milnorKNorm_of_algEquiv j ε hε n hsource x

example
    (R S T : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]
    [IsLocalHom (algebraMap R T)]
    [CharZero (ResidueField R)]
    [FiniteDimensional (ResidueField R) (ResidueField S)]
    [FiniteDimensional (ResidueField S) (ResidueField T)]
    [FiniteDimensional (ResidueField R) (ResidueField T)]
    (F E L : Type u) [Field F] [CharZero F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [FiniteDimensional F E] [FiniteDimensional E L] [FiniteDimensional F L]
    [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
    [Algebra T L] [IsFractionRing T L]
    (n : ℕ)
    (lower : ∀ y : MilnorKTheory E (n + 1),
      dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) y) =
        milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n y))
    (upper : ∀ z : MilnorKTheory L (n + 1),
      dvrMilnorTameSymbol' S E n (milnorKNorm E L (n + 1) z) =
        milnorKNorm (ResidueField S) (ResidueField T) n (dvrMilnorTameSymbol' T L n z))
    (x : MilnorKTheory L (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F L (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField T) n (dvrMilnorTameSymbol' T L n x) := by
  exact dvrMilnorTameSymbol'_milnorKNorm_of_tower R S T F E L n lower upper x

example
    (R S : Type v) (F E : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero (ResidueField R)]
    [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra R E] [IsScalarTower R F E]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E]
    (hd : Module.finrank F E = 1) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  exact dvrMilnorTameSymbol'_milnorKNorm_of_finrank_eq_one R S F E hd n x

example
    (R S F E Ω : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field F] [CharZero F] [Field E] [CharZero E] [Field Ω]
    [Algebra R F] [IsFractionRing R F]
    [Algebra F E] [FiniteDimensional F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E]
    [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[F] Ω)) (g : E →ₐ[F] Ω)
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  exact dvrMilnorTameSymbol'_milnorKNorm_complete_of_pGroup R S F E Ω ℓ hG g n x

end
