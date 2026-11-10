/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompletePGroup
public import Colib.RingTheory.KTheory.MilnorK.Residue.CanonicalRamifiedMap

/-!
# The ramification-weighted upper branch square

The proved complete p-group square is applied after the actual upper field
restriction. Ramified residue naturality supplies exactly the upper vertical
ramification exponent, with no compatibility premise or exponent cancellation.

Adapted from `Aglib/KTheory/MilnorK/Norm/FiniteExtension/CompleteRamifiedBranch.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 24–53.
The original complete p-group norm square and specified ramification equation are retained;
the maps here are the native chosen norm and canonical tame symbol.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open IsLocalRing

universe u

/-- Each actual upper p-group branch contributes its literal ramification weight. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_map_complete_of_pGroup
    (S T U E L D Ω : Type u)
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [IsAdicComplete (maximalIdeal T) T] [CharZero (ResidueField T)]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Field L] [CharZero L] [Algebra T L] [IsFractionRing T L]
    [Field D] [CharZero D] [Algebra L D] [FiniteDimensional L D]
    [Algebra T D] [IsScalarTower T L D]
    [Algebra T U] [Module.Finite T U] [IsLocalHom (algebraMap T U)]
    [Algebra U D] [IsScalarTower T U D] [IsFractionRing U D]
    [IsIntegralClosure U T D]
    [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω)) (g : D →ₐ[L] Ω)
    (j : S →+* U) [IsLocalHom j] (f : E →+* D)
    (hf : ∀ s, f (algebraMap S E s) = algebraMap U D (j s))
    {ϖ : S} {ρ : U} (hϖ : Irreducible ϖ) (hρ : Irreducible ρ)
    (w : Uˣ) (b : ℕ) (hb : j ϖ = (w : U) * ρ ^ b)
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' T L n (milnorKNorm L D (n + 1) (milnorKTheoryMap f (n + 1) x)) =
      b • milnorKNorm (ResidueField T) (ResidueField U) n
        (milnorKTheoryMap (ResidueField.map j) n (dvrMilnorTameSymbol' S E n x)) := by
  have hr := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ramified j f hf hϖ hρ w b hb n) x
  change dvrMilnorTameSymbol' U D n (milnorKTheoryMap f (n + 1) x) =
    (b : ℤ) • milnorKTheoryMap (ResidueField.map j) n
      (dvrMilnorTameSymbol' S E n x) at hr
  rw [dvrMilnorTameSymbol'_milnorKNorm_complete_of_pGroup T U L D Ω ℓ hG g,
    hr, map_zsmul, natCast_zsmul]

end Stacks.Chow

end
