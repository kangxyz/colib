/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompleteRamifiedBranch

/-! Full-hypothesis consumer of the literal ramification-weighted upper branch square. -/

noncomputable section

open Stacks.Chow IsLocalRing

universe u

example
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
  exact dvrMilnorTameSymbol'_milnorKNorm_map_complete_of_pGroup
    S T U E L D Ω ℓ hG g j f hf hϖ hρ w b hb n x

end
