/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRMixed

import Colib.RingTheory.Norm.DVRPrimeUniformizerFinite

/-!
# The prime-degree DVR norm square on the mixed span

The exact uniformizer coefficient supplies the native mixed-span square in
every residue characteristic.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Chow

variable (R S : Type u) (F E : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E] {π : R} {ϖ : S}

/-- In prime fraction-field degree, the native norm–residue square on the mixed span
holds in every residue characteristic. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_prime_degree_any
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (hp : Nat.Prime (Module.finrank F E))
    (m : ℕ) (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) := by
  obtain ⟨b₀, hb₀, hres⟩ :=
    IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_prime_degree_any
      R S F E hπ hϖ u e he hp
  exact dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_exact_coefficient
    R S F E hπ hϖ u e he b₀ hb₀ hres m x hx

end Stacks.Chow
