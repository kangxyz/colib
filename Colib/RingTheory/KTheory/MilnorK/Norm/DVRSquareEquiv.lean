/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTower
public import Colib.RingTheory.KTheory.MilnorK.Residue.Automorphism

/-!
# Transport of native DVR norm-residue squares

Adapted from `Aglib/KTheory/MilnorK/Norm/FiniteExtension/DVRResidueEquiv.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`. The field equivalence,
its integral restriction and the induced residue equivalence remain literal.
The source square is an explicit premise, not a claimed general DVR theorem.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open IsLocalRing

universe u v

/-- Actual compatible algebra equivalences transport a proved local norm-residue square. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_algEquiv
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
  have hex : ∃ y : MilnorKTheory E (n + 1), milnorKTheoryMap ε.toRingHom (n + 1) y = x := by
    refine ⟨milnorKTheoryMap ε.symm.toRingHom (n + 1) x, ?_⟩
    rw [← LinearMap.comp_apply, ← milnorKTheoryMap_comp]
    have hi : ε.toRingHom.comp ε.symm.toRingHom = RingHom.id L := by
      ext a
      exact ε.apply_symm_apply a
    rw [hi, milnorKTheoryMap_id, LinearMap.id_apply]
  obtain ⟨y, rfl⟩ := hex
  have hres := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ringEquiv j.toRingEquiv ε.toRingHom hε n) y
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe] at hres
  rw [milnorKNorm_map_algEquiv ε, hsource, hres]
  exact (milnorKNorm_map_algEquiv (ResidueField.mapAlgEquiv' j) n _).symm

end Stacks.Chow

end
