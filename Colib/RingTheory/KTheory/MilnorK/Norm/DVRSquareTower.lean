/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTower
public import Colib.RingTheory.KTheory.MilnorK.Residue.Automorphism
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Composition of native DVR norm-residue squares

Adapted from `Aglib/KTheory/MilnorK/Norm/FiniteExtension/DVRResidueTower.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`. Both proved squares
remain explicit premises. The maps are the original native chosen norms and
canonical tame residues, in the supplied fraction and residue scalar towers.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open IsLocalRing

universe u v

/-- Two actual local norm-residue squares compose in their original scalar towers. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_tower
    (R S T : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]
    [IsLocalHom (algebraMap R T)]
    [CharZero (ResidueField R)] [CharZero (ResidueField S)]
    [FiniteDimensional (ResidueField R) (ResidueField S)]
    [FiniteDimensional (ResidueField S) (ResidueField T)]
    [FiniteDimensional (ResidueField R) (ResidueField T)]
    (F E L : Type u) [Field F] [CharZero F] [Field E] [CharZero E] [Field L]
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
  calc
    _ = dvrMilnorTameSymbol' R F n
        (milnorKNorm F E (n + 1) (milnorKNorm E L (n + 1) x)) := by
      rw [milnorKNorm_tower]
    _ = milnorKNorm (ResidueField R) (ResidueField S) n
        (dvrMilnorTameSymbol' S E n (milnorKNorm E L (n + 1) x)) := lower _
    _ = milnorKNorm (ResidueField R) (ResidueField S) n
        (milnorKNorm (ResidueField S) (ResidueField T) n (dvrMilnorTameSymbol' T L n x)) := by
      rw [upper]
    _ = _ := milnorKNorm_tower n _

end Stacks.Chow

end
