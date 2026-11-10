/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport
public import Colib.RingTheory.DiscreteValuationRing.RamificationDegree
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm

/-!
# Degree annihilation from actual ramified residue restriction

Adapted from `Aglib/KTheory/MilnorK/Norm/FiniteExtension/DVRRestrictionKernel.lean:25-48`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`. The native chosen
norm projection and native DVR degree formula do not require the original
perfectness, residue characteristic zero, or integral-closure hypotheses.
The ramification exponent is never cancelled in a Milnor group.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Stacks.Chow

universe u

/-- A ramification-weighted restriction kernel is killed by the actual fraction-field degree. -/
theorem finrank_smul_eq_zero_of_ramified_residue_restrict
    (R S F E : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [IsLocalHom (algebraMap R S)]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (n : ℕ) (z : MilnorKTheory (ResidueField R) n)
    (hz : e • milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n z = 0) :
    Module.finrank F E • z = 0 := by
  have hring : e • milnorKRingMap (algebraMap (ResidueField R) (ResidueField S))
      (z : MilnorKRing (ResidueField R)) = 0 := by
    have h := congrArg ((milnorKGrading (ResidueField S) n).subtype) hz
    simpa only [map_nsmul, map_zero, milnorKTheoryMap_eq_transport,
      AddMonoidHom.coe_toIntLinearMap, AddSubgroup.subtype_apply,
      milnorKTransport_coe] using h
  have hnorm := congrArg (milnorKNormRing (ResidueField R) (ResidueField S)) hring
  rw [map_nsmul, milnorKNormRing_milnorKRingMap, natCast_zsmul,
    map_zero, smul_smul] at hnorm
  rw [IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    R S F E hπ hϖ u e he]
  apply Subtype.ext
  exact hnorm

end Stacks.Chow

end
