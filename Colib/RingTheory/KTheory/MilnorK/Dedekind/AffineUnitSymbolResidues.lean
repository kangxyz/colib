/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Dedekind.AffineUnramifiedNorm
public import Colib.RingTheory.KTheory.MilnorK.Residue.Specialization
public import Colib.RingTheory.KTheory.MilnorK.Residue.CanonicalNormalization

/-!
# Original local orders of global unit symbols

Adapted from Aglib `Dedekind/AffineUnitSymbolResidues.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 21–58.
The native shift map computes the same last-slot integer order. All units,
residue fields and fraction fields are unchanged; no valuation model is added.
-/

@[expose] public noncomputable section

/-- Appending a unit to a tuple is the native right symbol multiplication. -/
theorem milnorKMulSymbol_tupleSymbol {F : Type*} [Field F] (n : ℕ)
    (a : Fin n → Fˣ) (b : Fˣ) :
    milnorKMulSymbol F n b (milnorKTupleSymbol a) = milnorKTupleSymbol (Fin.snoc a b) := by
  apply Subtype.ext
  simp only [coe_milnorKMulSymbol, coe_milnorKTupleSymbol, List.ofFn_succ',
    Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
    milnorKSymbolProd_append, milnorKSymbolProd_singleton]

namespace Stacks.Chow

section DVR

variable (R E : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field E] [Algebra R E] [IsFractionRing R E]

/-- The arbitrary last unit contributes its actual integer DVR order. -/
theorem dvrMilnorTameSymbol'_ringUnits_last (n : ℕ) (a : Fin n → Rˣ) (b : Eˣ) :
    dvrMilnorTameSymbol' R E n
      (milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap R E).toMonoidHom ∘ a) b)) =
      dvrFracOrd (IsDiscreteValuationRing.exists_irreducible R).choose_spec b •
        milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) := by
  apply Subtype.ext
  rw [dvrMilnorTameSymbol'_coe]
  have hs : (milnorKTupleSymbol
      (Fin.snoc (Units.map (algebraMap R E).toMonoidHom ∘ a) b) : MilnorKRing E) =
      unitSymbolProd E (List.ofFn a) * milnorKSymbol E b := by
    rw [← milnorKMulSymbol_tupleSymbol, coe_milnorKMulSymbol]
    simp only [coe_milnorKTupleSymbol, unitSymbolProd, List.map_ofFn, Function.comp_def]
    rfl
  rw [hs, map_mul, dvrMilnorShiftMap_unitSymbolProd, dvrMilnorShiftMap_milnorKSymbol,
    MilnorKShift.shift_mul, MilnorKShift.main_mk, MilnorKShift.shift_mk,
    main_dvrMilnorThetaHom, shift_dvrMilnorThetaHom]
  simp only [zero_mul, add_zero, AddSubgroupClass.coe_zsmul, coe_milnorKTupleSymbol]
  have hres : residueSymbolProd R (List.ofFn a) =
      milnorKSymbolProd (IsLocalRing.ResidueField R)
        (List.ofFn (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a)) := by
    simp only [residueSymbolProd, List.map_ofFn]
  rw [mul_smul_comm, mul_one, hres]

end DVR

namespace DedekindResidue
open IsDedekindDomain IsLocalRing
variable (S E : Type*) [CommRing S] [IsDedekindDomain S]
  [Field E] [Algebra S E] [IsFractionRing S E]

/-- Literal reduction and the actual order at an original affine branch. -/
theorem residue_ring_units_last (q : HeightOneSpectrum S) (n : ℕ)
    (a : Fin n → Sˣ) (b : Eˣ) :
    dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n
      (milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap S E).toMonoidHom ∘ a) b)) =
      dvrFracOrd (IsDiscreteValuationRing.exists_irreducible
        (Localization.AtPrime q.asIdeal)).choose_spec b •
        milnorKTupleSymbol (Units.map ((IsLocalRing.residue (Localization.AtPrime q.asIdeal)).comp
          (algebraMap S (Localization.AtPrime q.asIdeal))).toMonoidHom ∘ a) := by
  have h := dvrMilnorTameSymbol'_ringUnits_last (Localization.AtPrime q.asIdeal) E n
    (Units.map (algebraMap S (Localization.AtPrime q.asIdeal)).toMonoidHom ∘ a) b
  convert h using 2
  · apply congrArg milnorKTupleSymbol
    congr 1
    funext i
    apply Units.ext
    exact IsScalarTower.algebraMap_apply S (Localization.AtPrime q.asIdeal) E (a i)
  · rfl

end DedekindResidue
end Stacks.Chow
