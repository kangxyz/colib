/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenInseparableTower
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenPureBaseChange
public import Colib.Util.References

import Colib.FieldTheory.IntermediateField.CompositumImage
import Colib.FieldTheory.PurelyInseparable.FiniteSeparabilization

/-!
# Restriction of a chosen Milnor norm tower to a separable compositum

Purely inseparable base change makes the two norm expressions in a finite
tower agree after restriction when the resulting compositum is separable.
The two inseparable-degree coefficients multiply to the total inseparable
degree before any detection argument.
-/

@[expose] public noncomputable section

open IntermediateField

universe u

namespace Stacks.Chow

/-- The two original norm expressions agree after a compatible purely
inseparable base change to a separable tower of composita. -/
theorem milnorKRingMap_milnorKNormRing_tower_of_pure_baseChange
    {K M L B C D : Type u} [Field K] [Field M] [Field L] [Field B] [Field C] [Field D]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [Algebra K B] [Algebra M C] [Algebra L D]
    [Algebra B C] [Algebra B D] [Algebra C D] [IsScalarTower B C D]
    [Algebra K C] [Algebra K D] [Algebra M D]
    [IsScalarTower K M C] [IsScalarTower K B C]
    [IsScalarTower M L D] [IsScalarTower M C D]
    [IsScalarTower K L D] [IsScalarTower K B D]
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]
    [FiniteDimensional B D] [IsPurelyInseparable K B] [IsPurelyInseparable M C]
    [Algebra.IsSeparable B D]
    (hC : IntermediateField.adjoin B (Set.range (algebraMap M C)) = ⊤)
    (hD : IntermediateField.adjoin B (Set.range (algebraMap L D)) = ⊤)
    (x : MilnorKRing L) :
    milnorKRingMap (algebraMap K B) (milnorKNormRing K M (milnorKNormRing M L x)) =
      milnorKRingMap (algebraMap K B) (milnorKNormRing K L x) := by
  let : FiniteDimensional B C := FiniteDimensional.left B C D
  let : FiniteDimensional C D := FiniteDimensional.right B C D
  let : Algebra.IsSeparable B C := Algebra.isSeparable_tower_bot_of_isSeparable B C D
  let : Algebra.IsSeparable C D := Algebra.isSeparable_tower_top_of_isSeparable B C D
  have hCD : IntermediateField.adjoin C (Set.range (algebraMap L D)) = ⊤ := by
    let S := IntermediateField.adjoin C (Set.range (algebraMap L D))
    have hle : IntermediateField.adjoin B (Set.range (algebraMap L D)) ≤
        S.restrictScalars B := IntermediateField.adjoin_le_iff.mpr
      (IntermediateField.subset_adjoin C (Set.range (algebraMap L D)))
    rw [hD] at hle
    exact (IntermediateField.restrictScalars_eq_top_iff (K := B)).mp (top_unique hle)
  calc
    _ = (Field.finInsepDegree K M : ℤ) •
          milnorKNormRing B C (milnorKRingMap (algebraMap M C) (milnorKNormRing M L x)) :=
      milnorKNormRing_baseChange_of_isPurelyInseparable hC _
    _ = (Field.finInsepDegree K L : ℤ) •
          milnorKNormRing B D (milnorKRingMap (algebraMap L D) x) := by
      rw [milnorKNormRing_baseChange_of_isPurelyInseparable hCD,
        map_zsmul, smul_smul, ← Nat.cast_mul,
        Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic K M L,
        milnorKNormRing_tower_of_isSeparable]
    _ = _ := (milnorKNormRing_baseChange_of_isPurelyInseparable hD x).symm

section FiniteTower

variable {K M L : Type u} [Field K] [Field M] [Field L]
  [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
  [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]

private theorem exists_finitePure_milnorKNormRing_tower_eq_after_restriction :
    ∃ B : IntermediateField K (AlgebraicClosure L),
      FiniteDimensional K B ∧ IsPurelyInseparable K B ∧
        ∀ x : MilnorKRing L,
          milnorKRingMap (algebraMap K B) (milnorKNormRing K M (milnorKNormRing M L x)) =
            milnorKRingMap (algebraMap K B) (milnorKNormRing K L x) := by
  let Ω := AlgebraicClosure L
  obtain ⟨B, hfinite, hpure, hsep⟩ := exists_finiteDimensional_isPurelyInseparable_isSeparable K L Ω
  let : IsPurelyInseparable K B := hpure
  let C := IntermediateField.adjoin B (Set.range (algebraMap M Ω))
  let D := IntermediateField.adjoin B (Set.range (algebraMap L Ω))
  let i := adjoinRangeFactor M B Ω
  let j := adjoinRangeFactor L B Ω
  let : Algebra M C := i.toAlgebra
  let : Algebra L D := j.toAlgebra
  have hCD : C ≤ D := by
    apply IntermediateField.adjoin.mono
    rintro _ ⟨m, rfl⟩
    exact ⟨algebraMap M L m, (IsScalarTower.algebraMap_apply M L Ω m).symm⟩
  let : Algebra C D := (IntermediateField.inclusion hCD).toRingHom.toAlgebra
  let : Algebra M D := ((algebraMap L D).comp (algebraMap M L)).toAlgebra
  let : IsScalarTower M L D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower B C D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower M C D := IsScalarTower.of_algebraMap_eq fun m =>
    (algebraMap D Ω).injective (IsScalarTower.algebraMap_apply M L Ω m).symm
  let : IsScalarTower K M C := IsScalarTower.of_algebraMap_eq fun k =>
    (algebraMap C Ω).injective (IsScalarTower.algebraMap_apply K M Ω k)
  let : IsScalarTower K L D := IsScalarTower.of_algebraMap_eq fun k =>
    (algebraMap D Ω).injective (IsScalarTower.algebraMap_apply K L Ω k)
  let : FiniteDimensional B D := finiteDimensional_adjoin_range_of_finiteDimensional K L B Ω
  let : IsPurelyInseparable M C := isPurelyInseparable_adjoin_range K M B Ω
  let : Algebra.IsSeparable B D :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable B Ω).mpr <| by
      rintro _ ⟨l, rfl⟩
      exact hsep l
  exact ⟨B, hfinite, hpure, milnorKRingMap_milnorKNormRing_tower_of_pure_baseChange
    (adjoin_range_adjoinRangeFactor_eq_top M B Ω)
    (adjoin_range_adjoinRangeFactor_eq_top L B Ω)⟩

/-- In any finite field tower, a power of the exponential characteristic
depending only on the tower kills the difference of the two chosen norm maps. -/
theorem exists_pow_zsmul_milnorKNormRing_tower_sub_eq_zero
    {p : ℕ} [ExpChar K p] :
    ∃ e : ℕ, ∀ x : MilnorKRing L, ((p ^ e : ℕ) : ℤ) •
      (milnorKNormRing K M (milnorKNormRing M L x) - milnorKNormRing K L x) = 0 := by
  obtain ⟨B, hfinite, hpure, heq⟩ :=
    exists_finitePure_milnorKNormRing_tower_eq_after_restriction (K := K) (M := M) (L := L)
  let : FiniteDimensional K B := hfinite
  let : IsPurelyInseparable K B := hpure
  obtain ⟨e, he⟩ := IsPurelyInseparable.finrank_eq_pow K B p
  refine ⟨e, fun x => ?_⟩
  rw [← he]
  apply finrank_zsmul_eq_zero_of_milnorKRingMap_eq_zero K B
  rw [map_sub, heq x, sub_self]

/-- Injectivity of multiplication by the exponential characteristic on the
base Milnor ring implies transitivity of the original chosen whole-ring norms. -/
theorem milnorKNormRing_comp_milnorKNormRing_of_injective_nsmul
    {p : ℕ} [ExpChar K p] (h : Function.Injective (fun x : MilnorKRing K => p • x)) :
    (milnorKNormRing K M).comp (milnorKNormRing M L) = milnorKNormRing K L := by
  apply AddMonoidHom.ext
  obtain ⟨B, hfinite, hpure, heq⟩ :=
    exists_finitePure_milnorKNormRing_tower_eq_after_restriction (K := K) (M := M) (L := L)
  let : FiniteDimensional K B := hfinite
  let : IsPurelyInseparable K B := hpure
  intro x
  exact milnorKRingMap_injective_of_isPurelyInseparable_of_injective_nsmul h (heq x)

/-- Under the same injectivity premise the original homogeneous norm maps
compose in every degree. -/
theorem milnorKNorm_comp_milnorKNorm_of_injective_nsmul
    {p : ℕ} [ExpChar K p] (h : Function.Injective (fun x : MilnorKRing K => p • x))
    (n : ℕ) : (milnorKNorm K M n).comp (milnorKNorm M L n) = milnorKNorm K L n := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun
    (milnorKNormRing_comp_milnorKNormRing_of_injective_nsmul (M := M) (L := L) h)
    (x : MilnorKRing L)

/-- Injectivity in each native homogeneous degree suffices for the integral
tower law. The native internal grading supplies the whole-ring hypothesis. -/
theorem milnorKNorm_comp_milnorKNorm_of_degreewise_injective_nsmul
    {p : ℕ} [ExpChar K p]
    (h : ∀ i : ℕ, Function.Injective (fun x : MilnorKTheory K i => p • x))
    (n : ℕ) : (milnorKNorm K M n).comp (milnorKNorm M L n) = milnorKNorm K L n := by
  apply milnorKNorm_comp_milnorKNorm_of_injective_nsmul (p := p) _ n
  intro x y hxy
  let e := DirectSum.decomposeAddEquiv (milnorKGrading K)
  apply e.injective
  apply DirectSum.ext
  intro i
  have he : p • e x = p • e y := by
    simpa only [map_nsmul] using congrArg e hxy
  let d : DirectSum ℕ (fun i => MilnorKTheory K i) →+ MilnorKTheory K i :=
    DFinsupp.evalAddMonoidHom i
  apply h i
  change p • d (e x) = p • d (e y)
  simpa only [map_nsmul] using congrArg d he

end FiniteTower

attribute [colib_tag "COL-1022"]
  milnorKRingMap_milnorKNormRing_of_isPurelyInseparable
  milnorKNormRing_baseChange_of_isPurelyInseparable
  exists_pow_zsmul_milnorKNormRing_tower_sub_eq_zero
  milnorKNorm_comp_milnorKNorm_of_injective_nsmul
  milnorKNorm_comp_milnorKNorm_of_degreewise_injective_nsmul

end Stacks.Chow

end
