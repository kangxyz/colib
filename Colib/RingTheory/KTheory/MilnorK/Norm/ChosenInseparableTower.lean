/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenInseparableTrace
public import Colib.RingTheory.KTheory.MilnorK.RestrictionKernel

/-!
# Restriction of the chosen norms in purely inseparable towers

The literal chosen norm and the composition of chosen norms have equal
restrictions to the top field. The resulting difference is killed by the
total field degree. Injectivity of multiplication by the exponential
characteristic implies injectivity of purely inseparable restriction.
-/

@[expose] public noncomputable section

universe u

open _root_.Module

namespace Stacks.Chow

/-- Injectivity of multiplication by the exponential characteristic detects
restriction to a finite purely inseparable extension on the native Milnor ring. -/
theorem milnorKRingMap_injective_of_isPurelyInseparable_of_injective_nsmul
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L] {p : ℕ} [ExpChar K p]
    (h : Function.Injective (fun x : MilnorKRing K => p • x)) :
    Function.Injective (milnorKRingMap (algebraMap K L)) := by
  have hpow (r : ℕ) : Function.Injective (fun x : MilnorKRing K => (p ^ r) • x) := by
    induction r with
    | zero =>
      intro x y hxy
      simpa only [pow_zero, one_nsmul] using hxy
    | succ r ih =>
      intro x y hxy
      apply ih
      apply h
      simpa only [pow_succ', mul_nsmul'] using hxy
  obtain ⟨r, hr⟩ := IsPurelyInseparable.finrank_eq_pow K L p
  intro x y hxy
  apply hpow r
  simpa only [milnorKNormRing_milnorKRingMap, hr, natCast_zsmul] using
    congrArg (milnorKNormRing K L) hxy

variable {K M L : Type u} [Field K] [Field M] [Field L]
  [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
  [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]
  [IsPurelyInseparable K L]

/-- The chosen norm and the two-step chosen norm have the same restriction
to the top field in every finite purely inseparable tower. -/
theorem milnorKRingMap_milnorKNormRing_tower_of_isPurelyInseparable
    (x : MilnorKRing L) :
    milnorKRingMap (algebraMap K L) (milnorKNormRing K M (milnorKNormRing M L x)) =
      milnorKRingMap (algebraMap K L) (milnorKNormRing K L x) := by
  let : IsPurelyInseparable K M := IsPurelyInseparable.tower_bot K M L
  let : IsPurelyInseparable M L := IsPurelyInseparable.tower_top K M L
  calc
    _ = milnorKRingMap (algebraMap M L)
          (milnorKRingMap (algebraMap K M) (milnorKNormRing K M (milnorKNormRing M L x))) := by
      rw [IsScalarTower.algebraMap_eq K M L, milnorKRingMap_comp_apply]
    _ = (finrank K M : ℤ) • ((finrank M L : ℤ) • x) := by
      rw [milnorKRingMap_milnorKNormRing_of_isPurelyInseparable, map_zsmul,
        milnorKRingMap_milnorKNormRing_of_isPurelyInseparable]
    _ = (finrank K L : ℤ) • x := by
      rw [smul_smul, ← Nat.cast_mul, finrank_mul_finrank]
    _ = _ := (milnorKRingMap_milnorKNormRing_of_isPurelyInseparable x).symm

/-- The total field degree annihilates the difference between the composed
and direct native chosen norms in a purely inseparable tower. -/
theorem finrank_zsmul_milnorKNormRing_tower_sub_eq_zero_of_isPurelyInseparable
    (x : MilnorKRing L) :
    (finrank K L : ℤ) • (milnorKNormRing K M (milnorKNormRing M L x) -
      milnorKNormRing K L x) = 0 := by
  apply finrank_zsmul_eq_zero_of_milnorKRingMap_eq_zero K L
  rw [map_sub, milnorKRingMap_milnorKNormRing_tower_of_isPurelyInseparable, sub_self]

/-- Purely inseparable transitivity for the original whole-ring norm maps under
injectivity of multiplication by the exponential characteristic. -/
theorem milnorKNormRing_comp_milnorKNormRing_of_isPurelyInseparable_of_injective_nsmul
    {p : ℕ} [ExpChar K p] (h : Function.Injective (fun x : MilnorKRing K => p • x)) :
    (milnorKNormRing K M).comp (milnorKNormRing M L) = milnorKNormRing K L := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKRingMap_injective_of_isPurelyInseparable_of_injective_nsmul h
    (milnorKRingMap_milnorKNormRing_tower_of_isPurelyInseparable x)

/-- Purely inseparable transitivity on each native homogeneous group under
injectivity of multiplication by the exponential characteristic. -/
theorem milnorKNorm_comp_milnorKNorm_of_isPurelyInseparable_of_injective_nsmul
    {p : ℕ} [ExpChar K p] (h : Function.Injective (fun x : MilnorKRing K => p • x))
    (n : ℕ) : (milnorKNorm K M n).comp (milnorKNorm M L n) = milnorKNorm K L n := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun
    (milnorKNormRing_comp_milnorKNormRing_of_isPurelyInseparable_of_injective_nsmul
      (M := M) (L := L) h) (x : MilnorKRing L)

end Stacks.Chow

end
