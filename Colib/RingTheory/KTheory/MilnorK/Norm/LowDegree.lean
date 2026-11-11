/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeOne
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeZero
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm

/-!
# The native Milnor norm in degrees zero and one

The native degree-zero equivalence identifies the norm with multiplication by the extension
degree. The native degree-one equivalence identifies it with the ordinary field norm on units.
Multiplicativity of extension degrees and transitivity of the ordinary field norm give
transitivity in both degrees for arbitrary finite compatible field towers.

-/

@[expose] public noncomputable section

universe u

namespace Stacks.Chow

private theorem coe_zeroMap_eq_zsmul_one
    (K : Type u) [Field K] (n : ℤ) :
    (milnorKZeroMap K n : MilnorKRing K) =
      n • (1 : MilnorKRing K) := by
  change (milnorKSteinbergIdeal K).ringCon.mk'
    (algebraMap ℤ (MilnorKTensorAlgebra K) n) = _
  rw [Algebra.algebraMap_eq_smul_one, map_zsmul, map_one]

private theorem coe_oneEquiv_symm_eq_symbol
    (K : Type u) [Field K] (a : Additive Kˣ) :
    ((milnorKTheoryOneAddEquiv K).symm a : MilnorKRing K) =
      milnorKSymbol K a.toMul := by
  rw [coe_milnorKTheoryOneAddEquiv_symm, milnorKSymbol_eq_mk']
  rfl

/-- The existing degree-one equivalence reads the chosen native norm as the unit norm. -/
theorem milnorKTheoryOneAddEquiv_milnorKNorm
    (K L : Type u) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (x : MilnorKTheory L 1) :
    (milnorKTheoryOneAddEquiv K (milnorKNorm K L 1 x)).toMul =
      Units.map (Algebra.norm K : L →* K)
        (milnorKTheoryOneAddEquiv L x).toMul := by
  let a : Lˣ := (milnorKTheoryOneAddEquiv L x).toMul
  have hx : (x : MilnorKRing L) = milnorKSymbol L a := by
    simpa only [AddEquiv.symm_apply_apply] using
      coe_oneEquiv_symm_eq_symbol L (milnorKTheoryOneAddEquiv L x)
  have h :
      milnorKNorm K L 1 x =
        (milnorKTheoryOneAddEquiv K).symm
          (Additive.ofMul (Units.map (Algebra.norm K : L →* K) a)) := by
    apply Subtype.ext
    rw [coe_milnorKNorm, hx, milnorKNormRing_milnorKSymbol,
      coe_oneEquiv_symm_eq_symbol]
    rfl
  rw [h, AddEquiv.apply_symm_apply]
  rfl

/-- The existing degree-zero equivalence reads the chosen native norm as degree multiplication. -/
theorem milnorKTheoryZeroAddEquiv_milnorKNorm
    (K L : Type u) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (x : MilnorKTheory L 0) :
    milnorKTheoryZeroAddEquiv K (milnorKNorm K L 0 x) =
      (Module.finrank K L : ℤ) * milnorKTheoryZeroAddEquiv L x := by
  obtain ⟨n, rfl⟩ := milnorKZeroMap_surjective L x
  have h :
      milnorKNorm K L 0 (milnorKZeroMap L n) =
        milnorKZeroMap K ((Module.finrank K L : ℤ) * n) := by
    apply Subtype.ext
    rw [coe_milnorKNorm, coe_zeroMap_eq_zsmul_one,
      map_zsmul, milnorKNormRing_one, coe_zeroMap_eq_zsmul_one, smul_smul]
    rw [mul_comm n]
  rw [h, milnorKTheoryZeroAddEquiv_milnorKZeroMap,
    milnorKTheoryZeroAddEquiv_milnorKZeroMap]

/-- The native degree-zero Milnor norm is transitive in finite field towers. -/
theorem milnorKNorm_tower_zero
    {k M L : Type u} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L]
    (x : MilnorKTheory L 0) :
    milnorKNorm k M 0 (milnorKNorm M L 0 x) = milnorKNorm k L 0 x := by
  apply (milnorKTheoryZeroAddEquiv k).injective
  simp only [milnorKTheoryZeroAddEquiv_milnorKNorm]
  rw [← mul_assoc, ← Nat.cast_mul, Module.finrank_mul_finrank k M L]

/-- The native degree-one Milnor norm is transitive in finite field towers. -/
theorem milnorKNorm_tower_one
    {k M L : Type u} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L]
    (x : MilnorKTheory L 1) :
    milnorKNorm k M 1 (milnorKNorm M L 1 x) = milnorKNorm k L 1 x := by
  apply (milnorKTheoryOneAddEquiv k).injective
  apply Additive.toMul.injective
  simp only [milnorKTheoryOneAddEquiv_milnorKNorm]
  apply Units.ext
  exact Algebra.norm_norm (R := k) (S := M)

end Stacks.Chow
