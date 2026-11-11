/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FlatLength

/-!
# Full fundamental-cycle degree of a finite flat morphism

For a finite flat morphism between Noetherian schemes, the pushforward of the
whole fundamental cycle has coefficient `finrank f y` times the fundamental
coefficient at `y`. The local calculation is the flat local-ring length formula.
The full fibre sum is the native Stacks rank formula, with separable and
inseparable degrees multiplied to the entire residue-field degree.

No reducedness, equidimensionality, connectedness or constant-rank hypothesis is
used in the coefficient statement. All components and their actual nilpotent
lengths are retained. This reconstructs the degree input of motivic's
`FiniteScalarFundamentalCycle` without introducing a second cycle model.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}}

/-- The actual stalk length equals the base stalk length times the local fibre length. -/
theorem length_stalk_eq_mul_localFiberLength (f : X ⟶ Y) [Flat f] (x : X) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) =
      Module.length (Y.presheaf.stalk (f x)) (Y.presheaf.stalk (f x)) *
        Module.length (X.presheaf.stalk x)
          ((X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMap x).hom
            (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))) := by
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  letI : Algebra A B := (f.stalkMap x).hom.toAlgebra
  letI : IsLocalHom (algebraMap A B) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  letI : Module.Flat A B := (RingHom.flat_algebraMap_iff).mp (by
    change (f.stalkMap x).hom.Flat
    exact Flat.stalkMap f x)
  have h := IsLocalRing.length_baseChange A B A
  rw [(TensorProduct.AlgebraTensorModule.rid A B B).length_eq] at h
  exact h

/-- The full residue degree and the canonical flat weighting give the same
fundamental coefficient, including inseparable residue extensions. -/
theorem fundamentalCycle_mul_residueDegree_eq
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsFinite f] [Flat f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    AlgebraicCycle.fundamentalCycle X x * (f.residueDegree x : ℤ) =
      AlgebraicCycle.fundamentalCycle Y (f x) * flatQuasiFiniteWeight f x *
        (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ) := by
  classical
  letI := (f.residueFieldMap x).hom.toAlgebra
  by_cases hx : x ∈ genericPoints X
  · have hy := mem_genericPoints_of_flat f hx
    have hl := congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
      (length_stalk_eq_mul_localFiberLength f x)
    simp only [ENat.toNat_mul, Nat.cast_mul] at hl
    have hd : (f.residueDegree x : ℤ) =
        (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ) *
          (Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) : ℤ) := by
      rw [← Nat.cast_mul, Field.finSepDegree_mul_finInsepDegree]
      rfl
    rw [AlgebraicCycle.fundamentalCycle_apply_generic X ⟨x, hx⟩,
      AlgebraicCycle.fundamentalCycle_apply_generic Y ⟨f x, hy⟩, hl, hd,
      flatQuasiFiniteWeight]
    ring
  · have hy : f x ∉ genericPoints Y :=
      fun hy => hx (mem_genericPoints_of_isFinite_image f x hy)
    rw [AlgebraicCycle.fundamentalCycle_apply_of_notMem X x hx,
      AlgebraicCycle.fundamentalCycle_apply_of_notMem Y (f x) hy]
    simp

/-- At every target point, actual finite pushforward multiplies the fundamental
coefficient by the rank of the finite flat map at that point. -/
theorem finiteCyclePushforward_fundamentalCycle_apply
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsFinite f] [Flat f] (y : Y) :
    finiteCyclePushforward f (AlgebraicCycle.fundamentalCycle X) y =
      (f.finrank y : ℤ) * AlgebraicCycle.fundamentalCycle Y y := by
  classical
  rw [finiteCyclePushforward_apply, finsum_mem_def]
  calc
    _ = AlgebraicCycle.fundamentalCycle Y y *
        separableDegreeWeightedFiberSum f (flatQuasiFiniteWeight f) y := by
      rw [separableDegreeWeightedFiberSum, mul_finsum]
      apply finsum_congr
      intro x
      by_cases hx : f x = y
      · have hx' : x ∈ f.base ⁻¹' {y} := hx
        rw [Set.indicator_of_mem hx', if_pos hx,
          fundamentalCycle_mul_residueDegree_eq f x, hx]
        ring
      · have hx' : x ∉ f.base ⁻¹' {y} := hx
        rw [Set.indicator_of_notMem hx', if_neg hx, mul_zero]
    _ = _ := by
      rw [congrFun (separableDegreeWeightedFiberSum_flatQuasiFiniteWeight f) y]
      ring

/-- Constant finite flat rank gives the whole ungraded fundamental-cycle identity. -/
theorem finiteCyclePushforward_fundamentalCycle_of_constant_finrank
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsFinite f] [Flat f]
    (d : ℕ) (hd : ∀ y, f.finrank y = d) :
    finiteCyclePushforward f (AlgebraicCycle.fundamentalCycle X) =
      (d : ℤ) • AlgebraicCycle.fundamentalCycle Y := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [finiteCyclePushforward_fundamentalCycle_apply, hd]
  simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul]

end Stacks.Chow
