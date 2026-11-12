/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowEtaleOfIsUnit

/-!
# Prime-to-characteristic divisibility of separably closed points

The native étaleness theorem for multiplication on an abelian variety discharges the
étaleness criterion in the native separably closed point-lifting theorem. Composition with
multiplication is the power operation on the actual group of rational points.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

/-- Rational points of an abelian variety over a separably closed field are divisible by
every natural number invertible in that field. -/
theorem exists_nsmul_eq_of_isUnit_of_isSepClosed
    {k : Type u} [Field k] [IsSepClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]
    (n : ℕ) (hn : IsUnit (n : k))
    (a : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ∃ b : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A), n • b = a := by
  obtain ⟨g, hg, hgn⟩ := exists_comp_zpow_id_left_eq_of_isSepClosed A
    (etaleZPowIdOfIsUnit A) (n : ℤ) (by simpa using hn)
    (Additive.toMul a).left (Over.w (Additive.toMul a))
  let b : 𝟙_ (Over (Spec (.of k))) ⟶ A := Over.homMk g hg
  have hb : b ^ (n : ℤ) = Additive.toMul a := by
    have hpow : b ^ (n : ℤ) = b ≫ (𝟙 A : A ⟶ A) ^ (n : ℤ) := by
      rw [GrpObj.comp_zpow, Category.comp_id]
    rw [hpow]
    exact Over.OverMorphism.ext hgn
  have hbn : b ^ n = Additive.toMul a := by simpa only [zpow_natCast] using hb
  exact ⟨Additive.ofMul b, by rw [← ofMul_pow, hbn, ofMul_toMul]⟩

end Stacks.Groupoids
