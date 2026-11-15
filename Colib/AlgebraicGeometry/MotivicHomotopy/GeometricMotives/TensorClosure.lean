/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.Effective
public import Mathlib.CategoryTheory.Monoidal.Subcategory
import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# Restricting an effective tensor to geometric motives

The restriction uses the native full subcategory. Its unit and product
closure are tested on the original smooth motives, and extended by
exactness in each variable.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "E(" k ")" => EffectiveMotivesMinus k
local notation "P(" k ")" => isEffectiveGeometric k
local notation "M(" k ")" => effectiveMotive k

variable [MonoidalCategory E(k)]
  [BraidedCategory E(k)]
  [∀ A : E(k), (tensorLeft A).CommShift ℤ]
  [∀ A : E(k), (tensorLeft A).IsTriangulated]

/-- A braided tensor with exact left tensor functors restricts to the geometric
subcategory when its unit and products of smooth motives are geometric. -/
theorem isEffectiveGeometric_monoidal_of_generators
    (hUnit : (P(k)) (𝟙_ E(k)))
    (hProd : ∀ X Y : Cor k, (P(k)) ((M(k)).obj X ⊗ (M(k)).obj Y)) :
    (P(k)).IsMonoidal where
  prop_unit := hUnit
  prop_tensor A B hA hB := by
    let Q (C : E(k)) := (P(k)).inverseImage (tensorLeft C)
    have hC (C : E(k)) (h : ∀ X : Cor k, (P(k)) (C ⊗ (M(k)).obj X)) :
        ∀ D : E(k), (P(k)) D → (P(k)) (C ⊗ D) := by
      let : (Q C).IsTriangulated :=
        inferInstanceAs (((P(k)).inverseImage (tensorLeft C)).IsTriangulated)
      let : (Q C).IsStableUnderRetracts :=
        ObjectProperty.isStableUnderRetracts_inverseImage _ _
      exact (isEffectiveGeometric_le_iff k (Q C)).2 h
    apply hC A _ B hB
    intro X
    exact (P(k)).prop_of_iso (BraidedCategory.braiding ((M(k)).obj X) A)
      (hC ((M(k)).obj X) (hProd X) A hA)

/-- The product and unit comparisons on original smooth motives supply the
closure needed for Mathlib's full monoidal subcategory. -/
theorem isEffectiveGeometric_monoidal_of_smoothProduct
    (eUnit : (M(k)).obj (Cor.mk (SmoothSite.base (Spec (.of k)))) ≅ 𝟙_ E(k))
    (eProd : ∀ X Y : Cor k, (M(k)).obj (Cor.mk
      (SmoothSite.product X.toSmoothSite Y.toSmoothSite)) ≅ (M(k)).obj X ⊗ (M(k)).obj Y) :
    (P(k)).IsMonoidal :=
  isEffectiveGeometric_monoidal_of_generators k
    ((P(k)).prop_of_iso eUnit (isEffectiveGeometric_effectiveMotive k _))
    (fun X Y => (P(k)).prop_of_iso (eProd X Y) (isEffectiveGeometric_effectiveMotive k _))

end AlgebraicGeometry.MotivicHomotopy
