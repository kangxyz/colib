/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Separable closures in a tower

For an algebraic tower `K ⊆ M ⊆ L`, the maximal separable subfields over `K`
in `M` and `L` embed into one another. The compositum of `M` and the latter
subfield in `L` is the relative separable closure of `M` in `L`.
-/

@[expose] public noncomputable section

namespace separableClosure

open IntermediateField

variable (K M L : Type*) [Field K] [Field M] [Field L]
  [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]

/-- The embedding between the maximal separable subfields over the base of a tower. -/
def towerMap : separableClosure K M →ₐ[K] separableClosure K L :=
  ((IsScalarTower.toAlgHom K M L).comp (separableClosure K M).val).codRestrict
    (separableClosure K L).toSubalgebra fun x ↦
      (map_mem_separableClosure_iff (IsScalarTower.toAlgHom K M L)).2 x.property

@[simp]
theorem coe_towerMap_apply (x : separableClosure K M) :
    (towerMap K M L x : L) = algebraMap M L (x : M) := rfl

/-- The inclusion of the maximal separable subfield over `K` into that over `M`. -/
def towerInclusion : separableClosure K L →ₐ[K] separableClosure M L :=
  inclusion (le_restrictScalars K M L)

@[simp]
theorem coe_towerInclusion_apply (x : separableClosure K L) :
    (towerInclusion K M L x : L) = (x : L) := rfl

scoped instance instAlgebraTowerMap : Algebra (separableClosure K M) (separableClosure K L) :=
  (towerMap K M L).toRingHom.toAlgebra

scoped instance instAlgebraTowerInclusion : Algebra (separableClosure K L) (separableClosure M L) :=
  (towerInclusion K M L).toRingHom.toAlgebra

scoped instance instIsScalarTowerBaseTowerMap :
    IsScalarTower K (separableClosure K M) (separableClosure K L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext (IsScalarTower.algebraMap_apply K M L x)

scoped instance instIsScalarTowerBaseTowerInclusion :
    IsScalarTower K (separableClosure K L) (separableClosure M L) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

scoped instance instIsScalarTowerTowerMapInclusion :
    IsScalarTower (separableClosure K M) (separableClosure K L) (separableClosure M L) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

scoped instance instIsScalarTowerTowerInclusionAmbient :
    IsScalarTower (separableClosure K L) (separableClosure M L) L :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

scoped instance instIsSeparableTowerMap :
    Algebra.IsSeparable (separableClosure K M) (separableClosure K L) :=
  Algebra.isSeparable_tower_top_of_isSeparable K _ _

scoped instance instIsPurelyInseparableTowerInclusion [Algebra.IsAlgebraic K L] :
    IsPurelyInseparable (separableClosure K L) (separableClosure M L) :=
  IsPurelyInseparable.tower_bot (separableClosure K L) (separableClosure M L) L

scoped instance instFiniteDimensionalTowerMap [FiniteDimensional K L] :
    FiniteDimensional (separableClosure K M) (separableClosure K L) :=
  FiniteDimensional.right K _ _

scoped instance instFiniteDimensionalTowerInclusion [FiniteDimensional K L] :
    FiniteDimensional (separableClosure K L) (separableClosure M L) :=
  FiniteDimensional.left (separableClosure K L) (separableClosure M L) L

/-- In the ambient field, the image of the relative separable closure over `M` is the
compositum of `M` and the maximal separable subfield over `K`. -/
theorem fieldRange_eq_adjoin_range [Algebra.IsAlgebraic K M] :
    (IsScalarTower.toAlgHom (separableClosure K L) (separableClosure M L) L).fieldRange =
      adjoin (separableClosure K L) (Set.range (algebraMap M L)) := by
  apply IntermediateField.toSubfield_injective
  let i := IsScalarTower.toAlgHom (separableClosure K L) (separableClosure M L) L
  change i.fieldRange.toSubfield = _
  have hRange : i.fieldRange.toSubfield = (separableClosure M L).toSubfield :=
    SetLike.coe_injective Subtype.range_coe
  rw [hRange, ← adjoin_eq_of_isAlgebraic (F := K), adjoin_toSubfield, adjoin_toSubfield]
  change Subfield.closure (Set.range (algebraMap M L) ∪ (separableClosure K L : Set L)) =
    Subfield.closure (Set.range (Subtype.val : separableClosure K L → L) ∪
      Set.range (algebraMap M L))
  rw [Subtype.range_coe, Set.union_comm]

/-- The image of `M` generates its relative separable closure over the maximal separable
subfield over `K`. -/
theorem adjoin_range_eq_top [Algebra.IsAlgebraic K M] :
    adjoin (separableClosure K L) (Set.range (algebraMap M (separableClosure M L))) = ⊤ := by
  apply map_injective (IsScalarTower.toAlgHom (separableClosure K L) (separableClosure M L) L)
  rw [adjoin_map, ← Set.range_comp, ← AlgHom.fieldRange_eq_map, fieldRange_eq_adjoin_range]
  rfl

end separableClosure
