/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionBaseChange
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FieldChange
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FieldExtensionFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.FiniteLocallyFreeFibreDegree

/-!
# Corestriction after finite field restriction

The actual point ambient projection is finite locally free of rank the
field degree. Its push-pull law counts every residue branch with its full
stalk length, including in inseparable extensions.

Adapted from `Motivic/Cohomology/Diagonal/CorestrictionDegree.lean:29-63` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCorestriction

open _root_.AlgebraicGeometry.Scheme
open PresheafWithTransfers
open DiagonalTopDegree DiagonalCorestrictionBaseChange
open DiagonalFieldChange

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

/-- Restriction followed by transfer on native signed point cycles is field degree. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/CorestrictionDegree.lean:31-53"
  "adaptation" "Degree law on the actual signed point cycles, with all local lengths"]
theorem pointPushforward_pointCycleFieldChange (q : ℕ)
    (α : point k ⟶ DiagonalCycleSymbols.target k q) :
    pointPushforward (k := k) (E := E) q
      (pointCycleFieldChange (k := k) (L := E) q α) =
        (Module.finrank k E : ℤ) • α := by
  let B := fieldExtensionBaseChangeSituation k E
  let C := fieldChowSituation k
  let s := pointAmbientStructure k q
  let d := Module.finrank k E
  let sq := pointAmbientMap_isPullback (k := k) (L := E) q
  let π := pullback.fst s B.g
  let z := pointCycleGrade k q α
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank π d :=
    isFiniteLocallyFreeOfRank_pullbackFst_fieldExtension k E s
  let : IsFinite B.g :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let : IsFinite π :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback s B.g).flip
      (inferInstance : IsFinite B.g)
  let : Flat π := Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank π d
  have hrd : AlgebraicGeometry.RelativeDimension π 0 :=
    Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank π d
  have hpush := properPushforward_flatPullback_of_isFiniteLocallyFreeOfRank C
    (π ≫ s) s π d rfl 0 rfl z
  have hval : (properPushforward C (π ≫ s) s π rfl 0
      (flatPullback C (π ≫ s) s π rfl 0 hrd 0 z)).val = (d : ℤ) • z.val :=
    congrArg (fun β : CycleGroup C s 0 => β.val) hpush
  rw [properPushforward_val_eq_finiteCyclePushforward] at hval
  apply Subtype.ext
  rw [pointPushforward_val, pointCycleFieldChange_val,
    val_baseChangeCyclePullbackOfIsPullback, finiteCyclePushforward_comp_apply]
  change finiteCyclePushforward (sq.isoPullback.inv ≫ pointAmbientMap (k := k) (E := E) q)
    (baseChangeCyclePullback B s 0 z).val = _
  have h (f g : (pullback s B.g : Scheme.{u}) ⟶ pointAmbient k q)
      [IsFinite f] [IsFinite g] (he : f = g) :
      finiteCyclePushforward f (baseChangeCyclePullback B s 0 z).val =
        finiteCyclePushforward g (baseChangeCyclePullback B s 0 z).val := by
    cases he
    rfl
  rw [h _ _ sq.isoPullback_inv_fst,
    val_baseChangeCyclePullback_eq_val_flatPullback k E s hrd 0 z]
  exact hval

/-- Transfer after restriction is multiplication by degree on every original diagonal class. -/
theorem corestriction_fieldChange (q : ℕ) (x : (motivicRawBaseComplex k q).homology q) :
    corestriction (k := k) (E := E) q (fieldChange (algebraMap k E) q x) =
      (Module.finrank k E : ℤ) • x := by
  obtain ⟨α, rfl⟩ := cycleClass_surjective k q x
  rw [fieldChange_cycleClass, corestriction_cycleClass,
    pointPushforward_pointCycleFieldChange, map_zsmul]

end AlgebraicGeometry.MotivicCohomology.DiagonalCorestriction
