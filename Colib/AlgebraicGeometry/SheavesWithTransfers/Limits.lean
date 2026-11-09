/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Basic
public import Colib.CategoryTheory.Preadditive.AdditiveFunctorLimits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Grp.Limits

/-!
# Limits and binary biproducts of sheaves with transfers

The additive-functor category inherits limits from abelian groups. Restriction
along the graph functor preserves these limits, and ordinary sheafness is
closed under them. Thus actual Nisnevich sheaves with transfers have binary
biproducts. No abelian-category or exactness assertion is required here.

Implementation adapted from `motivic_source_a6805c4`,
`Motivic/Transfers/Presheaf/Limits.lean`, blob
`0d50501bbf6e99b2b5da963e3b543761e92e4eda`. The definitions and comparisons retain the native
objects, all stated coefficient universes and the existing categorical limit maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u w w'

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

section Shape

variable (J : Type w) [Category.{w'} J] [HasLimitsOfShape J AddCommGrpCat.{v}]

instance : HasLimitsOfShape J (PresheafWithTransfers.{v} k) := by
  let := CategoryTheory.additiveFunctor_isClosedUnderLimitsOfShape
    (C := (Cor k)ᵒᵖ) (D := AddCommGrpCat.{v}) (J := J)
  exact hasLimitsOfShape_of_closedUnderLimits J
    (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{v})

instance : PreservesLimitsOfShape J (PresheafWithTransfers.toPresheaf.{v} k) := by
  dsimp [PresheafWithTransfers.toPresheaf, PresheafWithTransfers.restrictAlong]
  infer_instance

instance : (PresheafWithTransfers.IsNisnevichSheaf.{v} k).IsClosedUnderLimitsOfShape J := by
  change (ObjectProperty.inverseImage
    (Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      (A := AddCommGrpCat.{v}))
    (PresheafWithTransfers.toPresheaf k)).IsClosedUnderLimitsOfShape J
  infer_instance

/-- The actual sheaf-with-transfers subcategory inherits these native limits. -/
instance SheafWithTransfers.hasLimitsOfShape :
    HasLimitsOfShape J (SheafWithTransfers.{v} k) :=
  hasLimitsOfShape_of_closedUnderLimits J (PresheafWithTransfers.IsNisnevichSheaf.{v} k)

end Shape

instance : HasBinaryBiproducts (SheafWithTransfers.{v} k) := by
  let : HasBinaryProducts (SheafWithTransfers.{v} k) :=
    SheafWithTransfers.hasLimitsOfShape k (Discrete WalkingPair)
  exact HasBinaryBiproducts.of_hasBinaryProducts (C := SheafWithTransfers.{v} k)

instance : HasZeroObject (SheafWithTransfers.{v} k) := by
  let : HasTerminal (SheafWithTransfers.{v} k) :=
    SheafWithTransfers.hasLimitsOfShape k (Discrete PEmpty)
  exact hasZeroObject_of_hasTerminal_object

end AlgebraicGeometry
