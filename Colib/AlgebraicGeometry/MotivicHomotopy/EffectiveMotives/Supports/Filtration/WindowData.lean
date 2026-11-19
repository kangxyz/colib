/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.RepresentedCohomology
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Indexing
public import Mathlib.Algebra.Category.Grp.Colimits

/-! # The diagrams of relative coniveau cohomology -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "DM(" field ")" => EffectiveMotivesMinus field

variable (X : SmoothSite (Spec (CommRingCat.of k)))

/-- The relative support diagram takes the cohomology of
`(X \ Z, X \ W)` for each inclusion `Z ⊆ W`. -/
def coniveauRelativeSupportDiagram (K : DM(k)) (n : ℤ) (a b : ℕ) :
    ConiveauSupportPairs k X a b ⥤ AddCommGrpCat.{w'} :=
  opOp (ConiveauSupportPairs k X a b) ⋙ (coniveauSupportPairsInclusion k X a b).op ⋙
    effectivePairCohomology k K n

/-- Cohomology of the coniveau window between two codimension bounds. -/
abbrev coniveauRelativeSupportCohomology [UnivLE.{u, w'}] (K : DM(k)) (n : ℤ) (a b : ℕ) :
    AddCommGrpCat.{w'} := colimit (coniveauRelativeSupportDiagram k X K n a b)

end AlgebraicGeometry.MotivicHomotopy
