/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.NisnevichReflection
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Triangulated
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # Exactness of effective Nisnevich reflection -/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Use the abelian structure on Nisnevich sheaves with transfers for the derived adjunction. -/
local instance : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

instance : (effectiveReflection k).CommShift ℤ :=
  (effectiveReflectionAdjunction k).leftAdjointCommShift ℤ

instance : (effectiveReflectionAdjunction k).CommShift ℤ :=
  (effectiveReflectionAdjunction k).commShift_of_rightAdjoint ℤ

instance : (effectiveReflection k).IsTriangulated := by
  let G : DerivedCategory.Minus (LargeSheaves k) ⥤ EffectiveMotivesMinus k := effectiveReflection k
  let F : EffectiveMotivesMinus k ⥤ DerivedCategory.Minus (LargeSheaves k) :=
    effectiveMotivesMinusInclusion k
  let h : G ⊣ F := effectiveReflectionAdjunction k
  let : F.IsTriangulated := inferInstanceAs
    (((effectiveCohomologyCondition k).ι).IsTriangulated)
  exact h.isTriangulated_leftAdjoint

end AlgebraicGeometry.MotivicHomotopy
