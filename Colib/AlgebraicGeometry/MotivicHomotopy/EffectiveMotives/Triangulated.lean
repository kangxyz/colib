/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Basic
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.A1InvariantWeakSerre
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory

/-!
# The triangulated category of bounded-above effective motives

The original transfer cohomology condition is the inverse image of
the derived weak Serre condition along the bounded-above inclusion.
It therefore inherits the shift and distinguished triangles of the
native derived category.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

private theorem effectiveCondition_isTriangulated :
    (effectiveCohomologyCondition k).IsTriangulated := by
  let A := SheafWithTransfers.{u + 1} k
  let P := a1InvariantSheafProperty k
  let Q := DerivedCategoryB.derivedCategoryB P
  let F : DerivedCategory.Minus A ⥤ DerivedCategory A := DerivedCategory.Minus.ι
  let : P.IsWeakSerreClass := a1InvariantSheafProperty_isWeakSerreClass k
  have h : WeakSerre.IsWeakSerre P :=
    ⟨inferInstance, P.exists_prop_of_isWeakSerreClass, fun E h₀ h₁ h₃ h₄ =>
      ObjectProperty.prop_mid_of_exact₄ P.prop_obj₂_of_exact
        E.zero₀ E.zero₁ E.zero₂ E.exact₁ E.exact₂ E.exact₃ h₀ h₁ h₃ h₄⟩
  let : Q.IsClosedUnderIsomorphisms :=
    DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms P h
  let : Q.IsTriangulated := DerivedCategoryB.derivedCategoryB_isTriangulated P h
  change (Q.inverseImage F).IsTriangulated
  let : (Q.inverseImage F).IsTriangulatedClosed₂ :=
    .mk' (fun T hT h₁ h₃ =>
      Q.ext_of_isTriangulatedClosed₂ (F.mapTriangle.obj T) (F.map_distinguished T hT) h₁ h₃)
  exact ⟨⟩

instance : (effectiveCohomologyCondition k).IsTriangulated :=
  effectiveCondition_isTriangulated k

instance : (effectiveMotivesMinusToDerived k).CommShift ℤ :=
  inferInstanceAs (((effectiveCohomologyCondition k).ι ⋙ DerivedCategory.Minus.ι).CommShift ℤ)

instance : (effectiveMotivesMinusToDerived k).IsTriangulated := by
  change ((effectiveCohomologyCondition k).ι ⋙ DerivedCategory.Minus.ι).IsTriangulated
  infer_instance

end AlgebraicGeometry.MotivicHomotopy
