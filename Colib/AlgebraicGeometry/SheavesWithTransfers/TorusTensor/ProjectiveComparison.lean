/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryBounded

/-!
# Torus tensor on projective transfer representatives

Compute the presheaf tensor on the actual bounded-above projective
representative and then sheafify. The construction uses the native
projective equivalence and the exact derived sheafification functor.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
variable [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))

/-- Derived torus tensor on presheaf projective representatives, followed by
the actual exact Nisnevich sheafification. -/
def projectiveTorusTensorToDerivedMinus :
    DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤
      DerivedCategory.Minus (SheafWithTransfers.{u + 1} k) :=
  projectiveDerivedMinusFunctor k (parameterTensorFunctor Gₘ) ⋙
    (nisnevichSheafify k).mapDerivedCategoryMinus

end AlgebraicGeometry.SheafWithTransfers
