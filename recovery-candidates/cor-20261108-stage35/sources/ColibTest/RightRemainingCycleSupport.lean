/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingCycleSupport

/-! Literal endpoint consumers. Source-only; no compilation or kernel check performed. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {K : Type u} [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    [Smooth f] [Smooth g] [Smooth h] [Smooth i]
    [IsSeparated g] [IsSeparated h] [IsSeparated i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (hx : x ∉ genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    correspondenceRightWeightedRemainingCycle f g h i z w v hw hv x = 0 := by
  exact correspondenceRightWeightedRemainingCycle_eq_zero_of_not_generic
    f g h i z w v hz hw hv x hx

end Stacks.Chow
