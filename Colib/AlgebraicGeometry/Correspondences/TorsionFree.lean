/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Basic

/-!
# Integer cancellation on native finite correspondences

Finite correspondences are the original subgroup of integer-valued native
cycles. Cancellation is pointwise in the integers and uses no choice of a
free presentation, integrality hypothesis, or condition on the base field.
This does not claim that an arbitrary quotient of correspondences is torsion-free.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {S X Y : Scheme.{u}}

/-- Multiplication by a nonzero natural number is injective on actual finite cycles. -/
theorem finiteCorrespondences_nsmul_injective (f : X ⟶ S) (g : Y ⟶ S)
    (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (fun c : finiteCorrespondences f g => n • c) := by
  intro a b h
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  apply nsmul_right_injective hn
  exact congrArg (fun c : finiteCorrespondences f g => c.val z) h

/-- Native finite correspondences have unique division, hence no integer torsion. -/
instance finiteCorrespondences_hasUniqueDiv (f : X ⟶ S) (g : Y ⟶ S) :
    HasUniqueDiv (finiteCorrespondences f g) where
  nsmul_right_injective n hn := finiteCorrespondences_nsmul_injective f g n hn

end Stacks.Chow
