/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm

/-!
# The literal selected step of the native chosen Milnor norm

These supporting statements expose the existing recursion with exactly its
chosen witness. They do not replace that witness by an arbitrary element or
assert independence of the chosen tower.
-/

@[expose] public noncomputable section

open Module IntermediateField

universe u

namespace Stacks.Chow

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

/-- The first step of the native recursion uses exactly `h.choose`. -/
theorem milnorKNormRing_eq_selected_step
    (h : ∃ a : L, a ∉ Set.range (algebraMap K L)) :
    milnorKNormRing K L =
      (milnorKNormAdjoinSimple K
        (Algebra.IsIntegral.isIntegral (R := K) h.choose)).comp
          (milnorKNormRing K⟮h.choose⟯ L) := by
  classical
  rw [milnorKNormRing, milnorKNormAux, dite_eq_left h]
  rfl

/-- The literal selected recursion evaluated on the native whole Milnor ring. -/
theorem milnorKNormRing_selected_step_apply
    (h : ∃ a : L, a ∉ Set.range (algebraMap K L)) (x : MilnorKRing L) :
    milnorKNormRing K L x =
      milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) h.choose)
        (milnorKNormRing K⟮h.choose⟯ L x) := by
  exact congrArg (fun N : MilnorKRing L →+ MilnorKRing K => N x)
    (milnorKNormRing_eq_selected_step h)

end Stacks.Chow

end
