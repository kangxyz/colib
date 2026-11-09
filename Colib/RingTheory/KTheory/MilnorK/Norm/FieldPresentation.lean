/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Actual polynomial presentations of finite separable field extensions

The primitive element theorem supplies an actual algebra equivalence with the
native minimal-polynomial quotient. No norm property is used or claimed.
-/

@[expose] public noncomputable section

open Polynomial IntermediateField

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

/-- Every finite separable extension has an actual native polynomial presentation. -/
theorem exists_monicIrreducible_presentation (k L : Type u) [Field k] [Field L]
    [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L] :
    ∃ (d : ℕ) (p : MonicIrreducibleOfDegree k d),
      Nonempty (L ≃ₐ[k] AdjoinRoot (poly p)) := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element k L
  let hi : IsIntegral k a := Algebra.IsIntegral.isIntegral (R := k) a
  let g : k⟮a⟯ ≃ₐ[k] L := (IntermediateField.equivOfEq ha).trans IntermediateField.topEquiv
  exact ⟨(minpoly k a).natDegree, minpolyOfDegree k hi,
    ⟨g.symm.trans (adjoinSimpleEquivQuot k hi)⟩⟩

end Stacks.Chow

end
