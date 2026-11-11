/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # The actual range of a Cartesian scheme projection

Extracted from motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Sites/Smooth/Cartier/PunctureComparison.lean (blob dd15cd6c36b803181eff6b1b9d406891fbea1197),
to its generic scheme owner for use below the smooth site.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme

/-- The range of a full Cartesian projection is the preimage of the other range. -/
theorem range_fst_of_isPullback {D A B C : Scheme.{u}}
    {d : D ⟶ A} {e : D ⟶ B} {a : A ⟶ C} {i : B ⟶ C}
    (h : IsPullback d e a i) : Set.range d = a ⁻¹' Set.range i := by
  rw [← h.isoPullback_hom_fst]
  change Set.range ((pullback.fst a i) ∘ h.isoPullback.hom) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.surjective,
    Set.image_univ, Scheme.Pullback.range_fst]

end AlgebraicGeometry.Scheme
