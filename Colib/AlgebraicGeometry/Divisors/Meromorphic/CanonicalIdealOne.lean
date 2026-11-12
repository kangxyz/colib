/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalDifferenceRegular

/-!
# The original ideal's section one on the canonical nonvanishing open

The canonical nonvanishing open avoids the full closed subscheme. Its ideal has
a unique ordinary section with ambient value one, without taking a reduction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (E : X.IdealSheafData) [IsEffectiveCartierDivisor E]

local instance idealOnePositiveInvertible :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (divisorSheaf E) :=
  isTensorInvertible_invertibleSheaf E

/-- The canonical section's nonvanishing open avoids the original support. -/
theorem notMem_support_of_mem_nonvanishingOpen_canonicalSection
    (x : X) (hx : x ∈ canonicalDifferenceRegularOpen E) : x ∉ E.support := by
  have := isTensorInvertible_negativeTwist E
  obtain ⟨W, hxW, b, hb⟩ := (Stacks.SheafOfModules.mem_nonvanishingLocus_iff
    (X := X.toRingedSpace) (L := divisorSheaf E) (N := negativeTwist' E)
    (Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' E))
    (canonicalSection' E) x).mp hx
  have h1 : idealSheafSection E b = (1 : Γ(X, W)) :=
    (Stacks.SheafOfModules.evaluation_tensorPt X.presheaf X.ringCatSheaf.property
      (negativeTwist' E) (op W) ((canonicalSection' E).eval (op W)) b).symm.trans hb
  have hzero : E.subschemeι.app W (1 : Γ(X, W)) = 0 := by
    rw [← h1]
    exact subschemeι_app_idealSheafSection E b
  intro hsupport
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  have h2 := mem_ker_app_res E (show U ≤ W from hUW) hzero
  rw [map_one, E.ker_subschemeι_app ⟨U, hU⟩] at h2
  change x ∈ E.supportSet at hsupport
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := ⟨U, hU⟩) hxU,
    Scheme.mem_zeroLocus_iff] at hsupport
  exact hsupport 1 h2 (by rw [X.basicOpen_one]; exact hxU)

/-- The native canonical nonvanishing open is exactly the complement of the full support. -/
theorem canonicalDifferenceRegularOpen_eq_compl_support :
    canonicalDifferenceRegularOpen E = E.support.compl := by
  ext x
  exact ⟨notMem_support_of_mem_nonvanishingOpen_canonicalSection E x,
    mem_nonvanishingOpen_canonicalSection_of_notMem_support E x⟩

/-- The original closed subscheme has empty inverse image in its canonical nonvanishing open. -/
theorem preimage_canonicalDifferenceRegularOpen_subschemeι :
    E.subschemeι ⁻¹ᵁ canonicalDifferenceRegularOpen E = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  exact (notMem_support_of_mem_nonvanishingOpen_canonicalSection E (E.subschemeι x) hx)
    (by
      change E.subschemeι x ∈ (E.support : Set X)
      rw [← E.range_subschemeι]
      exact ⟨x, rfl⟩)

/-- The whole original ideal, restricted to the canonical nonvanishing open, contains one. -/
theorem exists_idealOneSection :
    ∃ b : Γ(negativeTwist' E, canonicalDifferenceRegularOpen E),
      idealSheafSection E b = (1 : Γ(X, canonicalDifferenceRegularOpen E)) := by
  apply (subschemeι_app_eq_zero_iff_exists_idealSheafSection E 1).mp
  have : Subsingleton Γ(E.subscheme, E.subschemeι ⁻¹ᵁ canonicalDifferenceRegularOpen E) :=
    CommRingCat.subsingleton_of_isTerminal
      (E.subscheme.sheaf.isTerminalOfEqEmpty (preimage_canonicalDifferenceRegularOpen_subschemeι E))
  exact Subsingleton.elim _ _

/-- The unique original ideal section with ambient value one. -/
def idealOneSection : Γ(negativeTwist' E, canonicalDifferenceRegularOpen E) :=
  (exists_idealOneSection E).choose

/-- The chosen section maps to one as a section, retaining all scheme structure. -/
@[simp]
theorem idealSheafSection_idealOneSection :
    idealSheafSection E (idealOneSection E) = (1 : Γ(X, canonicalDifferenceRegularOpen E)) :=
  (exists_idealOneSection E).choose_spec

end Stacks.Divisors
