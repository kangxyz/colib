/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalDifferenceNumerator
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections.TensorRestriction

/-!
# The original canonical Cartier section is invertible off the whole divisor

Every morphism avoiding the support of the divisor lands in the actual
nonvanishing open of its canonical section. No reduction of its source or of the
divisor is taken. This supplies the neighbourhood on which tensor division is regular.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

local instance canonicalPositiveTensorInvertible :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (divisorSheaf D) :=
  isTensorInvertible_invertibleSheaf D

/-- Away from the support, the original canonical section lies in its native
nonvanishing open. The local dual section is the section of the ideal with value one. -/
theorem mem_nonvanishingOpen_canonicalSection_of_notMem_support
    (x : X) (hx : x ∉ D.support) :
    x ∈ Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace)
      (divisorSheaf D) (canonicalSection' D) := by
  have := isTensorInvertible_negativeTwist D
  obtain ⟨U, hxU, hU⟩ := exists_affineOpens_ideal_eq_top D hx
  obtain ⟨b, hb⟩ := (mem_ideal_iff_exists_idealSheafSection D U 1).mp (by simp [hU])
  apply (Stacks.SheafOfModules.mem_nonvanishingLocus_iff
    (X := X.toRingedSpace) (L := divisorSheaf D) (N := negativeTwist' D)
    (Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' D))
    (canonicalSection' D) x).mpr
  refine ⟨U.1, hxU, b, ?_⟩
  exact (Stacks.SheafOfModules.evaluation_tensorPt X.presheaf X.ringCatSheaf.property
    (negativeTwist' D) (op U.1) ((canonicalSection' D).eval (op U.1)) b).trans hb

/-- The entire source of a support-avoiding morphism maps into the same native
nonvanishing open. The source can be nonreduced. -/
theorem range_subset_nonvanishingOpen_canonicalSection {Y : Scheme.{u}} (i : Y ⟶ X)
    (h : ∀ y : Y, i y ∉ D.support) :
    Set.range i ⊆ Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace)
      (divisorSheaf D) (canonicalSection' D) := by
  rintro _ ⟨y, rfl⟩
  exact mem_nonvanishingOpen_canonicalSection_of_notMem_support D (i y) (h y)

/-- An integral scheme's generic point belongs to the same nonvanishing open. -/
theorem genericPoint_mem_nonvanishingOpen_canonicalSection [IsIntegral X] :
    genericPoint X ∈ Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace)
      (divisorSheaf D) (canonicalSection' D) := by
  apply mem_nonvanishingOpen_canonicalSection_of_notMem_support D
  obtain ⟨g, hg, hgnz⟩ :=
    exists_stalk_eq_span_of_isEffectiveCartierDivisor
      (inferInstance : IsEffectiveCartierDivisor D) (genericPoint X)
  have htop : IdealSheafData.stalk D (genericPoint X) = ⊤ := by
    rw [hg]
    exact Ideal.span_singleton_eq_top.mpr
      (isUnit_iff_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hgnz))
  exact (IdealSheafData.stalk_eq_top_iff_notMem_support D (genericPoint X)).mp htop

end Stacks.Divisors
