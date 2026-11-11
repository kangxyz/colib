/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatProduct
public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# Full fundamental cycles under a finite disjoint clopen cover

All maps are actual open and closed immersions. Their stalk maps are the
actual isomorphisms, so every generic local length is unchanged, including
nilpotents. The covering condition is a partition of the actual point sets;
no cycle identity is supplied. This helper is used to assemble the actual
graph source components without making the source integral.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

universe u v

namespace Stacks.Chow

variable {D X : Scheme.{u}} [IsNoetherian D] [IsNoetherian X]

/-- An actual clopen immersion preserves the whole fundamental coefficient. -/
theorem fundamentalCycle_apply_clopen (i : D ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion i] (d : D) :
    AlgebraicCycle.fundamentalCycle D d = AlgebraicCycle.fundamentalCycle X (i d) := by
  by_cases hd : d ∈ genericPoints D
  · have hx := mem_genericPoints_of_flat i hd
    rw [AlgebraicCycle.fundamentalCycle_apply_generic D ⟨d, hd⟩,
      AlgebraicCycle.fundamentalCycle_apply_generic X ⟨i d, hx⟩]
    have hlen := Module.length_eq_of_ringEquiv
      (asIso (i.stalkMap d)).commRingCatIsoToRingEquiv
    rw [hlen]
  · have hx : i d ∉ genericPoints X := fun hx =>
      hd (mem_genericPoints_of_isFinite_image i d hx)
    rw [AlgebraicCycle.fundamentalCycle_apply_of_notMem D d hd,
      AlgebraicCycle.fundamentalCycle_apply_of_notMem X (i d) hx]

/-- Extension by zero along the actual clopen immersion, in the native cycle group. -/
theorem finiteCyclePushforward_fundamentalCycle_clopen_apply (i : D ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion i] (x : X) :
    finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle D) x =
      if x ∈ Set.range i then AlgebraicCycle.fundamentalCycle X x else 0 := by
  classical
  by_cases hx : x ∈ Set.range i
  · obtain ⟨d, rfl⟩ := hx
    rw [if_pos (Set.mem_range_self d), finiteCyclePushforward_apply_of_isClosedImmersion,
      fundamentalCycle_apply_clopen]
  · rw [if_neg hx,
      finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_range i x hx]

/-- A finite actual disjoint clopen cover adds to the full fundamental cycle. -/
theorem fundamentalCycle_eq_sum_clopen {ι : Type v} [Fintype ι]
    (D : ι → Scheme.{u}) [∀ s, IsNoetherian (D s)]
    (i : ∀ s, D s ⟶ X) [∀ s, IsClosedImmersion (i s)] [∀ s, IsOpenImmersion (i s)]
    (hcover : ∀ x : X, ∃! s : ι, x ∈ Set.range (i s)) :
    AlgebraicCycle.fundamentalCycle X =
      ∑ s : ι, finiteCyclePushforward (i s) (AlgebraicCycle.fundamentalCycle (D s)) := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro x
  change AlgebraicCycle.fundamentalCycle X x =
    ∑ s : ι, finiteCyclePushforward (i s) (AlgebraicCycle.fundamentalCycle (D s)) x
  obtain ⟨s, hs, huniq⟩ := hcover x
  rw [Finset.sum_eq_single s]
  · rw [finiteCyclePushforward_fundamentalCycle_clopen_apply, if_pos hs]
  · intro t ht hts
    rw [finiteCyclePushforward_fundamentalCycle_clopen_apply,
      if_neg (fun hx => hts (huniq t hx))]
  · intro hsnot
    exact (hsnot (Finset.mem_univ s)).elim

end Stacks.Chow
