/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FinitePushforward
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite cycle sums on a retained open subscheme -/

@[expose] public noncomputable section

open CategoryTheory Stacks.Chow
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {C V T : Scheme.{u}} [IsNoetherian C] [IsNoetherian V]
  (j : V ⟶ C) [IsOpenImmersion j] (m : V ⟶ T) [IsClosedImmersion m]
  (c : AlgebraicCycle C ℤ) (d : AlgebraicCycle V ℤ)
  (h : ∀ y : V, d y = c (j y))

include h in
/-- The finite pushforward of the restricted cycle is the original supported
sum with its actual retained points. -/
theorem finiteCyclePushforward_eq_sum_of_retained_points
    (l : (Function.locallyFinsupp.finite_support c).toFinset → V)
    (hl : ∀ z, j (l z) = z.val) :
    finiteCyclePushforward m d =
      ∑ z : (Function.locallyFinsupp.finite_support c).toFinset, single (m (l z)) (c z.val) := by
  let s := Function.locallyFinsupp.finite_support c
  let t := Function.locallyFinsupp.finite_support d
  have hc (z : s.toFinset) : d (l z) = c z.val := (h (l z)).trans (congrArg c (hl z))
  let mapSupport (z : s.toFinset) : t.toFinset :=
    ⟨l z, t.mem_toFinset.mpr (by
      change d (l z) ≠ 0
      rw [hc z]
      exact s.mem_toFinset.mp z.property)⟩
  have hinj : Function.Injective mapSupport := by
    intro x y hxy
    apply Subtype.ext
    exact (hl x).symm.trans ((congrArg (fun z : t.toFinset => j z.val) hxy).trans (hl y))
  have hsurj : Function.Surjective mapSupport := by
    intro y
    have hy : c (j y.val) ≠ 0 := by
      rw [← h y.val]
      exact t.mem_toFinset.mp y.property
    let z : s.toFinset := ⟨j y.val, s.mem_toFinset.mpr hy⟩
    exact ⟨z, Subtype.ext (j.isOpenEmbedding.injective (hl z))⟩
  let e := Equiv.ofBijective mapSupport ⟨hinj, hsurj⟩
  have hd : (∑ y : t.toFinset, single y.val (d y.val)) = d :=
    (Finset.sum_coe_sort (s := t.toFinset) (f := fun y => single y (d y))).trans
      (sum_apply_smul_single_eq_self_on_univ t)
  rw [← hd, map_sum]
  simp only [finiteCyclePushforward_single_of_isClosedImmersion]
  symm
  refine Fintype.sum_equiv e _ _ ?_
  intro z
  change single (m (l z)) (c z.val) = single (m (l z)) (d (l z))
  rw [hc]

end AlgebraicGeometry.AlgebraicCycle
