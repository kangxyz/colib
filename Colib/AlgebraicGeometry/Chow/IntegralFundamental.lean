/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental

/-!
# The whole native fundamental cycle of an integral scheme

The actual generic stalk is a field, so its length is one. These comparisons
consume the full length-valued fundamental cycle and do not normalize a
nonreduced scheme. They are used to recover native prime correspondence cycles.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Function.locallyFinsuppWithin

universe u

attribute [local instance] Classical.propDecidable

namespace AlgebraicGeometry.AlgebraicCycle

/-- For an integral Noetherian scheme the literal whole cycle is its prime cycle. -/
theorem fundamentalCycle_eq_single_genericPoint (X : Scheme.{u})
    [IsNoetherian X] [IsIntegral X] :
    fundamentalCycle X = single (genericPoint X) (1 : ℤ) := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : x = genericPoint X
  · subst x
    rw [fundamentalCycle_apply_generic_of_isReduced X
      ⟨genericPoint X, Stacks.Chow.genericPoint_mem_genericPoints X⟩]
    simp
  · have hng : x ∉ genericPoints X := by
      simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
    rw [fundamentalCycle_apply_of_notMem X x hng]
    simp [single_apply, hx]

end AlgebraicGeometry.AlgebraicCycle

namespace Stacks.Chow

/-- A closed integral support pushes its full cycle to the corresponding native prime. -/
theorem finiteCyclePushforward_fundamentalCycle_integral
    {X Y : Scheme.{u}} [IsNoetherian X] [IsIntegral X]
    (i : X ⟶ Y) [IsClosedImmersion i] :
    finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle X) =
      single (i (genericPoint X)) (1 : ℤ) := by
  rw [AlgebraicCycle.fundamentalCycle_eq_single_genericPoint,
    finiteCyclePushforward_single, residueDegree_eq_one_of_isPreimmersion]
  simp

end Stacks.Chow
