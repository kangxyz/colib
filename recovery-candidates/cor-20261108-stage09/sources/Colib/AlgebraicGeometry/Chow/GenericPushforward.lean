/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FinitePushforward
public import Colib.AlgebraicGeometry.Chow.GenericCoefficientCycle

/-!
# Finite weighted pushforward of actual generic coefficients

The finite set of actual generic points gives a literal finite sum in Mathlib's
native cycle group. Finite pushforward transports that sum using the actual
residue-field degree of every contributing component. Different generic points
may have the same image. This gives the weighted formula needed by the incidence
Tor cycle without assuming any injectivity, reducedness, or positivity.

The generic-set finiteness is the natural input at this lower level. The actual
incidence application derives it from its component geometry. No Tor coefficient
or associativity claim is made by this module.

References: Stacks Project, Tags 02QR (finite ungraded formal sums), 02R4 (finite
pushforward formula), and 02R5 (finite pushforward functoriality). Implementation
context: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Correspondences/Composition/Incidence/TorCycle.lean`; the native cycle model,
not that source's separate representation, is used here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Function.locallyFinsuppWithin
open scoped BigOperators

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable {X Y Z : Scheme.{u}}

/-- Finite pushforward of actual generic coefficients is the complete finite
residue-degree weighted sum, retaining negative coefficients and collisions. -/
theorem finiteCyclePushforward_ofGenericCoefficients (f : X ⟶ Y) [IsFinite f]
    (hfin : (genericPoints X).Finite) (c : genericPoints X → ℤ) :
    finiteCyclePushforward f (AlgebraicCycle.ofGenericCoefficients hfin c) =
      letI := hfin.fintype
      ∑ x : genericPoints X, single (f.base x.val) (c x * (f.residueDegree x.val : ℤ)) := by
  classical
  let := hfin.fintype
  rw [AlgebraicCycle.ofGenericCoefficients_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact finiteCyclePushforward_single f x.val (c x)

/-- At a target point the contributions from every generic point with that image
are added, using their individual residue degrees. -/
theorem finiteCyclePushforward_ofGenericCoefficients_apply (f : X ⟶ Y) [IsFinite f]
    (hfin : (genericPoints X).Finite) (c : genericPoints X → ℤ) (y : Y) :
    finiteCyclePushforward f (AlgebraicCycle.ofGenericCoefficients hfin c) y =
      letI := hfin.fintype
      ∑ x : genericPoints X,
        if y = f.base x.val then c x * (f.residueDegree x.val : ℤ) else 0 := by
  classical
  let := hfin.fintype
  rw [finiteCyclePushforward_ofGenericCoefficients]
  simp only [coe_sum, Finset.sum_apply, single_apply]

/-- Weighted pushforward of a generic cycle is supported on the actual images
of generic points and still has finite support. -/
theorem finiteCyclePushforward_ofGenericCoefficients_finite_support (f : X ⟶ Y)
    [IsFinite f] (hfin : (genericPoints X).Finite) (c : genericPoints X → ℤ) :
    (finiteCyclePushforward f (AlgebraicCycle.ofGenericCoefficients hfin c)).support.Finite :=
  finiteCyclePushforward_finite_support f _
    (AlgebraicCycle.finite_support_ofGenericCoefficients hfin c)

/-- Two successive finite pushforwards give the single actual composite-weight
formula on the original generic points, including all colliding intermediate images. -/
theorem finiteCyclePushforward_comp_ofGenericCoefficients
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [IsFinite g]
    (hfin : (genericPoints X).Finite) (c : genericPoints X → ℤ) :
    finiteCyclePushforward g
      (finiteCyclePushforward f (AlgebraicCycle.ofGenericCoefficients hfin c)) =
      letI := hfin.fintype
      ∑ x : genericPoints X,
        single ((f ≫ g).base x.val) (c x * ((f ≫ g).residueDegree x.val : ℤ)) := by
  rw [finiteCyclePushforward_comp_apply, finiteCyclePushforward_ofGenericCoefficients]

end Stacks.Chow
