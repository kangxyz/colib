/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward

/-!
# Weighted endpoint cycles of a whole closed support

An endpoint of a fundamental cycle is the sum of the unreduced endpoints
of the original integral components. Each summand has the original
generic stalk length and follows the actual component map to the ambient
scheme.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace
open scoped BigOperators

universe u

namespace AlgebraicGeometry.AlgebraicCycle

open _root_.AlgebraicGeometry.Scheme Scheme.AffineLineFiber Stacks.Chow

variable {k : Type u} [Field k] {D E : Scheme.{u}} [IsNoetherian D]

/-- After inclusion into the original support and a finite pushforward,
the full weighted endpoint is the sum of actual component endpoint cycles
with their full generic weights. -/
theorem finiteCyclePushforward_polynomialEndpointMap_fundamentalCycle_eq_sum
    (f : D ⟶ Spec (.of (Polynomial k))) (a : k) (m : D ⟶ E) [IsFinite m] :
    letI := (fundamentalCycle_genericPoints_finite D).fintype
    finiteCyclePushforward m (finiteCyclePushforward (inclusion f a)
      (polynomialEndpointMap f a (fundamentalCycle D))) =
      ∑ z : genericPoints D,
        let j := (integralComponentAt z.val).subschemeι
        letI : IsNoetherian (fiber (j ≫ f) a) :=
          isNoetherian_of_finiteType_of_isNoetherian (inclusion (j ≫ f) a ≫ j)
        ((Module.length (D.presheaf.stalk z.val) (D.presheaf.stalk z.val)).toNat : ℤ) •
          finiteCyclePushforward ((inclusion (j ≫ f) a ≫ j) ≫ m)
            (fundamentalCycle (fiber (j ≫ f) a)) := by
  classical
  let : Fintype (genericPoints D) := (fundamentalCycle_genericPoints_finite D).fintype
  let i := inclusion f a
  rw [fundamentalCycle, ofGenericCoefficients_eq_sum]
  simp only [map_sum, polynomialEndpointMap_single, map_zsmul]
  apply Finset.sum_congr rfl
  intro z _
  let j := (integralComponentAt z.val).subschemeι
  let q := AffineLineFiber.fiberMap f a j
  let : IsNoetherian (fiber (j ≫ f) a) :=
    isNoetherian_of_finiteType_of_isNoetherian (inclusion (j ≫ f) a ≫ j)
  let c := fundamentalCycle (fiber (j ≫ f) a)
  let w : ℤ := (Module.length (D.presheaf.stalk z.val) (D.presheaf.stalk z.val)).toNat
  change w • finiteCyclePushforward m (finiteCyclePushforward i (finiteCyclePushforward q c)) =
    w • finiteCyclePushforward ((inclusion (j ≫ f) a ≫ j) ≫ m) c
  rw [finiteCyclePushforward_comp_apply q i c, finiteCyclePushforward_comp_apply (q ≫ i) m c]
  exact congrArg (w • ·) (DFunLike.congr_fun (finiteCyclePushforward_congr _ _
    (congrArg (· ≫ m) (fiberMap_inclusion f a j))) c)

end AlgebraicGeometry.AlgebraicCycle
