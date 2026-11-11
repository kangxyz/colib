/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.LocalCoefficients.IntegralChainEvaluation
public import Colib.Topology.LocalCoefficients.PointRelativeHomology
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Evaluating the original point-relative chain equation

An integral chain evaluation that kills the basepoint generator takes equal
values on chains with equal images in the original point-relative quotient.
The proof uses the genuine degreewise short exact sequence and does not
construct or assume a straightening chain homotopy.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]
variable {G : Type u} [AddCommGroup G]

/-- Equality in the original point-relative quotient can be evaluated by any
integral simplex value function which vanishes on the basepoint constant. -/
theorem integralChainEvaluation_eq_of_pointRelative_eq (z : X) (n : ℕ)
    (v : SingularSimplex X ⦋n⦌ → G) (hv : v (ContinuousMap.const _ z) = 0)
    (a b : chainModule (constant X integralCoefficients.{u}) ⦋n⦌)
    (hab : (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
      (constant X integralCoefficients.{u}))).f n a =
      (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
        (constant X integralCoefficients.{u}))).f n b) :
    integralChainEvaluation n v a = integralChainEvaluation n v b := by
  let E := HomologicalComplex.eval (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n
  have hS := (pointRelativeSequence_shortExact z integralCoefficients.{u}).map_of_exact E
  have hz : ((pointRelativeSequence z integralCoefficients.{u}).map E).g (a - b) = 0 := by
    change (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
      (constant X integralCoefficients.{u}))).f n (a - b) = 0
    let q := (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
      (constant X integralCoefficients.{u}))).f n
    exact (q.hom.map_sub a b).trans (sub_eq_zero.mpr hab)
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp hS.exact (a - b) hz
  apply sub_eq_zero.mp
  rw [← map_sub, ← hc]
  exact ConcreteCategory.congr_hom (pointPushforward_integralChainEvaluation z n v hv) c

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/PointRelativeEvaluation.lean:40-58"
  "adaptation" "Actual point quotient and original finite singular chains"]
  integralChainEvaluation_eq_of_pointRelative_eq

attribute [colib_tag "COL-0526"]
  integralChainEvaluation_eq_of_pointRelative_eq

end FundamentalGroupoid.LocalCoefficients
