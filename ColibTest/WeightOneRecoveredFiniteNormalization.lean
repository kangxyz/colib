/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOne

/-!
# Consumers of the finite weight-one normalization

These examples state the public equivalence and its actual norm and graph
formulas at every level, including zero, one, composite and characteristic levels.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.PresheafWithTransfers
open AlgebraicGeometry.MotivicCohomology.WeightOne
open AlgebraicGeometry.MotivicCohomology.WeightOneFiniteCoefficients
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
universe w u
variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example (n : ℕ) :
    motivicFiniteCohomology k 1 1 n (base (Spec (.of k))) ≃+
      Additive (kˣ ⧸ (powMonoidHom n).range) :=
  weightOneFiniteEquiv k n

example (n : ℕ) (x : motivicCohomology k 1 1 (base (Spec (.of k)))) :
    weightOneFiniteEquiv k n (motivicBaseIntegralReduction k 1 1 n x) =
      Additive.ofMul (QuotientGroup.mk (motivicNorm k x).toMul : unitsModuloPowers k n) :=
  weightOneFiniteEquiv_integralReduction k n x

example (n : ℕ) (a : kˣ) :
    (weightOneFiniteEquiv k n).symm
      (Additive.ofMul (QuotientGroup.mk a : unitsModuloPowers k n)) =
        motivicBaseIntegralReduction k 1 1 n
          ((motivicRawBaseEvaluationComparison k 1 1).symm (graphUnitClass k a)) :=
  weightOneFiniteEquiv_symm_graph k n a

example (n : ℕ) (a : kˣ) :
    (weightOneFiniteEquiv k n).symm
      (Additive.ofMul (QuotientGroup.mk a : unitsModuloPowers k n)) =
        finiteGraphUnitClass k n a :=
  weightOneFiniteEquiv_symm_graphUnitClass k n a

example (n : ℕ) (z : point k ⟶ pointTarget k) :
    weightOneFiniteEquiv k n (finiteCycleClass k n z) =
      Additive.ofMul (QuotientGroup.mk (pointCycleNorm k z).toMul :
        unitsModuloPowers k n) :=
  weightOneFiniteEquiv_cycleClass k n z

example (n : ℕ) (a : kˣ) :
    finiteGraphUnitClass k n a = 0 ↔ ∃ b : kˣ, b ^ n = a :=
  finiteGraphUnitClass_eq_zero_iff_power k n a

example (a : kˣ) :
    weightOneFiniteEquiv k 0 (unitReduction k 0 (Additive.ofMul a)) =
      Additive.ofMul (QuotientGroup.mk a : unitsModuloPowers k 0) :=
  weightOneFiniteEquiv_unitReduction k 0 a

example (a : kˣ) : finiteGraphUnitClass k 0 a = 0 ↔ a = 1 := by
  rw [finiteGraphUnitClass_eq_zero_iff_power]
  simp only [pow_zero, exists_const, eq_comm]

example : Subsingleton (motivicFiniteCohomology k 1 1 1 (base (Spec (.of k)))) :=
  subsingleton_level_one k

example (a : kˣ) :
    weightOneFiniteEquiv k 6 (finiteGraphUnitClass k 6 a) =
      Additive.ofMul (QuotientGroup.mk a : unitsModuloPowers k 6) :=
  weightOneFiniteEquiv_graphUnitClass k 6 a

example (p : ℕ) [CharP k p] (a : kˣ) :
    weightOneFiniteEquiv k p (finiteGraphUnitClass k p a) =
      Additive.ofMul (QuotientGroup.mk a : unitsModuloPowers k p) :=
  weightOneFiniteEquiv_graphUnitClass k p a
