/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneClasses

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers AlgebraicGeometry.MotivicCohomology.WeightOne

universe w u
noncomputable section
variable (k : Type u) [Field k]
  [HasDerivedCategory.{w}
    (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example (n : ℕ) (a : kˣ) :
    finiteCycleClass k n ((Cor.graphFunctor k).map (rationalPoint k a)) =
      finiteGraphUnitClass k n a := finiteCycleClass_graph k n a

example (n : ℕ) (m : ℤ) (z : point k ⟶ pointTarget k) :
    finiteCycleClass k n (m • z) = m • finiteCycleClass k n z :=
  finiteCycleClass_zsmul k n m z

example (n : ℕ) (z : point k ⟶ pointTarget k) :
    FieldTopDegree.topDegreeFiniteEquiv k 1 n (finiteCycleClass k n z) =
      (QuotientAddGroup.mk (integralCycleClass k z) : FieldTopDegree.integralModulo k 1 n) :=
  topDegreeFiniteEquiv_cycleClass k n z

example (n : ℕ) (a : kˣ) :
    FieldTopDegree.topDegreeFiniteEquiv k 1 n (finiteGraphUnitClass k n a) =
      (QuotientAddGroup.mk (integralGraphUnitClass k a) : FieldTopDegree.integralModulo k 1 n) :=
  topDegreeFiniteEquiv_graphUnitClass k n a

example (n : ℕ) (a : kˣ) :
    (FieldTopDegree.topDegreeFiniteEquiv k 1 n).symm
      (QuotientAddGroup.mk (integralGraphUnitClass k a) : FieldTopDegree.integralModulo k 1 n) =
        finiteGraphUnitClass k n a := topDegreeFiniteEquiv_symm_graphUnitClass k n a

example (n : ℕ) (a : kˣ) :
    motivicFiniteBaseConeComparison k 1 1 n (finiteGraphUnitClass k n a) =
      CochainComplex.finiteCoefficients.integralHomology (motivicBaseComplex k 1) n 1
        (motivicBaseEvaluationComparison k 1 1 (integralGraphUnitClass k a)) :=
  finiteGraphUnitClass_coneComparison k n a

example (n : ℕ) (x : motivicFiniteCohomology k 1 1 n (base (Spec (.of k)))) :
    motivicBaseBockstein k 1 1 n x = 0 := finiteWeightOne_bockstein_eq_zero k n x

example (n : ℕ) (a : kˣ) : finiteGraphUnitClass k n a = 0 ↔
    ∃ y : motivicCohomology k 1 1 (base (Spec (.of k))), n • y = integralGraphUnitClass k a :=
  finiteGraphUnitClass_eq_zero_iff k n a

example (a : kˣ) : finiteGraphUnitClass k 0 a = 0 ↔ integralGraphUnitClass k a = 0 :=
  finiteGraphUnitClass_zero_eq_zero_iff k a

example (a : kˣ) : finiteGraphUnitClass k 1 a = 0 := finiteGraphUnitClass_one k a

example (n : ℕ) (x : motivicFiniteCohomology k 1 1 n (base (Spec (.of k)))) : n • x = 0 :=
  finiteWeightOne_nsmul_eq_zero k n x
