/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.RawClasses
public import Colib.AlgebraicGeometry.MotivicCohomology.FieldTopDegree

/-!
# Actual finite weight-one graph classes and the integral quotient

The positive integral insertion and Bockstein are those of the original
finite-coefficient cone. Every natural level is retained, including zero,
one and levels divisible by the characteristic. The top-degree equivalence
sends a reduced actual graph class to its actual integral class coset.

This does not identify that integral coset with a unit coset. That requires
the separately missing determinant-norm and graph-inverse dictionary.
The source scope is Motivic/Cohomology/Coefficients/Finite/WeightOne.lean at
revision a6805c4a87cdfd7717dd7a94039246a167f15380, with an explicit partial boundary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers NativeTorusPolynomial

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w}
    (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Reduction of genuine integral signed point-cycle classes under the original insertion. -/
def finiteCycleClass (n : ℕ) : (point k ⟶ pointTarget k) →+
    motivicFiniteCohomology k 1 1 n (base (Spec (.of k))) :=
  (motivicBaseIntegralReduction k 1 1 n).comp (integralCycleClass k)

/-- The literal rational graph followed by the actual positive integral reduction. -/
def finiteGraphUnitClass (n : ℕ) (a : kˣ) :
    motivicFiniteCohomology k 1 1 n (base (Spec (.of k))) :=
  motivicBaseIntegralReduction k 1 1 n (integralGraphUnitClass k a)

/-- The finite graph class retains the same geometric representative as its integral lift. -/
theorem finiteCycleClass_graph (n : ℕ) (a : kˣ) :
    finiteCycleClass k n ((Cor.graphFunctor k).map (rationalPoint k a)) =
      finiteGraphUnitClass k n a := rfl

/-- Signed native point multiplicities remain literal integer multiples after reduction. -/
theorem finiteCycleClass_zsmul (n : ℕ) (m : ℤ) (z : point k ⟶ pointTarget k) :
    finiteCycleClass k n (m • z) = m • finiteCycleClass k n z :=
  map_zsmul (finiteCycleClass k n) m z

/-- The existing actual top-degree quotient sends a reduced cycle to its integral coset. -/
theorem topDegreeFiniteEquiv_cycleClass (n : ℕ) (z : point k ⟶ pointTarget k) :
    FieldTopDegree.topDegreeFiniteEquiv k 1 n (finiteCycleClass k n z) =
      (QuotientAddGroup.mk (integralCycleClass k z) : FieldTopDegree.integralModulo k 1 n) :=
  FieldTopDegree.topDegreeFiniteEquiv_integralReduction k 1 n (integralCycleClass k z)

/-- In particular, the actual graph, with its positive insertion sign, maps to its own coset. -/
theorem topDegreeFiniteEquiv_graphUnitClass (n : ℕ) (a : kˣ) :
    FieldTopDegree.topDegreeFiniteEquiv k 1 n (finiteGraphUnitClass k n a) =
      (QuotientAddGroup.mk (integralGraphUnitClass k a) : FieldTopDegree.integralModulo k 1 n) :=
  FieldTopDegree.topDegreeFiniteEquiv_integralReduction k 1 n (integralGraphUnitClass k a)

/-- The inverse quotient map uses the original reduction of that same graph. -/
theorem topDegreeFiniteEquiv_symm_graphUnitClass (n : ℕ) (a : kˣ) :
    (FieldTopDegree.topDegreeFiniteEquiv k 1 n).symm
      (QuotientAddGroup.mk (integralGraphUnitClass k a) : FieldTopDegree.integralModulo k 1 n) =
        finiteGraphUnitClass k n a :=
  FieldTopDegree.topDegreeFiniteEquiv_symm_mk k 1 n (integralGraphUnitClass k a)

/-- The finite graph class agrees with the actual integral cone insertion under evaluation. -/
theorem finiteGraphUnitClass_coneComparison (n : ℕ) (a : kˣ) :
    motivicFiniteBaseConeComparison k 1 1 n (finiteGraphUnitClass k n a) =
      CochainComplex.finiteCoefficients.integralHomology (motivicBaseComplex k 1) n 1
        (motivicBaseEvaluationComparison k 1 1 (integralGraphUnitClass k a)) :=
  motivicBaseIntegralReduction_comparison k 1 1 n (integralGraphUnitClass k a)

/-- The genuine positive Bockstein vanishes on every finite weight-one field class. -/
theorem finiteWeightOne_bockstein_eq_zero (n : ℕ)
    (x : motivicFiniteCohomology k 1 1 n (base (Spec (.of k)))) :
    motivicBaseBockstein k 1 1 n x = 0 :=
  FieldTopDegree.bockstein_eq_zero k 1 1 n le_rfl x

/-- Vanishing of an actual reduced graph class means an actual integral multiple equation. -/
theorem finiteGraphUnitClass_eq_zero_iff (n : ℕ) (a : kˣ) :
    finiteGraphUnitClass k n a = 0 ↔
      ∃ y : motivicCohomology k 1 1 (base (Spec (.of k))),
        n • y = integralGraphUnitClass k a :=
  FieldTopDegree.integralReduction_eq_zero_iff k 1 n (integralGraphUnitClass k a)

/-- Every actual finite weight-one class is killed by its coefficient level. -/
theorem finiteWeightOne_nsmul_eq_zero (n : ℕ)
    (x : motivicFiniteCohomology k 1 1 n (base (Spec (.of k)))) : n • x = 0 :=
  FieldTopDegree.nsmul_eq_zero k 1 n x

/-- The graph formula also specializes to level zero without an invertibility premise. -/
theorem finiteGraphUnitClass_zero_eq_zero_iff (a : kˣ) :
    finiteGraphUnitClass k 0 a = 0 ↔ integralGraphUnitClass k a = 0 := by
  rw [finiteGraphUnitClass_eq_zero_iff]
  simp only [zero_nsmul, exists_const, eq_comm]

/-- The literal graph classes vanish at level one, just like the entire finite group. -/
theorem finiteGraphUnitClass_one (a : kˣ) : finiteGraphUnitClass k 1 a = 0 := by
  have h := finiteWeightOne_nsmul_eq_zero k 1 (finiteGraphUnitClass k 1 a)
  simpa only [one_nsmul] using h

end AlgebraicGeometry.MotivicCohomology.WeightOne
