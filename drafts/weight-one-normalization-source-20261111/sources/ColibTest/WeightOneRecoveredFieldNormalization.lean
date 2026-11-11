module
import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.FieldEquivalence
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.MotivicCohomology.WeightOne
open AlgebraicGeometry.PresheafWithTransfers
universe u
variable (k : Type u) [Field k]
example (z : point k ⟶ pointTarget k) :
    rawComparisonNorm k (cycleClass k z) = pointCycleNorm k z :=
  rawComparisonNorm_cycleClass k z
example (a : kˣ) : rawComparisonNorm k (graphUnitClass k a) = Additive.ofMul a :=
  rawComparisonNorm_graphUnitClass k a
example (a : Additive kˣ) : (homologyEquiv k).symm a = graphUnitClass k a.toMul :=
  homologyEquiv_symm_apply k a
example (a b : kˣ) : graphUnitClass k (a * b) = graphUnitClass k a + graphUnitClass k b :=
  graphUnitClass_mul k a b
example (z : point k ⟶ pointTarget k) :
    cycleClass k z = graphUnitClass k (pointCycleNorm k z).toMul :=
  cycleClass_eq_graphUnitClass_norm k z
