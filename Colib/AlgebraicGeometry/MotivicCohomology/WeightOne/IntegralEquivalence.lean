/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.FieldEquivalence

/-!
# The integral weight-one norm and its actual graph inverse

The existing derived/raw comparison transports the normalized geometric norm.
Its inverse retains the literal rational graph class. The last formula identifies
the forward map with the specified derived sheaf comparison, so no independently
chosen unit-group equivalence is substituted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The norm on the originally defined integral motivic cohomology group. -/
@[colib_tag "COL-1008",
  colib_ref "motivic_source_a6805c4"
    "Motivic/Cohomology/WeightOne/HomologyNorm.lean:131-135" "adaptation"
    "The actual derived norm transported through base-field evaluation"]
def motivicNorm : motivicCohomology k 1 1 (base (Spec (.of k))) →+ Additive kˣ :=
  (homologyNorm k).comp (motivicRawBaseEvaluationComparison k 1 1).toAddMonoidHom

/-- Integral weight-one cohomology of the original base field is its unit group. -/
@[colib_tag "COL-1008",
  colib_ref "motivic_source_a6805c4"
    "Motivic/Cohomology/WeightOne/Equivalence.lean:291-299" "adaptation"
    "Integral weight-one equivalence whose forward map is the actual geometric norm"]
def weightOneEquiv : motivicCohomology k 1 1 (base (Spec (.of k))) ≃+ Additive kˣ :=
  (motivicRawBaseEvaluationComparison k 1 1).trans (homologyEquiv k)

@[simp] theorem weightOneEquiv_apply
    (x : motivicCohomology k 1 1 (base (Spec (.of k)))) :
    weightOneEquiv k x = motivicNorm k x := rfl

/-- The actual derived norm retains the determinant of each signed point cycle. -/
@[colib_tag "COL-1008"]
theorem motivicNorm_integralCycleClass (z : point k ⟶ pointTarget k) :
    motivicNorm k (integralCycleClass k z) = pointCycleNorm k z := by
  change homologyNorm k ((motivicRawBaseEvaluationComparison k 1 1)
    ((motivicRawBaseEvaluationComparison k 1 1).symm (cycleClass k z))) = _
  rw [AddEquiv.apply_symm_apply, homologyNorm_cycleClass]

/-- The integral rational graph class has the original unit as its norm. -/
@[simp, colib_tag "COL-1008"] theorem motivicNorm_integralGraphUnitClass (a : kˣ) :
    motivicNorm k (integralGraphUnitClass k a) = Additive.ofMul a := by
  change homologyNorm k ((motivicRawBaseEvaluationComparison k 1 1)
    (integralGraphUnitClass k a)) = _
  rw [integralGraphUnitClass_comparison]
  exact rawComparisonNorm_graphUnitClass k a

/-- The inverse equivalence is precisely the existing integral rational graph class. -/
@[colib_tag "COL-1008",
  colib_ref "motivic_source_a6805c4"
    "Motivic/Cohomology/WeightOne/Equivalence.lean:301-307" "adaptation"
    "The inverse equivalence is the actual graph class under base-field evaluation"]
theorem weightOneEquiv_symm_apply (a : Additive kˣ) :
    (weightOneEquiv k).symm a = integralGraphUnitClass k a.toMul := by
  change (motivicRawBaseEvaluationComparison k 1 1).symm
    ((homologyEquiv k).symm a) = _
  rw [homologyEquiv_symm_apply]
  rfl

/-- The normalized forward map is the actual derived geometric sheaf map. -/
@[colib_tag "COL-1008"]
theorem motivicNorm_eq_derivedWeightOneComparison
    (x : motivicCohomology k 1 1 (base (Spec (.of k)))) :
    motivicNorm k x = shiftedUnitsBaseHomologyEquiv k
      (hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) 1
        (derivedWeightOneComparison k 1 x)) := by
  rw [rawWeightOneComparison_derived]
  rfl

end AlgebraicGeometry.MotivicCohomology.WeightOne
