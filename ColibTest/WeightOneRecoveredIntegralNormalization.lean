/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.IntegralEquivalence
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.MotivicCohomology.WeightOne
open AlgebraicGeometry.PresheafWithTransfers
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
universe w u
variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
example (a : Additive kˣ) :
    (weightOneEquiv k).symm a = integralGraphUnitClass k a.toMul :=
  weightOneEquiv_symm_apply k a
example (z : point k ⟶ pointTarget k) :
    motivicNorm k (integralCycleClass k z) = pointCycleNorm k z :=
  motivicNorm_integralCycleClass k z
example (a : kˣ) : motivicNorm k (integralGraphUnitClass k a) = Additive.ofMul a :=
  motivicNorm_integralGraphUnitClass k a
example (x : motivicCohomology k 1 1 (base (Spec (.of k)))) :
    motivicNorm k x = shiftedUnitsBaseHomologyEquiv k
      (hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) 1
        (derivedWeightOneComparison k 1 x)) :=
  motivicNorm_eq_derivedWeightOneComparison k x
