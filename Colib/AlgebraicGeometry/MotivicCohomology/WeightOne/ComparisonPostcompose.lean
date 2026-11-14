/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.FieldComparisonMap

/-! # The specified derived weight-one comparison is its actual coefficient postcomposition -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
universe w u
namespace AlgebraicGeometry.MotivicCohomology.WeightOne
variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The existing derived weight-one map postcomposes with the existing sheaf comparison. -/
lemma derivedWeightOneComparison_eq_postcompose (p : ℤ)
    (x : motivicCohomology k p 1 (base (Spec (.of k)))) :
    derivedWeightOneComparison k p x =
      x ≫ (DerivedCategory.Q.map (weightOneSheafComparison k))⟦p⟧' := rfl

end AlgebraicGeometry.MotivicCohomology.WeightOne
