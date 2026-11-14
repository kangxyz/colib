/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.IntegralEquivalence

/-! # The original derived weight-one section uses the original geometric norm -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
universe w u
namespace AlgebraicGeometry.MotivicCohomology.WeightOne
variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The actual derived weight-one section is the global unit obtained from the original norm. -/
lemma derivedWeightOneComparison_globalUnit
    (x : motivicCohomology k 1 1 (base (Spec (.of k)))) :
    ((shiftedUnitsBaseHomologyIso k).hom
      (hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) 1
        (derivedWeightOneComparison k 1 x))).down =
      Additive.ofMul (specGlobalUnit (motivicNorm k x).toMul) := by
  let v := (shiftedUnitsBaseHomologyIso k).hom
    (hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) 1
      (derivedWeightOneComparison k 1 x))
  let e := NativeTorusPolynomial.specUnitsIso (𝟙 (Spec (.of k)))
  have hn : ULift.up (motivicNorm k x) = e.hom v := by
    rw [motivicNorm_eq_derivedWeightOneComparison]
    rfl
  have he : e.inv (e.hom v) = v :=
    ConcreteCategory.congr_hom e.hom_inv_id v
  change v.down = _
  calc
    v.down = (e.inv (ULift.up (motivicNorm k x))).down := by
      rw [hn]
      exact congrArg ULift.down he.symm
    _ = _ := congrArg ULift.down
      (NativeTorusPolynomial.specUnitsIso_inv_apply (𝟙 (Spec (.of k)))
        (motivicNorm k x).toMul)

end AlgebraicGeometry.MotivicCohomology.WeightOne
