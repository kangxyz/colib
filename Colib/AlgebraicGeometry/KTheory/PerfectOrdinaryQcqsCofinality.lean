/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.QcqsGeometry
public import Colib.AlgebraicGeometry.KTheory.OpenDerivedImageCofinality
/-! # Original ordinary qcqs restriction cofinality

Actual native qcqs roofs and perfect complements discharge the original geometric inputs.
The native relative cofinality theorem already constructs the original dense cofiber and
joint weak-arrow data. This keeps exactly the original restriction map and honest K-zero
injectivity; no surjectivity onto all local K-zero is asserted.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory
open OpenDerivedImage
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]
/-- The unchanged ordinary relative restriction is bijective in positive degrees. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GlobalCofinality.lean:48"
  "adaptation" "Original actual qcqs roofs and complements discharge ordinary cofinality"]
theorem qcqs_perfectOpenKRestrict_succ_bijective (n : ℕ) :
    Function.Bijective (perfectOpenKRestrict j (n + 1)) := by
  let : Fact (HasDerivedRoofs j) := ⟨hasDerivedRoofs_of_qcqs j⟩
  exact relativeKRestrict_succ_bijective j (hasPerfectComplements_of_qcqs j) n
/-- The same actual ordinary restriction remains injective in degree zero as well. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GlobalCofinality.lean:56"
  "adaptation" "Original actual qcqs roofs and complements discharge ordinary cofinality"]
theorem qcqs_perfectOpenKRestrict_injective (n : ℕ) :
    Function.Injective (perfectOpenKRestrict j n) := by
  let : Fact (HasDerivedRoofs j) := ⟨hasDerivedRoofs_of_qcqs j⟩
  exact relativeKRestrict_injective j (hasPerfectComplements_of_qcqs j) n
end AlgebraicGeometry.Scheme.Modules
