/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenPullback
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenMaps
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupportedOriginalRestriction

/-! # Original relative restriction comparison on K-groups -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
/-- The original relative restriction commutes with the literal bounded-flat inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenNaturality.lean:136"
  "adaptation" "Original actual supported algebraic pullback and restriction square."]
lemma boundedAboveFlatPerfectSupportedOpenKRestrict_comparison (n : ℕ) :
    (perfectSupportedOpenKRestrict j T n).comp
      (boundedAboveFlatPerfectSupportedOpenToPerfectKMap j T n) =
      (boundedAboveFlatPerfectSupportedToPerfectKMap (j ⁻¹ᵁ T).ι n).comp
        (boundedAboveFlatPerfectSupportedOpenKRestrict j n) := by
  unfold perfectSupportedOpenKRestrict boundedAboveFlatPerfectSupportedOpenToPerfectKMap
    boundedAboveFlatPerfectSupportedToPerfectKMap boundedAboveFlatPerfectSupportedOpenKRestrict
  rw [CategoryTheory.Waldhausen.KMap_comp_KMap, CategoryTheory.Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (boundedAboveFlatPerfectSupportedOriginalRestrictionIso j T) n

end AlgebraicGeometry.Scheme.Modules
