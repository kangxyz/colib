/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenRestrictionExact
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectOriginalRestriction
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenSupport
/-! # The original ordinary relative restriction K-map and inclusion square -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
/-- The degree-`n` K-map from the bounded-flat relative-open model for `j : U ⟶ X` to bounded-flat
perfect K-theory on `U`, induced by restriction. -/
@[colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/PairRestriction.lean:56"
  "adaptation" "Original ordinary restriction K-map and actual inclusion square"]
def boundedAboveFlatPerfectOpenKRestrict (n : ℕ) :
    BoundedAboveFlatPerfectOpenK j n →*
    RingedSpace.boundedAboveFlatPerfectK U.toRingedSpace n :=
  CategoryTheory.Waldhausen.KMap (boundedAboveFlatPerfectOpenRestriction_exact j) n

/-- The original inclusion square commutes with the actual relative restriction K-map. -/
@[colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/PairRestriction.lean:60"
  "adaptation" "Original ordinary restriction K-map and actual inclusion square"]
theorem boundedAboveFlatPerfectOpenKRestrict_comparison (n : ℕ) :
    (perfectOpenKRestrict j n).comp (boundedAboveFlatPerfectOpenToPerfectOpenKMap j n) =
      (RingedSpace.boundedAboveFlatPerfectToPerfectKMap U.toRingedSpace n).comp
        (boundedAboveFlatPerfectOpenKRestrict j n) := by
  unfold perfectOpenKRestrict boundedAboveFlatPerfectOpenToPerfectOpenKMap
    RingedSpace.boundedAboveFlatPerfectToPerfectKMap boundedAboveFlatPerfectOpenKRestrict
  rw [CategoryTheory.Waldhausen.KMap_comp_KMap, CategoryTheory.Waldhausen.KMap_comp_KMap]
  exact CategoryTheory.Waldhausen.KMap_eq_of_iso _ _
    (boundedAboveFlatPerfectOriginalRestrictionIso j) n

end AlgebraicGeometry.Scheme.Modules
