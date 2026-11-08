/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectOpenLongExactSequence

/-!
# The degree-zero range of actual open restriction

The coarse change-of-weak-equivalences map is surjective in degree zero. Its literal
factorization of restriction therefore identifies the two actual ranges in perfect K-theory
of the open. This does not assert surjectivity onto that K-group.
-/

@[expose] public noncomputable section

open CategoryTheory Waldhausen

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The relative coarse restriction and the original restriction have the same degree-zero
range, for every open immersion, without quasi-compactness or quasi-separatedness. -/
theorem range_perfectOpenKRestrict_zero {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (perfectOpenKRestrict j 0).range =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).range := by
  rw [← perfectOpenKRestrict_comp_perfectOpenKMap, MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 (perfectOpenKMap_zero_surjective j), Subgroup.map_top]

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0312",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/OpenKZeroImage.lean:25-36"
    "adaptation" "Degree-zero equality of the actual coarse and fine restriction ranges"]
  AlgebraicGeometry.Scheme.Modules.range_perfectOpenKRestrict_zero
