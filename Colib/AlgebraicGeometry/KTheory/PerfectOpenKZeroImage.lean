/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectOpenRestrictionRange

/-!
# The actual degree-zero restriction-image subgroup

The codomain is the actual range of fine global restriction, not all perfect K-zero of the
open. The existing unconditional equality of fine and coarse ranges supplies the literal
codomain-restricted map and its surjectivity. Its injectivity is a separate cofinality theorem.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/OpenKZeroImage.lean:38-65`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The honest target consists of classes in the actual global fine restriction range. -/
abbrev PerfectOpenKZeroImage := (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).range

/-- The unchanged relative restriction, with codomain restricted to its proved actual image. -/
def perfectOpenKZeroToImage : PerfectOpenK j 0 →* PerfectOpenKZeroImage j :=
  (perfectOpenKRestrict j 0).codRestrict (PerfectOpenKZeroImage j) (fun a => by
    change perfectOpenKRestrict j 0 a ∈
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).range
    rw [← range_perfectOpenKRestrict_zero j]
    exact ⟨a, rfl⟩)

/-- Forgetting membership gives exactly the original relative restriction map. -/
@[simp] theorem perfectOpenKZeroToImage_coe (a : PerfectOpenK j 0) :
    (perfectOpenKZeroToImage j a :
      (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 0) =
        perfectOpenKRestrict j 0 a := rfl

/-- Every class of the actual fine restriction image has a relative representative. -/
theorem perfectOpenKZeroToImage_surjective : Function.Surjective (perfectOpenKZeroToImage j) := by
  rintro ⟨x, a, rfl⟩
  refine ⟨perfectOpenKMap j 0 a, ?_⟩
  apply Subtype.ext
  exact DFunLike.congr_fun (perfectOpenKRestrict_comp_perfectOpenKMap j 0) a

/-- Codomain restriction does not change the original kernel. -/
@[simp] theorem perfectOpenKZeroToImage_ker :
    (perfectOpenKZeroToImage j).ker = (perfectOpenKRestrict j 0).ker := by
  ext a
  change (perfectOpenKZeroToImage j a = 1) ↔ perfectOpenKRestrict j 0 a = 1
  exact Subtype.ext_iff

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0315",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/OpenKZeroImage.lean:38-65"
    "adaptation" "Actual fine restriction range and unchanged relative map \
    with codomain restricted"]
  AlgebraicGeometry.Scheme.Modules.PerfectOpenKZeroImage
  AlgebraicGeometry.Scheme.Modules.perfectOpenKZeroToImage
  AlgebraicGeometry.Scheme.Modules.perfectOpenKZeroToImage_surjective
