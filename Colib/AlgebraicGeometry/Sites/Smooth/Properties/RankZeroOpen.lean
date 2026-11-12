/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafIso
public import Colib.AlgebraicGeometry.Scheme.Stalk.Dimension.RankZero

/-! # Actual integral affine neighborhoods at a smooth rank-zero point -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Properties/RankZeroOpen.lean`, blob
`2db0b498de98e29c72e6eafb5c929818ffadb000`.
Native mathematical objects, original coefficient universes, and actual displayed maps are retained.

-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.SmoothSite
variable {k : Type u} [Field k]

/-- Every original smooth point has an actual integral affine open neighborhood.
This uses the native open component cover followed by its actual affine cover. -/
theorem exists_integral_affine_open (X : SmoothSite (Spec (.of k))) (x : X.left) :
    ∃ O : X.left.Opens, IsAffineOpen O ∧ x ∈ O ∧ IsIntegral O.toScheme := by
  let C := integralAffineCover k X
  obtain ⟨i, y, hy⟩ := C.exists_eq x
  let O := (C.f i).opensRange
  have hx : x ∈ O := ⟨y, hy⟩
  let : Nonempty O.toScheme := ⟨⟨x, hx⟩⟩
  have hi : IsIntegral O.toScheme :=
    isIntegral_of_isOpenImmersion (C.f i).isoOpensRange.inv
  exact ⟨O, isAffineOpen_opensRange (C.f i), hx, hi⟩

end AlgebraicGeometry.Scheme.SmoothSite
