/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineCylinderPowerComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.Support

/-! # The supported pairs of a native tower of affine lines and affine space -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite Contraction

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))

/-- The marked tower comparison identifies the original complement inclusions. -/
def affineCylinderPowerSupportIso (X : Sm) [IsAffine X.left] (n : ℕ) :
    Arrow.mk (closedPairOpenInclusion (affineCylinderPowerZero k X n).left) ≅
      Arrow.mk (closedPairOpenInclusion (relativeAffineSpaceZeroSection X n).left) :=
  closedSupportArrowIso
    (i := affineCylinderPowerZero k X n) (j := relativeAffineSpaceZeroSection X n)
    (affineCylinderPowerAffineSpaceIso k X n) (Iso.refl X)
    ((affineCylinderPowerAffineSpaceIso_zero k X n).trans
      (Category.id_comp (relativeAffineSpaceZeroSection X n)).symm)

/-- The two original ambient maps induce a commuting square of marked pairs. -/
theorem affineCylinderPowerSupportIso_hom_naturality
    {X Y : Sm} [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) (n : ℕ) :
    closedSupportArrowMap (f := affineCylinderPowerMap k f n) (g := f)
        (affineCylinderPowerZero_isPullback k f n) ≫ (affineCylinderPowerSupportIso k Y n).hom =
      (affineCylinderPowerSupportIso k X n).hom ≫
        closedSupportArrowMap (f := affineSpaceObjectMap f n) (g := f)
          (affineSpaceOrigin_isPullback f n) := by
  apply closedSupportArrowMap_eq_of_right
  exact affineCylinderPowerAffineSpaceIso_naturality k f n

/-- The inverse comparison transports restriction of affine spaces to restriction of
the original native towers. -/
theorem affineCylinderPowerSupportIso_inv_naturality
    {X Y : Sm} [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) (n : ℕ) :
    closedSupportArrowMap (f := affineSpaceObjectMap f n) (g := f)
        (affineSpaceOrigin_isPullback f n) ≫ (affineCylinderPowerSupportIso k Y n).inv =
      (affineCylinderPowerSupportIso k X n).inv ≫
        closedSupportArrowMap (f := affineCylinderPowerMap k f n) (g := f)
          (affineCylinderPowerZero_isPullback k f n) := by
  let e := affineCylinderPowerSupportIso k X n
  let e' := affineCylinderPowerSupportIso k Y n
  let a := closedSupportArrowMap (f := affineCylinderPowerMap k f n) (g := f)
    (affineCylinderPowerZero_isPullback k f n)
  let b := closedSupportArrowMap (f := affineSpaceObjectMap f n) (g := f)
    (affineSpaceOrigin_isPullback f n)
  have h : a ≫ e'.hom = e.hom ≫ b := affineCylinderPowerSupportIso_hom_naturality k f n
  change b ≫ e'.inv = e.inv ≫ a
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

end AlgebraicGeometry.MotivicHomotopy
