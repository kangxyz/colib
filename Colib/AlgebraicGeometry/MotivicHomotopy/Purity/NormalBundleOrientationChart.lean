/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleChart
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.OrientationDescent
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ComplementComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.Support

/-! # The original supported arrows on normal-bundle charts -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite Contraction

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]
  {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X) [IsClosedImmersion i.left]
  {n m : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)

local notation "E₀" => (Stacks.Conormal.conormalSheafDegreeOne i.left : Z.left.Modules)
local notation "p" => normalBundleProjection i hX hZ
local notation "z" => normalBundleZeroSection i hX hZ
variable (V : Z.left.affineOpens)

set_option quotPrecheck false in
local notation "U" => (opensFunctor Z).obj V.1

/-- The two literal presentations of the complement over the chart open agree. -/
def normalBundleRestrictionArrowIso :
    (relativeOpenRestrictionPair k (p) (closedPairOpenInclusion (z).left)).obj V.1 ≅
      Arrow.mk (closedPairOpenInclusion (normalBundleZeroOn i hX hZ V).left) :=
  (openInclusionArrowIso (closedPairOpenInclusion (normalBundleZeroOn i hX hZ V).left)
    (preimageOpenMap (normalBundle i hX hZ) (closedPairOpenInclusion (z).left) ((p).left ⁻¹ᵁ V.1))
    (range_normalBundleZeroOn_open i hX hZ V)).symm

theorem normalBundleRestrictionArrowIso_hom_right :
    (normalBundleRestrictionArrowIso k i hX hZ V).hom.right = 𝟙 _ := (rfl)

set_option maxHeartbeats 500000 in
-- The native bundle and its chart use the same two smooth-site ambient objects.
/-- A basis chart induces the original identification of restricted supports. -/
def normalBundleBasisArrowIso
    (b : Module.Basis (Fin (n - m)) Γ(Z.left, V.1) Γ(E₀, V.1)) :
    (relativeOpenRestrictionPair k (p) (closedPairOpenInclusion (z).left)).obj V.1 ≅
      Arrow.mk (closedPairOpenInclusion (relativeAffineSpaceZeroSection U (n - m)).left) := by
  let t := normalBundleZeroOn i hX hZ V
  let t' := relativeAffineSpaceZeroSection U (n - m)
  let e := normalBundleBasisChart i hX hZ V b
  have hz : t ≫ e.hom = (Iso.refl U).hom ≫ t' :=
    (normalBundleBasisChart_zero i hX hZ V b).trans (Category.id_comp t').symm
  let : IsClosedImmersion t.left := normalBundleZeroOn_isClosedImmersion i hX hZ V
  let : IsClosedImmersion t'.left := affineSpaceOrigin_isClosedImmersion U (n - m)
  let f : Arrow.mk (closedPairOpenInclusion t.left) ≅
      Arrow.mk (closedPairOpenInclusion t'.left) :=
    closedSupportArrowIso (i := t) (j := t') e (Iso.refl U) hz
  exact normalBundleRestrictionArrowIso k i hX hZ V ≪≫ f

/-- The marked arrow comparison has the given chart as its ambient component. -/
theorem normalBundleBasisArrowIso_hom_right
    (b : Module.Basis (Fin (n - m)) Γ(Z.left, V.1) Γ(E₀, V.1)) :
    (normalBundleBasisArrowIso k i hX hZ V b).hom.right =
      (normalBundleBasisChart i hX hZ V b).hom := by
  change (normalBundleRestrictionArrowIso k i hX hZ V).hom.right ≫
    (normalBundleBasisChart i hX hZ V b).hom = _
  rw [normalBundleRestrictionArrowIso_hom_right, Category.id_comp]

end AlgebraicGeometry.MotivicHomotopy
