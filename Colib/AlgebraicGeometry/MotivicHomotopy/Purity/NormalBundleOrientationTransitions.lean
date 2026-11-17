/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineFrameParameterAction
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleOrientationChart
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.VectorBundleFrameChange

/-! # Change of frame and open restriction of the original supported normal chart -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite

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

set_option maxHeartbeats 550000 in
-- The transition is compared on the underlying affine schemes.
/-- The normal chart arrow transforms by the actual transition matrix between the frames. -/
theorem normalBundleBasisArrowIso_frameChange
    (b b' : Module.Basis (Fin (n - m)) Γ(Z.left, V.1) Γ(E₀, V.1)) :
    (normalBundleBasisArrowIso k i hX hZ V b).hom ≫
        affineSpaceMatrixSupportArrowMap U (n - m)
          (Scheme.Modules.vectorBundleFrameChangeMatrix E₀ V b b') =
      (normalBundleBasisArrowIso k i hX hZ V b').hom := by
  let A := Scheme.Modules.vectorBundleFrameChangeMatrix E₀ V b b'
  let α := affineSpaceMatrixSupportArrowMap U (n - m) A
  let q := normalBundleBasisArrowIso k i hX hZ V b
  let q' := normalBundleBasisArrowIso k i hX hZ V b'
  apply openPairArrowMap_eq_of_right
  change q.hom.right ≫ α.right = q'.hom.right
  rw [normalBundleBasisArrowIso_hom_right, normalBundleBasisArrowIso_hom_right]
  apply MorphismProperty.Over.Hom.ext
  let e := Scheme.Modules.vectorBundleBasisChart E₀ V b
  let e' := Scheme.Modules.vectorBundleBasisChart E₀ V b'
  change e.hom ≫ AffineSpace.matrixMap A.val = e'.hom
  have hf : e.inv ≫ e'.hom = AffineSpace.matrixMap A.val :=
    Scheme.Modules.vectorBundleBasisChart_frameChange E₀ V b b'
  exact (congrArg (e.hom ≫ ·) hf.symm).trans (e.hom_inv_id_assoc e'.hom)

set_option maxHeartbeats 550000 in
-- The ambient open inclusion uses the literal restriction of the underlying spectrum.
/-- The normal chart arrow on an affine subopen is the restriction of the marked chart. -/
theorem normalBundleBasisArrowIso_restrict
    (b : Module.Basis (Fin (n - m)) Γ(Z.left, V.1) Γ(E₀, V.1))
    (W : Z.left.affineOpens) (h : W.1 ≤ V.1) :
    let f := (opensFunctor Z).map (homOfLE h)
    (relativeOpenRestrictionPair k (p) (closedPairOpenInclusion (z).left)).map (homOfLE h) ≫
        (normalBundleBasisArrowIso k i hX hZ V b).hom =
      (normalBundleBasisArrowIso k i hX hZ W
        (Scheme.Modules.vectorBundleBasisRestrict E₀ b h)).hom ≫
        closedSupportArrowMap (f := affineSpaceObjectMap f (n - m)) (g := f)
          (affineSpaceOrigin_isPullback f (n - m)) := by
  intro f
  let b₁ := Scheme.Modules.vectorBundleBasisRestrict E₀ b h
  let α := (relativeOpenRestrictionPair k (p) (closedPairOpenInclusion (z).left)).map (homOfLE h)
  let β := closedSupportArrowMap (f := affineSpaceObjectMap f (n - m)) (g := f)
    (affineSpaceOrigin_isPullback f (n - m))
  let q₀ := normalBundleBasisArrowIso k i hX hZ W b₁
  let q₁ := normalBundleBasisArrowIso k i hX hZ V b
  let g := (normalBundle i hX hZ).left.homOfLE ((p).left.preimage_mono h)
  have hα : α.right.left = g := rfl
  have hβ : β.right.left = (affineSpaceObjectMap f (n - m)).left := rfl
  apply openPairArrowMap_eq_of_right
  change α.right ≫ q₁.hom.right = q₀.hom.right ≫ β.right
  rw [normalBundleBasisArrowIso_hom_right, normalBundleBasisArrowIso_hom_right]
  apply MorphismProperty.Over.Hom.ext
  let e₀ := Scheme.Modules.vectorBundleBasisChart E₀ W b₁
  let e₁ := Scheme.Modules.vectorBundleBasisChart E₀ V b
  change α.right.left ≫ e₁.hom = e₀.hom ≫ β.right.left
  rw [hα, hβ]
  exact Scheme.Modules.vectorBundleBasisChart_restrict E₀ b h

end AlgebraicGeometry.MotivicHomotopy
