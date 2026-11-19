/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.OpenNaturality.NormalBundle
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationPairBaseChange

/-! # The original normal fibre over the restricted centre -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open SmoothSite Stacks.Deformation

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]
  {Z X Z' X' : SmoothSite (Spec (CommRingCat.of k))} {i : Z ⟶ X} {j : Z' ⟶ X'}
  [IsClosedImmersion i.left] [IsClosedImmersion j.left]
  {f : X ⟶ X'} {g : Z ⟶ Z'} (h : IsPullback i.left g.left f.left j.left)

set_option maxHeartbeats 500000 in
-- Identify the literal zero sections in the input and target normal bundles.
/-- The original normal-bundle map pulls back the zero section in a flat square. -/
theorem smoothNormalFibreBaseChange_zero_isPullback [Flat f.left] :
    IsPullback (normalBundleZeroSectionOfSmooth i).left g.left
      (smoothNormalFibreBaseChange k h).left (normalBundleZeroSectionOfSmooth j).left := by
  let : Smooth (i.left ≫ X.hom) := smooth_closedPair_comp i
  let : Smooth (j.left ≫ X'.hom) := smooth_closedPair_comp j
  exact isPullback_deformationNormalZeroSection h X'.hom X.hom

set_option maxHeartbeats 500000 in
-- Use the original projection, which is independent of the witnesses of pure dimension.
/-- The map on the native normal bundles lies over the original map of centres. -/
theorem smoothNormalFibreBaseChange_projection {n m : ℕ}
    (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)
    (hX' : RelativeDimension X'.hom n) (hZ' : RelativeDimension Z'.hom m) :
    smoothNormalFibreBaseChange k h ≫ normalBundleProjection j hX' hZ' =
      normalBundleProjection i hX hZ ≫ g := by
  let : Smooth (i.left ≫ X.hom) := smooth_closedPair_comp i
  let : Smooth (j.left ≫ X'.hom) := smooth_closedPair_comp j
  apply MorphismProperty.Over.Hom.ext
  exact deformationNormalFibreMap_toBase h X.hom X'.hom

end AlgebraicGeometry.MotivicHomotopy
