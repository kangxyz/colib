/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationEquivalences
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.Support
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Triangle

/-!
# The deformation comparison on relative motives

The two original fibre inclusions give a comparison with the normal bundle
by inverting the map from the original normal-bundle fibre. Composing with
the oriented Thom map identifies the relative motive with the indicated Tate
twist of the centre.
-/

@[expose] public noncomputable section

open AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open SmoothSite

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" k ")" => SmoothSite (Spec (CommRingCat.of k))

variable {Z X : Sm(k)} (i : Z ⟶ X) [IsClosedImmersion i.left] {n m : ℕ}
  (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)

set_option quotPrecheck false in
local notation "P₁" => effectivePairMotiveMap k (deformationOneSquare i)
set_option quotPrecheck false in
local notation "P₀" => effectivePairMotiveMap k (deformationZeroSquare i hX hZ)

/-- The deformation comparison is the map from the fibre at one followed
by the inverse of the map from the original normal-bundle fibre. -/
def effectiveDeformationComparison :
    effectiveMotiveWithSupport k i ≅
      effectiveMotiveWithSupport k (normalBundleZeroSection i hX hZ) :=
  @asIso _ _ _ _ (P₁) (isIso_effectivePairMotiveMap_deformationOne k i) ≪≫
    (@asIso _ _ _ _ (P₀) (isIso_effectivePairMotiveMap_deformationZero k i)).symm

set_option maxHeartbeats 900000 in
-- The two projected source and target motives come from the original deformation squares.
/-- Composing the deformation comparison with the actual normal fibre recovers
the original fibre-one comparison. -/
@[reassoc, simp]
theorem effectiveDeformationComparison_hom_comp_normal :
    (effectiveDeformationComparison k i hX hZ).hom ≫ (P₀) = (P₁) := by
  let e := @asIso _ _ _ _ (P₀) (isIso_effectivePairMotiveMap_deformationZero k i)
  have he : e.hom = (P₀) :=
    @asIso_hom _ _ _ _ (P₀) (isIso_effectivePairMotiveMap_deformationZero k i)
  have hc : (effectiveDeformationComparison k i hX hZ).hom = (P₁) ≫ e.inv := by
    unfold effectiveDeformationComparison
    exact congrArg (· ≫ e.inv)
      (@asIso_hom _ _ _ _ (P₁) (isIso_effectivePairMotiveMap_deformationOne k i))
  have hleft : (effectiveDeformationComparison k i hX hZ).hom ≫ (P₀) =
      ((P₁) ≫ e.inv) ≫ (P₀) := congrArg (· ≫ (P₀)) hc
  have hright : e.inv ≫ (P₀) = 𝟙 _ :=
    (congrArg (e.inv ≫ ·) he.symm).trans e.inv_hom_id
  have hfinal : ((P₁) ≫ e.inv) ≫ (P₀) = (P₁) :=
    (Category.assoc _ _ _).trans ((congrArg ((P₁) ≫ ·) hright).trans (Category.comp_id _))
  exact hleft.trans hfinal

variable [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

/-- Purity assembled from the original deformation maps and an oriented
normal-bundle Thom comparison of codimension `n - m`. -/
def effectivePurityOfThom
    (τ : effectiveMotiveWithSupport k (normalBundleZeroSection i hX hZ) ≅
      (Stabilization.iterate (effectiveLefschetzTwistFunctor k) (n - m)).obj
        ((effectiveSmoothMotive k).obj Z)) :
    effectiveMotiveWithSupport k i ≅
      (Stabilization.iterate (effectiveLefschetzTwistFunctor k) (n - m)).obj
        ((effectiveSmoothMotive k).obj Z) :=
  effectiveDeformationComparison k i hX hZ ≪≫ τ

end AlgebraicGeometry.MotivicHomotopy
