/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationComparison
import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationPairBaseChange

/-! # Naturality of the deformation comparison under maps of closed pairs -/

@[expose] public noncomputable section

open AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open SmoothSite Stacks.Deformation

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))
local notation "P" => effectivePairMotiveFunctor k

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option Elab.async false in
set_option maxHeartbeats 2000000 in
-- Map the two fibre squares before cancelling the normal-fibre isomorphism.
/-- A map of deformations that preserves the support and commutes with both fibres
intertwines the original deformation comparisons on supported motives. -/
theorem effectiveDeformationComparison_naturality
    {Z X Z' X' : Sm} {i : Z ⟶ X} {j : Z' ⟶ X'}
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    {n m n' m' : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)
    (hX' : RelativeDimension X'.hom n') (hZ' : RelativeDimension Z'.hom m')
    {f : X' ⟶ X} {g : Z' ⟶ Z} (h : IsPullback j.left g.left f.left i.left)
    {a : closedPairDeformation j ⟶ closedPairDeformation i}
    {b : deformationSupport Z' ⟶ deformationSupport Z}
    (ha : IsPullback (deformationSupportInclusion j).left b.left a.left
      (deformationSupportInclusion i).left)
    {v : normalBundleOfSmooth j ⟶ normalBundleOfSmooth i}
    (hv : IsPullback (normalBundleZeroSection j hX' hZ').left g.left v.left
      (normalBundleZeroSection i hX hZ).left)
    (h₁ : deformationOneMap j ≫ a = f ≫ deformationOneMap i)
    (h₀ : deformationNormalMapOfSmooth j ≫ a = v ≫ deformationNormalMapOfSmooth i) :
    effectiveMotiveWithSupportMap k (i := j) (j := i) (f := f) (g := g) h ≫
        (effectiveDeformationComparison k i hX hZ).hom =
      (effectiveDeformationComparison k j hX' hZ').hom ≫
        effectiveMotiveWithSupportMap k (i := normalBundleZeroSectionOfSmooth j)
          (j := normalBundleZeroSectionOfSmooth i) (f := v) (g := g) hv := by
  let F₁ := deformationOneSquare j
  let G₁ := deformationOneSquare i
  let F₀ := deformationZeroSquareOfSmooth j
  let G₀ := deformationZeroSquareOfSmooth i
  let A := closedSupportArrowMap (i := j) (j := i) (f := f) (g := g) h
  let B := closedSupportArrowMap
    (i := deformationSupportInclusion j) (j := deformationSupportInclusion i)
    (f := a) (g := b) ha
  let N := closedSupportArrowMap (i := normalBundleZeroSectionOfSmooth j)
    (j := normalBundleZeroSectionOfSmooth i) (f := v) (g := g) hv
  let : IsOpenImmersion G₁.f₂₄.left := inferInstanceAs
    (IsOpenImmersion (closedPairOpenInclusion (deformationSupportInclusion i).left).left)
  let : IsOpenImmersion G₀.f₂₄.left := inferInstanceAs
    (IsOpenImmersion (closedPairOpenInclusion (deformationSupportInclusion i).left).left)
  have c₁ : CommSq (pairSquareArrow F₁) A B (pairSquareArrow G₁) :=
    ⟨pairSquareArrow_comm_of_ambient F₁ G₁ A B h₁⟩
  have c₀ : CommSq (pairSquareArrow F₀) N B (pairSquareArrow G₀) :=
    ⟨pairSquareArrow_comm_of_ambient F₀ G₀ N B h₀⟩
  let p := effectivePairMotiveMap k G₀
  let : IsIso p := isIso_effectivePairMotiveMap_deformationZero k i
  have w₁ : (P).map A ≫ effectivePairMotiveMap k G₁ =
      effectivePairMotiveMap k F₁ ≫ (P).map B := ((c₁.map (P)).w).symm
  have w₀ : (P).map N ≫ p = effectivePairMotiveMap k F₀ ≫ (P).map B :=
    ((c₀.map (P)).w).symm
  have e₁ : (effectiveDeformationComparison k i hX hZ).hom ≫ p =
      effectivePairMotiveMap k G₁ := effectiveDeformationComparison_hom_comp_normal k i hX hZ
  have e₀ : (effectiveDeformationComparison k j hX' hZ').hom ≫ effectivePairMotiveMap k F₀ =
      effectivePairMotiveMap k F₁ := effectiveDeformationComparison_hom_comp_normal k j hX' hZ'
  change (P).map A ≫ (effectiveDeformationComparison k i hX hZ).hom =
    (effectiveDeformationComparison k j hX' hZ').hom ≫ (P).map N
  apply (cancel_mono p).1
  exact (Category.assoc _ _ _).trans ((congrArg ((P).map A ≫ ·) e₁).trans
    (w₁.trans ((congrArg (· ≫ (P).map B) e₀.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg
        ((effectiveDeformationComparison k j hX' hZ').hom ≫ ·) w₀.symm).trans
          (Category.assoc _ _ _).symm)))))

set_option Elab.async false in
set_option maxHeartbeats 1800000 in
-- Use the literal deformation maps furnished by flat base change.
/-- Flat base change of a smooth closed pair commutes with the original deformation
comparison between supported motives. -/
theorem effectiveDeformationComparison_naturality_of_flat
    {Z X Z' X' : Sm} {i : Z ⟶ X} {j : Z' ⟶ X'}
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    {n m n' m' : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)
    (hX' : RelativeDimension X'.hom n') (hZ' : RelativeDimension Z'.hom m')
    {f : X' ⟶ X} {g : Z' ⟶ Z} (h : IsPullback j.left g.left f.left i.left) [Flat f.left] :
    let v := smoothNormalFibreBaseChange k h
    let hv : IsPullback (normalBundleZeroSectionOfSmooth j).left g.left v.left
        (normalBundleZeroSectionOfSmooth i).left := by
      let := smooth_closedPair_comp i
      let := smooth_closedPair_comp j
      exact isPullback_deformationNormalZeroSection h X.hom X'.hom
    effectiveMotiveWithSupportMap k (i := j) (j := i) (f := f) (g := g) h ≫
        (effectiveDeformationComparison k i hX hZ).hom =
      (effectiveDeformationComparison k j hX' hZ').hom ≫
        effectiveMotiveWithSupportMap k (i := normalBundleZeroSectionOfSmooth j)
          (j := normalBundleZeroSectionOfSmooth i) (f := v) (g := g) hv := by
  intro v hv
  let a := smoothDeformationBaseChange k h
  let b := smoothDeformationSupportBaseChange k g
  have ha : IsPullback (deformationSupportInclusion j).left b.left a.left
      (deformationSupportInclusion i).left := smoothDeformationSupportBaseChange_isPullback k h
  have h₁ : deformationOneMap j ≫ a = f ≫ deformationOneMap i := by
    apply MorphismProperty.Over.Hom.ext
    exact closedPairOneSection_deformationMapOver h
  have h₀ : deformationNormalMapOfSmooth j ≫ a = v ≫ deformationNormalMapOfSmooth i := by
    let := smooth_closedPair_comp i
    let := smooth_closedPair_comp j
    apply MorphismProperty.Over.Hom.ext
    exact (isPullback_deformationNormalFibreMap h X.hom X'.hom).w
  exact effectiveDeformationComparison_naturality k hX hZ hX' hZ' h ha hv h₁ h₀

end AlgebraicGeometry.MotivicHomotopy
