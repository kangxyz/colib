/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.ClosedImmersion
public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.OpenNaturality.ThomClass
import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationNaturality

/-! # Naturality of effective purity under open restriction -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open SmoothSite MonoidalCategory

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]

attribute [local instance] thomGraphBasicCorSheafify thomGraphBasicSmoothSheafify

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Φ" => effectivePairMotiveFunctor k
local notation "M" => effectiveSmoothMotive k

attribute [local instance] thomGraphBasicBaseNoetherian thomGraphBasicAbelian
  thomGraphBasicMonoidal

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable
  effectivePairThomGraph

variable {Z X Z' X' : SmoothSite (Spec (CommRingCat.of k))} {i : Z ⟶ X} {j : Z' ⟶ X'}
  [IsClosedImmersion i.left] [IsClosedImmersion j.left]
  {f : X ⟶ X'} {g : Z ⟶ Z'} (h : IsPullback i.left g.left f.left j.left)
  {n m : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)
  (hX' : RelativeDimension X'.hom n) (hZ' : RelativeDimension Z'.hom m)

local notation "L" => Stabilization.iterate (effectiveLefschetzTwistFunctor k) (n - m)
local notation "N" => normalBundleZeroSectionOfSmooth i
local notation "N'" => normalBundleZeroSectionOfSmooth j
local notation "v" => smoothNormalFibreBaseChange k h

section Flat

variable [Flat f.left] [IsOpenImmersion g.left]

local notation "hN" => smoothNormalFibreBaseChange_zero_isPullback k h
local notation "ν" => closedSupportArrowMap (i := N) (j := N') (f := v) (g := g) (hN)

set_option maxHeartbeats 1200000 in
-- Apply graph naturality and the original tensor comparison to the normalized class.
/-- The actual Thom isomorphism is natural for a flat square with open centre map. -/
theorem effectiveNormalBundleThomIso_naturality_of_flat_of_isOpenImmersion :
    (Φ).map (ν) ≫ (effectiveNormalBundleThomIso k j hX' hZ').hom =
      (effectiveNormalBundleThomIso k i hX hZ).hom ≫ (L).map ((M).map g) := by
  let p := normalBundleProjection i hX hZ
  let p' := normalBundleProjection j hX' hZ'
  let τ := normalBundleThomClassAsPair k i hX hZ
  let τ' := normalBundleThomClassAsPair k j hX' hZ'
  let K := effectiveThomCoefficient k (n - m)
  have hc : (Φ).map (ν) ≫ τ' = τ :=
    normalBundleThomClass_baseChange k h hX hZ hX' hZ'
  have hp := smoothNormalFibreBaseChange_projection k h hX hZ hX' hZ'
  let d := K ◁ (M).map g
  let G := effectivePairThomGraph k p τ
  let G' := effectivePairThomGraph k p' τ'
  have hg : CommSq ((Φ).map (ν)) G G' d :=
    ⟨(effectivePairThomGraph_naturality_over k (ν) p p' g hp τ').trans
      (congrArg (fun t => effectivePairThomGraph k p t ≫ d) hc)⟩
  let e := effectiveLefschetzPowerTensorIso k ((M).obj Z) (n - m)
  let e' := effectiveLefschetzPowerTensorIso k ((M).obj Z') (n - m)
  have he : CommSq d e.hom e'.hom ((L).map ((M).map g)) :=
    ⟨effectiveLefschetzPowerTensorIso_naturality k ((M).map g) (n - m)⟩
  exact (hg.vert_comp he).w

set_option maxHeartbeats 1300000 in
-- Paste the two comparisons using the same original map of normal pairs.
/-- Flat base change with an open map of centres preserves the original purity
isomorphism of smooth closed pairs of matching pure dimensions. -/
theorem effectivePurity_naturality_of_flat_of_isOpenImmersion :
    effectiveMotiveWithSupportMap k h ≫ (effectivePurity k j hX' hZ').hom =
      (effectivePurity k i hX hZ).hom ≫ (L).map ((M).map g) := by
  let D := effectiveDeformationComparison k i hX hZ
  let D' := effectiveDeformationComparison k j hX' hZ'
  let T := effectiveNormalBundleThomIso k i hX hZ
  let T' := effectiveNormalBundleThomIso k j hX' hZ'
  have hD : CommSq (effectiveMotiveWithSupportMap k h) D.hom D'.hom ((Φ).map (ν)) :=
    ⟨effectiveDeformationComparison_naturality_of_flat k hX' hZ' hX hZ h⟩
  have hT : CommSq ((Φ).map (ν)) T.hom T'.hom ((L).map ((M).map g)) :=
    ⟨effectiveNormalBundleThomIso_naturality_of_flat_of_isOpenImmersion k h hX hZ hX' hZ'⟩
  exact (hD.vert_comp hT).w

end Flat

/-- Restriction to an ambient open intertwines purity with the original
iterated Lefschetz twist of the motive map of the restricted centre. -/
theorem effectivePurity_naturality_of_isOpenImmersion [IsOpenImmersion f.left] :
    effectiveMotiveWithSupportMap k h ≫ (effectivePurity k j hX' hZ').hom =
      (effectivePurity k i hX hZ).hom ≫ (L).map ((M).map g) := by
  let : IsOpenImmersion g.left := MorphismProperty.of_isPullback h inferInstance
  exact effectivePurity_naturality_of_flat_of_isOpenImmersion k h hX hZ hX' hZ'

end AlgebraicGeometry.MotivicHomotopy
