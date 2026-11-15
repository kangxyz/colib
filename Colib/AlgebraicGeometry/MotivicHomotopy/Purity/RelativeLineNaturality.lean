/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineThom
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.LaurentNaturality

/-! # Naturality of the original relative line Thom comparison -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable (k : Type u) [Field k]

local instance instNoetherianRelativeLineNaturality :
    IsNoetherian (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
  inferInstanceAs (IsNoetherian (Spec (CommRingCat.of k)))

set_option maxHeartbeats 900000 in
-- Type the affine chart morphism using the underlying maps before taking motives.
private def appendZeroAffinePairMap
    {Z Y Z' Y' : SmoothSite (Spec (CommRingCat.of k))}
    (z : Z ⟶ Y) {z' : Z' ⟶ Y'} [IsClosedImmersion z.left] [IsClosedImmersion z'.left]
    {a : Z ⟶ Z'} {b : Y ⟶ Y'} (h : IsPullback z.left a.left b.left z'.left) :=
  let R := CommRingCat.of k
  let u := closedPairOpenMap (f := b) (g := a.left) h
  let h' := appendZeroSection_isPullback R z (z' := z') (a := a) (b := b) h
  let v := closedPairOpenMap (f := affineLineCylinder.map b) (g := a.left) h'
  let hc := appendZeroAffineOpen_naturality R z (z' := z') (a := a) (b := b) h
  Arrow.homMk' (f := appendZeroAffineOpen R z) (g := appendZeroAffineOpen R z')
    (affineLineCylinder.map u) v hc.symm

set_option maxHeartbeats 900000 in
-- Apply the literal Laurent cylinder to the original open-complement morphism.
private def appendZeroLaurentPairMap
    {Z Y Z' Y' : SmoothSite (Spec (CommRingCat.of k))}
    (z : Z ⟶ Y) {z' : Z' ⟶ Y'} [IsClosedImmersion z.left] [IsClosedImmersion z'.left]
    {a : Z ⟶ Z'} {b : Y ⟶ Y'} (h : IsPullback z.left a.left b.left z'.left) :=
  (laurentPair k).map (closedSupportArrowMap (i := z) (j := z') (f := b) (g := a) h)

private theorem boundary_comp_shift_naturality
    {C : Type*} [Category* C] (H : C ⥤ C) {X X' A A' B B' : C}
    (f : X ⟶ X') (u : A ⟶ A') (v : B ⟶ B')
    (δ : X ⟶ H.obj A) (δ' : X' ⟶ H.obj A')
    (q : A ⟶ B) (q' : A' ⟶ B')
    (hδ : f ≫ δ' = δ ≫ H.map u) (hq : u ≫ q' = q ≫ v) :
    f ≫ (δ' ≫ H.map q') = (δ ≫ H.map q) ≫ H.map v := by
  rw [← Category.assoc, hδ, Category.assoc, ← H.map_comp, hq, H.map_comp, Category.assoc]

set_option maxHeartbeats 900000 in
-- Use the same native affine and Laurent charts for each marked zero coordinate.
private def appendZeroLaurentChartArrow
    {Z Y : SmoothSite (Spec (CommRingCat.of k))} (z : Z ⟶ Y) [IsClosedImmersion z.left] :=
  let R := CommRingCat.of k
  let j := closedPairOpenInclusion z.left
  let i := appendZeroAffineOpen R z
  let l := appendZeroLaurentOpen R z
  let v := closedPairOpenInclusion (appendZeroSection R z).left
  relativeLineLaurentArrow k j i l v
    (appendZeroAffineOpen_comp R z) (appendZeroLaurentOpen_comp R z)

set_option maxHeartbeats 1100000 in
-- The components are the native inclusions of the affine and Laurent charts.
private theorem appendZeroLaurentComparison_square
    {Z Y Z' Y' : SmoothSite (Spec (CommRingCat.of k))}
    (z : Z ⟶ Y) {z' : Z' ⟶ Y'} [IsClosedImmersion z.left] [IsClosedImmersion z'.left]
    {a : Z ⟶ Z'} {b : Y ⟶ Y'} (h : IsPullback z.left a.left b.left z'.left) :
    appendZeroLaurentChartArrow k z ≫
        appendZeroAffinePairMap k z (z' := z') (a := a) (b := b) h =
      appendZeroLaurentPairMap k z (z' := z') (a := a) (b := b) h ≫
        appendZeroLaurentChartArrow k z' := by
  apply Arrow.hom_ext
  · exact (SmoothSite.Contraction.openInclusion.naturality
      (closedPairOpenMap (f := b) (g := a.left) h)).symm
  · exact appendZeroLaurentOpen_naturality (.of k) z (z' := z') (a := a) (b := b) h

private theorem map_chart_comparison_inv
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A A' B B' : C} (l : A ⟶ B) (l' : A' ⟶ B') (u : A ⟶ A') (v : B ⟶ B')
    (e : F.obj A ≅ F.obj B) (e' : F.obj A' ≅ F.obj B')
    (he : e.hom = F.map l) (he' : e'.hom = F.map l') (h : l ≫ v = u ≫ l')
    (m : F.obj B ⟶ F.obj B') (t : F.obj A ⟶ F.obj A')
    (hm : m = F.map v) (ht : t = F.map u) : m ≫ e'.inv = e.inv ≫ t := by
  rw [hm, ht]
  have hc : e.hom ≫ F.map v = F.map u ≫ e'.hom := by
    rw [he, he', ← F.map_comp l v, ← F.map_comp u l', h]
  apply e.eq_inv_comp.2
  rw [← Category.assoc, hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The canonical abelian structure on sheaves with transfers. -/
local instance instAbelianRelativeLineNaturality : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

set_option maxHeartbeats 950000 in
-- The relative comparison uses the original pullback and open covering of the marked section.
private def appendZeroLaurentChartData
    {Z Y : SmoothSite (Spec (CommRingCat.of k))} (z : Z ⟶ Y) [IsClosedImmersion z.left] :=
  let R := CommRingCat.of k
  let j := closedPairOpenInclusion z.left
  let i := appendZeroAffineOpen R z
  let l := appendZeroLaurentOpen R z
  let v := closedPairOpenInclusion (appendZeroSection R z).left
  relativeLineLaurentComparisonData k j i l v
    (appendZeroAffineOpen_comp R z) (appendZeroLaurentOpen_comp R z)
    (appendZeroOpen_isPullback R z) (appendZeroOpen_range_cover R z)

private abbrev appendZeroPairMotiveFunctor :=
  ((smoothTransferRepresentable k).mapArrow ⋙ coker (LargeSheaves k)) ⋙ effectiveTransferSheaf k

set_option maxHeartbeats 1500000 in
-- Apply the original pair functor to the actual chart square before inverting excision.
private theorem appendZeroLaurentChartMap
    {Z Y Z' Y' : SmoothSite (Spec (CommRingCat.of k))}
    (z : Z ⟶ Y) {z' : Z' ⟶ Y'} [IsClosedImmersion z.left] [IsClosedImmersion z'.left]
    {a : Z ⟶ Z'} {b : Y ⟶ Y'} (h : IsPullback z.left a.left b.left z'.left)
    (m : effectivePairMotive k (appendZeroAffineOpen (.of k) z) ⟶
      effectivePairMotive k (appendZeroAffineOpen (.of k) z'))
    (t : effectivePairMotive k (torusCylinder.map (closedPairOpenInclusion z.left)) ⟶
      effectivePairMotive k (torusCylinder.map (closedPairOpenInclusion z'.left)))
    (hm : m = (appendZeroPairMotiveFunctor k).map (appendZeroAffinePairMap k z h))
    (ht : t = (appendZeroPairMotiveFunctor k).map (appendZeroLaurentPairMap k z h)) :
    m ≫ (appendZeroLaurentChartData k z').val.inv =
      (appendZeroLaurentChartData k z).val.inv ≫ t := by
  let Q := appendZeroPairMotiveFunctor k
  let l₀ := appendZeroLaurentChartArrow k z
  let l₁ := appendZeroLaurentChartArrow k z'
  let m' := appendZeroAffinePairMap k z (z' := z') (a := a) (b := b) h
  let t' := appendZeroLaurentPairMap k z (z' := z') (a := a) (b := b) h
  let e₀ := appendZeroLaurentChartData k z
  let e₁ := appendZeroLaurentChartData k z'
  let hs := appendZeroLaurentComparison_square k z (z' := z') (a := a) (b := b) h
  let j₀ := closedPairOpenInclusion z.left
  let j₁ := closedPairOpenInclusion z'.left
  exact map_chart_comparison_inv Q
    (A := Arrow.mk (torusCylinder.map j₀)) (A' := Arrow.mk (torusCylinder.map j₁))
    (B := Arrow.mk (appendZeroAffineOpen (.of k) z))
    (B' := Arrow.mk (appendZeroAffineOpen (.of k) z'))
    l₀ l₁ t' m' e₀.val e₁.val e₀.property e₁.property hs m t hm ht

variable [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

set_option maxHeartbeats 1600000 in
-- Compose the two comparison equations before applying the original shift.
/-- Naturality of adjoining one marked zero coordinate, on the original support maps. -/
theorem effectiveAppendZeroSectionThomIso_naturality
    {Z Y Z' Y' : SmoothSite (Spec (CommRingCat.of k))}
    (z : Z ⟶ Y) {z' : Z' ⟶ Y'} [IsClosedImmersion z.left] [IsClosedImmersion z'.left]
    {a : Z ⟶ Z'} {b : Y ⟶ Y'} (h : IsPullback z.left a.left b.left z'.left) :
    let za := appendZeroSection (.of k) z
    let za' := appendZeroSection (.of k) z'
    let hz := appendZeroSection_isPullback (.of k) z (z' := z') (a := a) (b := b) h
    let f := effectiveMotiveWithSupportMap k (i := za) (j := za')
      (f := affineLineCylinder.map b) (g := a) hz
    let g := effectiveMotiveWithSupportMap k (i := z) (j := z') (f := b) (g := a) h
    f ≫ (effectiveAppendZeroSectionThomIso k z').hom =
      (effectiveAppendZeroSectionThomIso k z).hom ≫ (effectiveLefschetzTwistFunctor k).map g := by
  intro za za' hz f g
  let R := CommRingCat.of k
  let j₀ := closedPairOpenInclusion z.left
  let j₁ := closedPairOpenInclusion z'.left
  let a₀ := appendZeroAffineOpen R z
  let a₁ := appendZeroAffineOpen R z'
  let v₀ := closedPairOpenInclusion (appendZeroSection R z).left
  let v₁ := closedPairOpenInclusion (appendZeroSection R z').left
  let m := appendZeroAffinePairMap k z (z' := z') (a := a) (b := b) h
  let t := appendZeroLaurentPairMap k z (z' := z') (a := a) (b := b) h
  let q₀ := (effectiveRelativeLaurentRetract k j₀).r
  let q₁ := (effectiveRelativeLaurentRetract k j₁).r
  let e₀ := (appendZeroLaurentChartData k z).val
  let e₁ := (appendZeroLaurentChartData k z').val
  let Q := appendZeroPairMotiveFunctor k
  have h₁ := appendZeroLaurentChartMap k z (z' := z') (a := a) (b := b) h
    (Q.map m) (Q.map t) rfl rfl
  have h₂ := effectiveRelativeLaurentRetract_naturality k j₀ j₁
    (closedSupportArrowMap (i := z) (j := z') (f := b) (g := a) h)
  let u := closedPairOpenMap (f := b) (g := a.left) h
  let v := closedPairOpenMap (f := affineLineCylinder.map b) (g := a.left) hz
  have hn := effectiveNestedPairBoundary_naturality k a₀ v₀ a₁ v₁
    (affineLineCylinder.map u) v (affineLineCylinder.map b)
    (appendZeroAffineOpen_naturality R z (z' := z') (a := a) (b := b) h)
    (closedPairOpenMap_comm (f := affineLineCylinder.map b) (g := a.left) hz).symm
  let H := shiftFunctor (EffectiveMotivesMinus k) (1 : ℤ)
  let δ₀ := effectiveNestedPairBoundary k a₀ v₀
  let δ₁ := effectiveNestedPairBoundary k a₁ v₁
  let g' := (effectiveReducedTorusTensorFunctor k).map g
  have hh : f ≫ δ₁ = δ₀ ≫ H.map (Q.map m) := hn
  have hq : Q.map m ≫ (e₁.inv ≫ q₁) = (e₀.inv ≫ q₀) ≫ g' := by
    calc
      _ = (Q.map m ≫ e₁.inv) ≫ q₁ := (Category.assoc _ _ _).symm
      _ = (e₀.inv ≫ Q.map t) ≫ q₁ := congrArg (· ≫ q₁) h₁
      _ = e₀.inv ≫ q₀ ≫ g' := (Category.assoc _ _ _).trans (congrArg (e₀.inv ≫ ·) h₂)
      _ = _ := (Category.assoc _ _ _).symm
  have hs₀ : (effectiveAppendZeroSectionThomIso k z).hom = δ₀ ≫ H.map (e₀.inv ≫ q₀) :=
    relativeLineThomIso_hom k j₀ a₀ (appendZeroLaurentOpen R z) v₀
      (appendZeroAffineOpen_comp R z) (appendZeroLaurentOpen_comp R z)
      (appendZeroOpen_isPullback R z) (appendZeroOpen_range_cover R z)
  have hs₁ : (effectiveAppendZeroSectionThomIso k z').hom = δ₁ ≫ H.map (e₁.inv ≫ q₁) :=
    relativeLineThomIso_hom k j₁ a₁ (appendZeroLaurentOpen R z') v₁
      (appendZeroAffineOpen_comp R z') (appendZeroLaurentOpen_comp R z')
      (appendZeroOpen_isPullback R z') (appendZeroOpen_range_cover R z')
  change f ≫ (effectiveAppendZeroSectionThomIso k z').hom =
    (effectiveAppendZeroSectionThomIso k z).hom ≫ H.map g'
  have hc := boundary_comp_shift_naturality H f (Q.map m) g' δ₀ δ₁
    (e₀.inv ≫ q₀) (e₁.inv ≫ q₁) hh hq
  exact (congrArg (f ≫ ·) hs₁).trans (hc.trans (congrArg (· ≫ H.map g') hs₀.symm))

end AlgebraicGeometry.MotivicHomotopy
