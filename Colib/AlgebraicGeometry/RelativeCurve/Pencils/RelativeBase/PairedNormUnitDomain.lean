/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.UnitOpen
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ChartBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.PullbackGeneration
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.NormBoundaryCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormMark

/-!
# The common unit domain of the original two norm pairs

The source and target pairs generate over the same open containing both
whole target boundaries. At the mark the full inverse fiber is covered by
the actual marked and residual schemes.

Adapted from `SectionPairNormParameterNeighborhood.lean` under
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Norm` at
a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

private theorem exists_pairedSourceMarkedBoundary_cover
    {S X Y P C Z D : Scheme.{u}} (π : P ⟶ S) (f : C ⟶ P) [IsFinite f]
    (j : Y ⟶ C) (jA : X ⟶ P) [Mono jA]
    (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
    (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
    (d : D ⟶ C)
    (bE : (residualMarkedFiberOpen f j (z ≫ jA) s
      (markedSection_original_equation f j (z ≫ jA) s
        (pairedMark_isPullback f j jA p hRet z s H))).toScheme ⟶ D)
    (hbE : bE ≫ d = residualMarkedFiberMap f j (z ≫ jA) s
      (markedSection_original_equation f j (z ≫ jA) s
        (pairedMark_isPullback f j jA p hRet z s H))) :
    let b := j ≫ f ≫ π
    let F := graphProductMap π f j
    let mZ := retainedProductInclusion b π (z ≫ jA)
    let B := pullback (pullback.snd b (f ≫ π)) d ⨿ pullback b (s ≫ j ≫ f ≫ π)
    ∃ (K : Bool → Scheme.{u}) (l : ∀ i, K i ⟶ pullback F mZ) (v : ∀ i, K i ⟶ B),
      (∀ x : (pullback F mZ : Scheme.{u}), ∃ i, x ∈ Set.range (l i)) ∧
      ∀ i, l i ≫ pullback.fst F mZ = v i ≫ fullGraphBoundaryMap (f ≫ π) j s d := by
  dsimp only
  let b := j ≫ f ≫ π
  let F := graphProductMap π f j
  let zA := z ≫ jA
  let mZ := retainedProductInclusion b π zA
  let J := retainedProductInclusion b (f ≫ π) j
  let Hmark := pairedMark_isPullback f j jA p hRet z s H
  let s₀ := productMarkedSection b π f zA j s Hmark
  let H₀ := productMarkedSection_isPullback b π f zA j s Hmark
  let h₀ := markedSection_original_equation F J mZ s₀ H₀
  let t : pullback b (zA ≫ π) ⟶ pullback F mZ := markedFiberSection F J mZ s₀ h₀
  let R : (pullback F mZ : Scheme.{u}).Opens := residualMarkedFiberOpen F J mZ s₀ h₀
  let B := pullback (pullback.snd b (f ≫ π)) d ⨿ pullback b (s ≫ j ≫ f ≫ π)
  let iA := fullGraphBoundaryMap (f ≫ π) j s d
  let e := pairedMarkToSource π f j jA p hRet z s hs
  let vZ : pullback b (zA ≫ π) ⟶ B := e ≫ coprod.inr
  have hZ : t ≫ pullback.fst F mZ = vZ ≫ iA := by
    rw [show t ≫ pullback.fst F mZ = s₀ ≫ J from markedFiberSection_fst F J mZ s₀ h₀]
    simpa only [vZ, iA, e, Category.assoc, fullGraphBoundaryMap, coprod.inr_desc] using
      (pairedMarkToSource_markedProductMap π f j jA p hRet z s hs H).symm
  obtain ⟨vE, hvE⟩ := exists_productResidualBoundary_factor b π f j zA s Hmark d bE hbE
  let vR : R.toScheme ⟶ B := vE ≫ coprod.inl
  have hR : R.ι ≫ pullback.fst F mZ = vR ≫ iA := by
    calc
      _ = vE ≫ pullback.fst (pullback.snd b (f ≫ π)) d := hvE
      _ = _ := by simp only [vR, iA, Category.assoc, fullGraphBoundaryMap,
        coprod.inl_desc, infinityProductMap, b]
  let K : Bool → Scheme.{u} := Bool.rec R.toScheme (pullback b (zA ≫ π))
  let l : ∀ i, K i ⟶ pullback F mZ := Bool.rec R.ι t
  let v : ∀ i, K i ⟶ B := Bool.rec vR vZ
  refine ⟨K, l, v, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ Set.range t
    · exact ⟨true, hx⟩
    · refine ⟨false, ?_⟩
      change x ∈ Set.range R.ι
      rw [Opens.range_ι]
      exact hx
  · intro i
    cases i
    · exact hR
    · exact hZ

/-- The original whole marked fiber lies over the original normalized boundary,
as expressed by pulling back its unit ideals. -/
abbrev SourceMarkedBoundaryGeneration {S Y P C Z D : Scheme.{u}}
    (π : P ⟶ S) (f : C ⟶ P) (j : Y ⟶ C) (z : Z ⟶ P)
    (s : Z ⟶ Y) (d : D ⟶ C) : Prop :=
  ∀ I : (pullback (j ≫ f ≫ π) (f ≫ π) : Scheme.{u}).IdealSheafData,
    I.comap (fullGraphBoundaryMap (f ≫ π) j s d) = ⊤ →
      I.comap (pullback.fst (graphProductMap π f j)
        (retainedProductInclusion (j ≫ f ≫ π) π z)) = ⊤

/-- The full residual factor and the marked section supply the native marked
generation property. -/
theorem sourceMarkedBoundaryGeneration_of_residualFactor
    {S X Y P C Z D : Scheme.{u}} (π : P ⟶ S) (f : C ⟶ P) [IsFinite f]
    (j : Y ⟶ C) (jA : X ⟶ P) [Mono jA]
    (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
    (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
    (d : D ⟶ C)
    (bE : (residualMarkedFiberOpen f j (z ≫ jA) s
      (markedSection_original_equation f j (z ≫ jA) s
        (pairedMark_isPullback f j jA p hRet z s H))).toScheme ⟶ D)
    (hbE : bE ≫ d = residualMarkedFiberMap f j (z ≫ jA) s
      (markedSection_original_equation f j (z ≫ jA) s
        (pairedMark_isPullback f j jA p hRet z s H))) :
    SourceMarkedBoundaryGeneration π f j (z ≫ jA) s d := by
  intro I hI
  obtain ⟨K, l, v, hcover, hfactor⟩ :=
    exists_pairedSourceMarkedBoundary_cover π f j jA p hRet z s hs H d bE hbE
  apply IdealSheafData.eq_top_of_range_cover _ l hcover
  intro i
  rw [← IdealSheafData.comap_comp, hfactor, IdealSheafData.comap_comp, hI,
    IdealSheafData.comap_top]

attribute [local instance]
  compactificationGraphIdeal_isEffectiveCartierDivisor
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

local instance {U : Scheme.{u}} (L : U.Modules) [hL : IsInvertibleModule U L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible U.sheaf.obj U.ringCatSheaf.property L := hL

local instance {U : Scheme.{u}} (D : U.IdealSheafData) [IsEffectiveCartierDivisor D] :
    IsInvertibleModule U (divisorSheaf D) := Stacks.Divisors.isInvertible_divisorSheaf D

variable {S X Y P C A Z D₁ D₂ : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π] (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (a : A ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d₁ : D₁ ⟶ C) (hd₁ : Disjoint (Set.range j) (Set.range d₁))
  (d₂ : D₂ ⟶ P) (hd₂ : Disjoint (Set.range jA) (Set.range d₂))
  (ha : Disjoint (Set.range a) (Set.range z))
  (c₁ : SectionData q (f ≫ π) j p hB a z s hs H e d₁ hd₁ ha)
  (c₂ : SectionData q π jA (𝟙 X) hA a z z (Category.comp_id z) (IsPullback.of_id_snd)
    e d₂ hd₂ ha)

local notation "b" => (j ≫ f ≫ π)
local notation "zA" => (z ≫ jA)
local notation "F" => (graphProductMap π f j)
local notation "κ" => (graphTargetParameterMap π f j jA p hRet)
local notation "Δ₁" => (Hom.ker (compactificationGraph (f ≫ π) j))
local notation "Δ₂" => (Hom.ker (compactificationGraph π jA))
local notation "L₁" => (Stacks.Divisors.tensorModules (divisorSheaf Δ₁) (SectionData.T c₁))
local notation "L₂" => (Stacks.Divisors.tensorModules (divisorSheaf Δ₂) (SectionData.T c₂))
local notation "mI" => (retainedProductInclusion b π d₂)
local notation "mZ" => (retainedProductInclusion b π zA)

variable (bI : pullback f d₂ ⟶ D₁) (hbI : bI ≫ d₁ = pullback.fst f d₂)

set_option maxHeartbeats 800000 in
-- The two entire boundary pullbacks are compared through their original product maps.
include hbI in
/-- The actual common open of the four generators contains both whole
target boundary schemes. -/
theorem exists_pairedNormUnitDomain
    (hSrc : SourceMarkedBoundaryGeneration π f j zA s d₁) :
    letI := c₁.T_invertible
    letI := c₂.T_invertible
    ∃ U : (pullback b π : Scheme.{u}).Opens,
      Set.range mI ⊆ (U : Set (pullback b π : Scheme.{u})) ∧
      Set.range mZ ⊆ (U : Set (pullback b π : Scheme.{u})) ∧
      let w₁ := pullback.fst F U.ι
      let w₂ := U.ι ≫ κ
      graphNumeratorGeneratesOnPullback w₁ Δ₁ c₁.T c₁.aS ∧
      sectionGeneratesOnPullback w₁ c₁.T c₁.bS ∧
      graphNumeratorGeneratesOnPullback w₂ Δ₂ c₂.T c₂.aS ∧
      sectionGeneratesOnPullback w₂ c₂.T c₂.bS := by
  let := c₁.T_invertible
  let := c₂.T_invertible
  let I₁ := zeroScheme _ L₁ c₁.aS
  let I₂ := zeroScheme _ c₁.T c₁.bS
  let J₁ := zeroScheme _ L₂ c₂.aS
  let J₂ := zeroScheme _ c₂.T c₂.bS
  let U₁ := normUnitOpen F I₁ (J₁.comap κ)
  let U₂ := normUnitOpen F I₂ (J₂.comap κ)
  let U := U₁ ⊓ U₂
  have src {W : Scheme.{u}} (g : W ⟶ pullback b (f ≫ π))
      (v : W ⟶ pullback (pullback.snd b (f ≫ π)) d₁ ⨿ pullback b (s ≫ j ≫ f ≫ π))
      (h : v ≫ fullGraphBoundaryMap (f ≫ π) j s d₁ = g) :
      I₁.comap g = ⊤ ∧ I₂.comap g = ⊤ := by
    obtain ⟨h₁, h₂⟩ := SectionData.generators_on_boundary_factor q (f ≫ π) j p hB a z s hs H
      e d₁ hd₁ ha c₁ g v h
    exact ⟨(Stacks.Divisors.zeroScheme_pullback g L₁ c₁.aS).symm.trans h₁,
      (Stacks.Divisors.zeroScheme_pullback g c₁.T c₁.bS).symm.trans h₂⟩
  have tgt {W : Scheme.{u}} (g : W ⟶ pullback b π)
      (v : W ⟶ pullback (pullback.snd (jA ≫ π) π) d₂ ⨿ pullback (jA ≫ π) (z ≫ jA ≫ π))
      (h : v ≫ fullGraphBoundaryMap π jA z d₂ = g ≫ κ) :
      (J₁.comap κ).comap g = ⊤ ∧ (J₂.comap κ).comap g = ⊤ := by
    obtain ⟨h₁, h₂⟩ := SectionData.generators_on_boundary_factor q π jA (𝟙 X) hA a z z
      (Category.comp_id z) (IsPullback.of_id_snd) e d₂ hd₂ ha c₂ (g ≫ κ) v h
    rw [← IdealSheafData.comap_comp, ← IdealSheafData.comap_comp]
    exact ⟨(Stacks.Divisors.zeroScheme_pullback (g ≫ κ) L₂ c₂.aS).symm.trans h₁,
      (Stacks.Divisors.zeroScheme_pullback (g ≫ κ) c₂.T c₂.bS).symm.trans h₂⟩
  have hInfinity : Set.range mI ⊆ (U : Set (pullback b π : Scheme.{u})) := by
    obtain ⟨u, hu⟩ := exists_productInverseBoundary_factor b π f d₁ d₂ bI hbI
    obtain ⟨v, hv⟩ := exists_productTargetBoundary_factor b π (jA ≫ π) κ
      (graphTargetParameterMap_snd π f j jA p hRet) d₂
    obtain ⟨h₁, h₂⟩ := src (pullback.fst F mI) (u ≫ coprod.inl) (by
      simpa only [Category.assoc, fullGraphBoundaryMap, coprod.inl_desc, infinityProductMap]
        using hu.symm)
    obtain ⟨h₃, h₄⟩ := tgt mI (v ≫ coprod.inl) (by
      simpa only [Category.assoc, fullGraphBoundaryMap, coprod.inl_desc, infinityProductMap]
        using hv.symm)
    exact Set.subset_inter ((range_subset_normUnitOpen_iff F I₁ (J₁.comap κ) mI).2 ⟨h₃, h₁⟩)
      ((range_subset_normUnitOpen_iff F I₂ (J₂.comap κ) mI).2 ⟨h₄, h₂⟩)
  have hMarked : Set.range mZ ⊆ (U : Set (pullback b π : Scheme.{u})) := by
    let e₂ := pairedMarkToTarget q π f j jA p hB hA z
    obtain ⟨h₅, h₆⟩ := tgt mZ (e₂ ≫ coprod.inr) (by
      simpa only [Category.assoc, fullGraphBoundaryMap, coprod.inr_desc] using
        pairedMarkToTarget_markedProductMap q π f j jA p hRet hB hA z)
    have hSrc₁ := hSrc I₁ ((Stacks.Divisors.zeroScheme_pullback _ L₁ c₁.aS).symm.trans
      c₁.numerator_zero)
    have hSrc₂ := hSrc I₂ ((Stacks.Divisors.zeroScheme_pullback _ c₁.T c₁.bS).symm.trans
      c₁.denominator_zero)
    exact Set.subset_inter
      ((range_subset_normUnitOpen_iff F I₁ (J₁.comap κ) mZ).2 ⟨h₅, hSrc₁⟩)
      ((range_subset_normUnitOpen_iff F I₂ (J₂.comap κ) mZ).2 ⟨h₆, hSrc₂⟩)
  have hu₁ : Set.range U.ι ⊆ (U₁ : Set (pullback b π : Scheme.{u})) := by
    rw [Opens.range_ι]
    exact inf_le_left
  have hu₂ : Set.range U.ι ⊆ (U₂ : Set (pullback b π : Scheme.{u})) := by
    rw [Opens.range_ι]
    exact inf_le_right
  obtain ⟨h₃, h₁⟩ := (range_subset_normUnitOpen_iff F I₁ (J₁.comap κ) U.ι).1 hu₁
  obtain ⟨h₄, h₂⟩ := (range_subset_normUnitOpen_iff F I₂ (J₂.comap κ) U.ι).1 hu₂
  let w₁ := pullback.fst F U.ι
  let w₂ := U.ι ≫ κ
  refine ⟨U, hInfinity, hMarked,
    (Stacks.Divisors.zeroScheme_pullback w₁ L₁ c₁.aS).trans h₁,
    (Stacks.Divisors.zeroScheme_pullback w₁ c₁.T c₁.bS).trans h₂, ?_, ?_⟩
  · exact (Stacks.Divisors.zeroScheme_pullback w₂ L₂ c₂.aS).trans
      ((IdealSheafData.comap_comp _ _ _).trans h₃)
  · exact (Stacks.Divisors.zeroScheme_pullback w₂ c₂.T c₂.bS).trans
      ((IdealSheafData.comap_comp _ _ _).trans h₄)

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
