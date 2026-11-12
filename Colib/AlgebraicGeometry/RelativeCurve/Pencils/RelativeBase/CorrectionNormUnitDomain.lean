/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionUnitRatio
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionMarkedCover
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.NormBoundaryCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedMarkedSquare

/-!
# The common generator open for the correction norm

The original source and target sections generate on an open containing
the full marked and infinity boundaries.

Adapted from `Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Correction/NormalizedUnit.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

local instance {X : Scheme.{u}} (L : X.Modules) [hL : IsInvertibleModule X L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL

section Correction

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

local instance {U : Scheme.{u}} (D : U.IdealSheafData) [IsEffectiveCartierDivisor D] :
    IsInvertibleModule U (divisorSheaf D) := Stacks.Divisors.isInvertible_divisorSheaf D

variable {S X Y P C A Z D₁ D₂ : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π]
  (f : C ⟶ P) [IsFinite f]
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

local notation "b" => (a ≫ q)
local notation "zA" => (z ≫ jA)
local notation "hA₀" => (hA.trans (Category.id_comp q))
local notation "Hmark" => (pairedMark_isPullback f j jA p hRet z s H)
local notation "hmark" => (markedSection_original_equation f j zA s Hmark)
local notation "F" => (retainedProductInclusion b π f)
local notation "τ" => (correctionTargetParameterMap q π jA hA₀ a)
local notation "iN" => (psiBoundaryInclusion q (f ≫ π) j p hB a z s hs d₁)
local notation "iA" => (fullGraphBoundaryMap π jA z d₂)
local notation "θA" => (fullGraphCoordinate q π jA (𝟙 X) hA z z (Category.comp_id z)
  IsPullback.of_id_snd e d₂ hd₂)
local notation "θN" => (fullCorrectionCoordinate q (f ≫ π) z e d₁ a ha)
local notation "Δ₂" => (Hom.ker (compactificationGraph π jA))
local notation "L₂" => (tensorModules (divisorSheaf Δ₂) (SectionData.T c₂))
set_option quotPrecheck false in
local notation "pole" => (tensorSection (divisorSheaf Δ₂) (SectionData.T c₂) ⊤
  (divisorSheafGlobalSection Δ₂) c₂.bS)
local notation "mI" => (retainedProductInclusion b π d₂)
local notation "mZ" => (retainedProductInclusion b π zA)

variable (bI : pullback f d₂ ⟶ D₁) (hbI : bI ≫ d₁ = pullback.fst f d₂)

private theorem correctionGenerators_comap_factor {D : Scheme.{u}}
    (g : D ⟶ pullback b (f ≫ π))
    (v : D ⟶ pullback (pullback.snd b (f ≫ π)) d₁ ⨿ pullback b (z ≫ q))
    (h : v ≫ iN = g) :
    letI := c₁.N_invertible
    (zeroScheme _ c₁.N c₁.nS).comap g = ⊤ ∧ (zeroScheme _ c₁.N c₁.dS).comap g = ⊤ := by
  let := c₁.N_invertible
  exact ⟨(zeroScheme_pullback g c₁.N c₁.nS).symm.trans
      (zeroScheme_pullback_eq_top_of_factor iN g v h c₁.N c₁.nS c₁.correctionNumerator_zero),
    (zeroScheme_pullback g c₁.N c₁.dS).symm.trans
      (zeroScheme_pullback_eq_top_of_factor iN g v h c₁.N c₁.dS c₁.correctionDenominator_zero)⟩

include hbI in
private theorem correctionGenerators_on_inverse_infinity :
    letI := c₁.N_invertible
    (zeroScheme _ c₁.N c₁.nS).comap (pullback.fst F mI) = ⊤ ∧
      (zeroScheme _ c₁.N c₁.dS).comap (pullback.fst F mI) = ⊤ := by
  let := c₁.N_invertible
  obtain ⟨v, hv⟩ := exists_productInverseBoundary_factor b π f d₁ d₂ bI hbI
  exact correctionGenerators_comap_factor q π f j p hB a z s hs H e d₁ hd₁ ha c₁
    (pullback.fst F mI) (v ≫ coprod.inl) (by
      simpa only [Category.assoc, psiBoundaryInclusion, coprod.inl_desc] using hv.symm)

private theorem correctionTargetGenerators_on_infinity :
    letI := c₂.T_invertible
    (zeroScheme _ L₂ c₂.aS).comap (mI ≫ τ) = ⊤ ∧
      (zeroScheme _ L₂ pole).comap (mI ≫ τ) = ⊤ := by
  let := c₂.T_invertible
  let g := mI ≫ τ
  obtain ⟨v, hv⟩ := exists_productTargetBoundary_factor b π (jA ≫ π) τ
    (correctionTargetParameterMap_snd q π jA hA₀ a) d₂
  obtain ⟨hgen, _⟩ := SectionData.generators_on_boundary_factor q π jA (𝟙 X) hA a z z
    (Category.comp_id z) IsPullback.of_id_snd e d₂ hd₂ ha c₂ g (v ≫ coprod.inl) (by
      simpa only [g, Category.assoc, fullGraphBoundaryMap, coprod.inl_desc, infinityProductMap]
        using hv.symm)
  have hcoef := SectionData.graphSectionRatioCoefficient_on_infinity q π jA (𝟙 X) hA a z z
    (Category.comp_id z) IsPullback.of_id_snd e d₂ hd₂ ha c₂ g (𝟙 _) v
      (by simpa only [Category.id_comp, g, infinityProductMap] using hv) hgen
  have hu : IsUnit (graphSectionRatioCoefficient g Δ₂ c₂.T c₂.aS c₂.bS hgen) := by
    have h : graphSectionRatioCoefficient g Δ₂ c₂.T c₂.aS c₂.bS hgen = 1 := by
      simpa only [Hom.id_appTop, CommRingCat.id_apply] using hcoef
    rw [h]
    exact isUnit_one
  exact ⟨(zeroScheme_pullback g L₂ c₂.aS).symm.trans hgen,
    (zeroScheme_pullback g L₂ pole).symm.trans
      (zeroScheme_top_of_unit_sectionRatioCoefficient _ _ _ hgen hu)⟩

private theorem correctionTargetGenerators_on_mark :
    letI := c₂.T_invertible
    (zeroScheme _ L₂ c₂.aS).comap (mZ ≫ τ) = ⊤ ∧
      (zeroScheme _ L₂ pole).comap (mZ ≫ τ) = ⊤ := by
  let := c₂.T_invertible
  let g := mZ ≫ τ
  let v := correctionMarkToTargetProduct q π jA hA₀ a z
  let v' := markedProductToTarget q π jA (𝟙 X) hA z z (Category.comp_id z)
  let m := correctionMarkBaseIso q π jA hA₀ a z
  have hv : v ≫ markedProductMap π jA z = g :=
    correctionMarkToTargetProduct_map q π jA hA₀ a z
  have hmap : v ≫ v' = m.hom ≫ correctionProductToTarget q z a :=
    correctionMarkToTargetProduct_coordinate q π jA hA₀ a z
  obtain ⟨hgen, _⟩ := SectionData.generators_on_boundary_factor q π jA (𝟙 X) hA a z z
    (Category.comp_id z) IsPullback.of_id_snd e d₂ hd₂ ha c₂ g (v ≫ coprod.inr) (by
      simpa only [Category.assoc, fullGraphBoundaryMap, coprod.inr_desc] using hv)
  have hcoef := SectionData.graphSectionRatioCoefficient_on_mark q π jA (𝟙 X) hA a z z
    (Category.comp_id z) IsPullback.of_id_snd e d₂ hd₂ ha c₂ g (𝟙 _) v
      (by simpa only [Category.id_comp] using hv.symm) hgen
  have heq : graphSectionRatioCoefficient g Δ₂ c₂.T c₂.aS c₂.bS hgen =
      m.hom.appTop (correctionCoordinate q z e a) := by
    have he : graphSectionRatioCoefficient g Δ₂ c₂.T c₂.aS c₂.bS hgen =
        (v ≫ v').appTop (targetCoordinate q z e) := by
      simpa only [Hom.id_appTop, CommRingCat.id_apply] using hcoef
    rw [he, hmap, Hom.comp_appTop, CommRingCat.comp_apply]
    rfl
  have hu : IsUnit (correctionCoordinate q z e a) := by
    rw [← correctionUnit_coordinate q z e a ha]
    exact isUnit_structureModuleIso_coordinate (correctionUnit q z e a ha)
  have hunit : IsUnit (graphSectionRatioCoefficient g Δ₂ c₂.T c₂.aS c₂.bS hgen) := by
    rw [heq]
    exact hu.map m.hom.appTop.hom
  rw [← zeroScheme_pullback g L₂ c₂.aS, ← zeroScheme_pullback g L₂ pole]
  exact ⟨hgen, zeroScheme_top_of_unit_sectionRatioCoefficient _ _ _ hgen hunit⟩

/-- The graph pole and numerator have the normalized scalar on the full boundary. -/
theorem correctionTargetPole_boundary_scalar :
    letI := c₂.T_invertible
    pullbackGlobalSections iA L₂ pole = θA • pullbackGlobalSections iA L₂ c₂.aS := by
  let := c₂.T_invertible
  exact graphPole_boundary_eq_coordinate_smul iA (divisorSheaf Δ₂) c₂.T
    (fullGraphFrame q π jA (𝟙 X) hA z z (Category.comp_id z) IsPullback.of_id_snd e d₂ hd₂)
    (divisorSheafGlobalSection Δ₂) c₂.aS c₂.bS c₂.normalized

/-- The original correction and target sections generate on a common open
containing both entire boundary schemes. -/
theorem exists_correctionNormUnitDomain
    (bI : pullback f d₂ ⟶ D₁) (hbI : bI ≫ d₁ = pullback.fst f d₂)
    (bE : (residualMarkedFiberOpen f j zA s hmark).toScheme ⟶ D₁)
    (hbE : bE ≫ d₁ = residualMarkedFiberMap f j zA s hmark) :
    letI := c₁.N_invertible
    letI := c₂.T_invertible
    ∃ U : (pullback b π : Scheme.{u}).Opens,
      Set.range mI ⊆ (U : Set (pullback b π : Scheme.{u})) ∧
      Set.range mZ ⊆ (U : Set (pullback b π : Scheme.{u})) ∧
      let u₁ := pullback.fst F U.ι
      let u₂ := U.ι ≫ τ
      zeroScheme _ ((Modules.pullback u₂).obj L₂) (pullbackGlobalSections u₂ L₂ pole) = ⊤ ∧
        zeroScheme _ ((Modules.pullback u₂).obj L₂) (pullbackGlobalSections u₂ L₂ c₂.aS) = ⊤ ∧
          zeroScheme _ ((Modules.pullback u₁).obj c₁.N)
            (pullbackGlobalSections u₁ c₁.N c₁.nS) = ⊤ ∧
            zeroScheme _ ((Modules.pullback u₁).obj c₁.N)
              (pullbackGlobalSections u₁ c₁.N c₁.dS) = ⊤ := by
  let := c₁.N_invertible
  let := c₂.T_invertible
  obtain ⟨haI, hpI⟩ := correctionTargetGenerators_on_infinity q π jA hA a z e d₂ hd₂ ha c₂
  obtain ⟨haZ, hpZ⟩ := correctionTargetGenerators_on_mark q π jA hA a z e d₂ hd₂ ha c₂
  have hI :=
    correctionGenerators_on_inverse_infinity q π f j p hB a z s hs H e d₁ hd₁ d₂ ha c₁ bI hbI
  have hn : (zeroScheme _ c₁.N c₁.nS).comap iN = ⊤ :=
    (zeroScheme_pullback iN c₁.N c₁.nS).symm.trans c₁.correctionNumerator_zero
  have hd : (zeroScheme _ c₁.N c₁.dS).comap iN = ⊤ :=
    (zeroScheme_pullback iN c₁.N c₁.dS).symm.trans c₁.correctionDenominator_zero
  exact exists_normQuotient_generator_open F c₁.N τ L₂ c₁.nS c₁.dS pole c₂.aS mI mZ
    ⟨hpI, haI, hI⟩
    ⟨hpZ, haZ, comap_eq_top_on_correctionMarkedBoundary q π jA hA₀ a f j p hB z s hs Hmark
      d₁ bE hbE _ hn, comap_eq_top_on_correctionMarkedBoundary q π jA hA₀ a f j p hB z s hs Hmark
      d₁ bE hbE _ hd⟩

end Correction

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

end
