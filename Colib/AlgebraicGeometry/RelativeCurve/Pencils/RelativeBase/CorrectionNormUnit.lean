/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.BoundaryUnit
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionNormMarkComparison
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionNormInfinity
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionNormUnitDomain

/-!
# The norm quotient of the original correction sections

The correction is a unit on the original puncture and has value one
on the full infinity and marked boundaries.

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

/-- The actual correction pairs have a norm quotient on a common open
containing the prescribed full boundaries. -/
abbrev HasCorrectionNormUnit : Prop :=
    let hN := c₁.N_invertible
    let hT := c₂.T_invertible
    let hD : IsEffectiveCartierDivisor Δ₂ :=
      compactificationGraphIdeal_isEffectiveCartierDivisor π jA
    let hL : IsInvertibleModule (pullback (jA ≫ π) π) L₂ :=
      @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf _ (divisorSheaf Δ₂) c₂.T
        (@Stacks.Divisors.isInvertible_divisorSheaf _ Δ₂ hD) hT
    ∃ U : (pullback b π : Scheme.{u}).Opens,
      let u₁ : (pullback F U.ι : Scheme.{u}) ⟶ pullback b (f ≫ π) := pullback.fst F U.ι
      let u₂ : U.toScheme ⟶ pullback (jA ≫ π) π := U.ι ≫ τ
      let g : (pullback F U.ι : Scheme.{u}) ⟶ U.toScheme := pullback.snd F U.ι
      ∃ hG : IsFiniteLocallyFree g,
        @NormQuotientOfSectionPairs (pullback F U.ι) (pullback b π)
          (pullback b (f ≫ π)) (pullback (jA ≫ π) π)
          (pullback b (d₂ ≫ π)) (pullback b (zA ≫ π))
          U g hG u₁ u₂ c₁.N hN L₂ hL c₁.nS c₁.dS pole c₂.aS mI mZ

set_option maxHeartbeats 800000 in
-- The norm and section ratios use the same original pullback on each affine chart.
/-- The original correction norm quotient is a unit with value one on both
whole boundary schemes. The coefficient equality uses the native norm. -/
theorem exists_correctionNormUnit [hFinite : IsFiniteLocallyFree F] [IsClosedImmersion (z ≫ jA)]
    (bI : pullback f d₂ ⟶ D₁) (hbI : bI ≫ d₁ = pullback.fst f d₂)
    (bE : (residualMarkedFiberOpen f j zA s hmark).toScheme ⟶ D₁)
    (hbE : bE ≫ d₁ = residualMarkedFiberMap f j zA s hmark) :
    HasCorrectionNormUnit q π f j jA p hB hA a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂ := by
  let hN := c₁.N_invertible
  let hD : IsEffectiveCartierDivisor Δ₂ :=
    compactificationGraphIdeal_isEffectiveCartierDivisor π jA
  let hT := c₂.T_invertible
  let hL : IsInvertibleModule (pullback (jA ≫ π) π) L₂ :=
    @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf _ (divisorSheaf Δ₂) c₂.T
      (@Stacks.Divisors.isInvertible_divisorSheaf _ Δ₂ hD) hT
  obtain ⟨U, hI, hZ, hp, ha', hn, hd⟩ :=
    exists_correctionNormUnitDomain q π f j jA p hRet hB hA a z s hs H e d₁ hd₁ d₂ hd₂ ha
      c₁ c₂ bI hbI bE hbE
  let u₁ : (pullback F U.ι : Scheme.{u}) ⟶ pullback b (f ≫ π) := pullback.fst F U.ι
  let u₂ : U.toScheme ⟶ pullback (jA ≫ π) π := U.ι ≫ τ
  let g : (pullback F U.ι : Scheme.{u}) ⟶ U.toScheme := pullback.snd F U.ι
  let hG : IsFiniteLocallyFree g :=
    @isFiniteLocallyFree_pullback_snd (pullback b (f ≫ π)) U.toScheme (pullback b π)
      F U.ι hFinite
  let cN : Γ((pullback F U.ι : Scheme.{u}), ⊤) :=
    @sectionRatioCoefficientOnPullback _ _ u₁ c₁.N hN c₁.nS c₁.dS hn
  let cA : Γ(U.toScheme, ⊤) :=
    @sectionRatioCoefficientOnPullback _ _ u₂ L₂ hL pole c₂.aS hp
  have hunitN : IsUnit cN := @isUnit_sectionRatioCoefficientOnPullback _ _
    u₁ c₁.N hN c₁.nS c₁.dS hn hd
  have hunitA : IsUnit cA := @isUnit_sectionRatioCoefficientOnPullback _ _
    u₂ L₂ hL pole c₂.aS hp ha'
  have hscalarN {B : Scheme.{u}} (i : B ⟶ pullback F U.ι)
      (v : B ⟶ pullback (pullback.snd b (f ≫ π)) d₁ ⨿ pullback b (z ≫ q))
      (h : i ≫ u₁ = v ≫ iN) : i.appTop cN * v.appTop θN = 1 :=
    sectionRatioCoefficient_mul_boundary u₁ iN i v h c₁.N c₁.nS c₁.dS θN hn c₁.scalar
  have hscalarA {B : Scheme.{u}} (i : B ⟶ U.toScheme)
      (v : B ⟶ pullback (pullback.snd (jA ≫ π) π) d₂ ⨿ pullback (jA ≫ π) (z ≫ jA ≫ π))
      (h : i ≫ u₂ = v ≫ iA) : i.appTop cA * v.appTop θA = 1 :=
    sectionRatioCoefficient_mul_boundary u₂ iA i v h L₂ pole c₂.aS θA hp
      (correctionTargetPole_boundary_scalar q π jA hA a z e d₂ hd₂ ha c₂)
  have hquotient : NormQuotientOnBoundaries U g mI mZ cN cA := by
    apply exists_normQuotient_on_boundaries U g mI mZ hI hZ cN cA hunitN hunitA
    · intro l hl
      obtain ⟨v, hv, hθ⟩ := exists_correctionTargetInfinity_factor q π jA hA a z e d₂ hd₂ U l hl
      have htarget := hscalarA l v hv
      rw [hθ, mul_one] at htarget
      obtain ⟨vN, hvN, hθN⟩ := exists_correctionSourceInfinity_factor q π f j p hB a z s hs
        e d₁ d₂ ha U bI hbI l hl
      have hsource := hscalarN (normQuotientBoundaryMap F U mI l hl) vN hvN
      rw [hθN, mul_one] at hsource
      exact (normTop_appTop_eq_one_of_boundary F U mI l hl hFinite hG cN hsource).trans
        htarget.symm
    · intro l hl
      exact correctionNormCoefficient_on_mark q π f j jA p hRet hB hA a z s hs H e
        d₁ d₂ hd₂ ha U bE hbE hFinite hG l hl cN cA hscalarN hscalarA
  exact ⟨U, hG, hn, hd, hp, ha', hquotient⟩

end Correction

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

end
