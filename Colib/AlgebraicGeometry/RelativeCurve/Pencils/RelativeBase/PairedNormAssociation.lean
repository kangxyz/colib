/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Marked.NormAssociation
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ChartBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.GraphAssociation
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.PullbackGeneration
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.NormBoundaryCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormChartMark

/-!
# Normalization of the paired graph norm on its actual chart

The two exact graph coefficients determine one association unit. It takes
value one on the full infinity and marked schemes, using the original
residual and inverse-infinity maps into the source boundary.

Adapted from `SectionPairNormParameterNeighborhood.lean` under
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Norm` at
a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option cleanup.letToHave false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

attribute [local instance]
  compactificationGraphIdeal_isEffectiveCartierDivisor
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

local instance {U : Scheme.{u}} (L : U.Modules) [hL : IsInvertibleModule U L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible U.sheaf.obj U.ringCatSheaf.property L := hL

local instance {U : Scheme.{u}} (D : U.IdealSheafData) [IsEffectiveCartierDivisor D] :
    IsInvertibleModule U (divisorSheaf D) := Stacks.Divisors.isInvertible_divisorSheaf D

variable {S X Y P C A Z D₁ D₂ W : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π] [SmoothOfRelativeDimension 1 π] (f : C ⟶ P) [IsFinite f]
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
local notation "Hmark" => (pairedMark_isPullback f j jA p hRet z s H)
local notation "F" => (graphProductMap π f j)
local notation "κ" => (graphTargetParameterMap π f j jA p hRet)
local notation "Δ₁" => (Hom.ker (compactificationGraph (f ≫ π) j))
local notation "Δ₂" => (Hom.ker (compactificationGraph π jA))
variable (w : W ⟶ pullback (j ≫ f ≫ π) π) [IsOpenImmersion w] [IsAffine W]
  [IsClosedImmersion d₂] [IsClosedImmersion (z ≫ jA)]
  (bI : pullback f d₂ ⟶ D₁) (hbI : bI ≫ d₁ = pullback.fst f d₂)
  (hResidual : PairedNormChartResidualFactor π f j jA p hRet z s H w d₁)

local notation "w₁" => (pullback.fst F w)
local notation "w₂" => (w ≫ κ)
local notation "pW" => (pullback.snd F w)
local notation "mI" => (retainedProductInclusion b π d₂)
local notation "mZ" => (retainedProductInclusion b π zA)
local notation "iI" => (pullback.snd mI w)
local notation "iZ" => (pullback.snd mZ w)

/-- A determinant association unit with value one on two specified
boundary maps. -/
abbrev NormAssociationOnBoundaries {X W B₁ B₂ : Scheme.{u}} (g : X ⟶ W)
    (i₁ : B₁ ⟶ W) (i₂ : B₂ ⟶ W) (cB : Γ(X, ⊤)) (cA : Γ(W, ⊤)) : Prop :=
  let : Algebra Γ(W, ⊤) Γ(X, ⊤) := g.appTop.hom.toAlgebra
  ∃ μ : Γ(W, ⊤)ˣ, Algebra.norm Γ(W, ⊤) cB = (μ : Γ(W, ⊤)) * cA ∧
    i₁.appTop (μ : Γ(W, ⊤)) = 1 ∧ i₂.appTop (μ : Γ(W, ⊤)) = 1

include w hbI hResidual

set_option maxHeartbeats 1200000 in
-- The chart comparison transports both whole marked and inverse-infinity fibers.
/-- The norm association of the same original pairs is one on both full
boundaries of this chart. -/
theorem exists_pairedNormAssociationUnit_on_chart
    (ha₁ : @graphNumeratorGeneratesOnPullback (pullback F w) (pullback b (f ≫ π)) w₁
      Δ₁ (compactificationGraphIdeal_isEffectiveCartierDivisor (f ≫ π) j)
      c₁.T c₁.T_invertible c₁.aS)
    (ha₂ : @graphNumeratorGeneratesOnPullback W (pullback (jA ≫ π) π) w₂
      Δ₂ (compactificationGraphIdeal_isEffectiveCartierDivisor π jA)
      c₂.T c₂.T_invertible c₂.aS)
    (cB : Γ((pullback F w : Scheme.{u}), ⊤)) (cA : Γ(W, ⊤)) :
    @sectionGeneratesOnPullback (pullback F w) (pullback b (f ≫ π)) w₁
      c₁.T c₁.T_invertible c₁.bS →
    @sectionGeneratesOnPullback W (pullback (jA ≫ π) π) w₂ c₂.T c₂.T_invertible c₂.bS →
    cB = @graphSectionRatioCoefficientOfGenerating (pullback F w) (pullback b (f ≫ π))
      w₁ Δ₁ (compactificationGraphIdeal_isEffectiveCartierDivisor (f ≫ π) j)
      c₁.T c₁.T_invertible c₁.aS c₁.bS ha₁ →
    cA = @graphSectionRatioCoefficientOfGenerating W (pullback (jA ≫ π) π)
      w₂ Δ₂ (compactificationGraphIdeal_isEffectiveCartierDivisor π jA)
      c₂.T c₂.T_invertible c₂.aS c₂.bS ha₂ →
    (letI : Algebra Γ(W, ⊤) Γ((pullback F w : Scheme.{u}), ⊤) := (pW).appTop.hom.toAlgebra;
      Module.Free Γ(W, ⊤) Γ((pullback F w : Scheme.{u}), ⊤)) →
    @NormAssociationOnBoundaries (pullback F w) W (pullback mI w) (pullback mZ w)
      (pullback.snd F w) (pullback.snd mI w) (pullback.snd mZ w) cB cA := by
  intro hb₁ hb₂ hcB hcA hfree
  subst cB
  subst cA
  let := c₁.T_invertible
  let := c₂.T_invertible
  let : Algebra Γ(W, ⊤) Γ((pullback F w : Scheme.{u}), ⊤) := (pW).appTop.hom.toAlgebra
  let : Module.Free Γ(W, ⊤) Γ((pullback F w : Scheme.{u}), ⊤) := hfree
  let b₀ := graphSectionRatioCoefficientOfGenerating w₁ Δ₁ c₁.T c₁.aS c₁.bS ha₁
  let a₀ := graphSectionRatioCoefficientOfGenerating w₂ Δ₂ c₂.T c₂.aS c₂.bS ha₂
  obtain ⟨μ, hμ⟩ := exists_graphSectionRatio_norm_associated π f j jA p hRet w
    c₁.T c₂.T c₁.aS c₁.bS c₂.aS c₂.bS ha₁ hb₁ ha₂ hb₂
    (isEffectiveCartierDivisor_targetGraph_on_chart π f j jA p hRet w)
  let : IsClosedImmersion mI :=
    MorphismProperty.of_isPullback (retainedProductInclusion_isPullback b π d₂) inferInstance
  let : IsClosedImmersion mZ :=
    MorphismProperty.of_isPullback (retainedProductInclusion_isPullback b π zA) inferInstance
  let : IsAffine (pullback mI w) := isAffine_of_isAffineHom iI
  let : IsAffine (pullback mZ w) := isAffine_of_isAffineHom iZ
  refine ⟨μ, hμ, ?_, ?_⟩
  · obtain ⟨v₁, hv₁⟩ := exists_chartInverseBoundary_factor b π f w d₁ d₂ bI hbI
    obtain ⟨v₂, hv₂⟩ := exists_chartTargetBoundary_factor b π w (jA ≫ π) κ
      (graphTargetParameterMap_snd π f j jA p hRet) d₂
    have h₁ : (pullback.fst pW iI).appTop b₀ = 1 :=
      SectionData.graphSectionRatioCoefficient_on_infinity q (f ≫ π) j p hB a z s hs H
        e d₁ hd₁ ha c₁ w₁ (pullback.fst pW iI) v₁
        (by simpa only [infinityProductMap] using hv₁) ha₁
    have h₂ : (iI).appTop a₀ = 1 :=
      SectionData.graphSectionRatioCoefficient_on_infinity q π jA (𝟙 X) hA a z z
        (Category.comp_id z) (IsPullback.of_id_snd) e d₂ hd₂ ha c₂ w₂ iI v₂
        (by simpa only [Category.assoc, infinityProductMap] using hv₂) ha₂
    exact appTop_normAssociationUnit_eq_one_of_inverseBoundary pW iI b₀ a₀ μ h₁ h₂ hμ
  · let J := retainedProductInclusion b (f ≫ π) j
    let s₀ := productMarkedSection b π f zA j s Hmark
    let H₀ := productMarkedSection_isPullback b π f zA j s Hmark
    let Jw := pullback.snd J w₁
    let sw := baseChangeMarkedSection F J mZ s₀ H₀ w
    let hsw := markedSection_baseChange_equation F J mZ s₀ H₀ w
    let e₁ := pairedMarkToSource π f j jA p hRet z s hs
    let e₂ := pairedMarkToTarget q π f j jA p hB hA z
    let u := pullback.fst mZ w
    have hsource : (sw ≫ Jw) ≫ w₁ = (u ≫ e₁) ≫ markedProductMap (f ≫ π) j s :=
      pairedNormChart_sourceMark_factor π f j jA p hRet z s hs H w
    have htarget : iZ ≫ w₂ = (u ≫ e₂) ≫ markedProductMap π jA z :=
      pairedNormChart_targetMark_factor q π f j jA p hRet hB hA z w
    have hsource' := SectionData.graphSectionRatioCoefficient_on_mark q (f ≫ π) j p hB a z s hs H
      e d₁ hd₁ ha c₁ w₁ (sw ≫ Jw) (u ≫ e₁) hsource ha₁
    have htarget' := SectionData.graphSectionRatioCoefficient_on_mark q π jA (𝟙 X) hA a z z
      (Category.comp_id z) (IsPullback.of_id_snd) e d₂ hd₂ ha c₂ w₂ iZ (u ≫ e₂) htarget ha₂
    have hsame : (sw ≫ Jw).appTop b₀ = (iZ).appTop a₀ := by
      have heq : e₁ ≫ markedProductToTarget q (f ≫ π) j p hB z s hs =
          e₂ ≫ markedProductToTarget q π jA (𝟙 X) hA z z (Category.comp_id z) :=
        pairedMark_coordinateMap q π f j jA p hRet hB hA z s hs
      dsimp only [b₀, a₀]
      rw [hsource', htarget']
      simp only [Category.assoc, heq]
    obtain ⟨vResidual, hvResidual⟩ := hResidual
    have hres : (residualMarkedFiberMap pW Jw iZ sw hsw).appTop b₀ = 1 :=
      SectionData.graphSectionRatioCoefficient_on_infinity q (f ≫ π) j p hB a z s hs H
        e d₁ hd₁ ha c₁ w₁ (residualMarkedFiberMap pW Jw iZ sw hsw) vResidual
        (by simpa only [infinityProductMap] using hvResidual) ha₁
    have hc := pairedNormChart_targetMark_cartier q π f j jA p hRet hB hA z s hs H w
    have hreg := (isRegular_appTop_graphSectionRatioCoefficient w₂ Δ₂ c₂.T
      iZ hc c₂.aS c₂.bS ha₂ hb₂).right
    exact appTop_normAssociationUnit_eq_one_of_markedBoundary pW iZ Jw sw hsw
      (baseChangeMarkedSection_isPullback F J mZ s₀ H₀ w) b₀ a₀ μ hsame hres hreg hμ

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
