/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.SectionNormRatio
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ParameterChange
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.PullbackGeneration
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionRatioBaseChange
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SectionData
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumPullback

/-!
# The two original lambda cycles on a parameter component

The principal cycle of the normalized norm unit is the difference of the
same two signed zero cycles. The original graph terms cancel through the
finite map of products on each actual parameter component.

Adapted from `Motivic/Transfers/Presheaf/Actions/Pencils/OriginalComponentLambdaDifference.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.Chow Stacks.Divisors Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

local instance {V : Scheme.{u}} (D : V.IdealSheafData) [IsEffectiveCartierDivisor D] :
    IsInvertibleModule V (divisorSheaf D) := Stacks.Divisors.isInvertible_divisorSheaf D

variable {S X Y P C A Z D₁ D₂ K : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π] (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) [Flat p] (hRet : j ≫ f = p ≫ jA)
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
  (α : K ⟶ Y) [Flat α] [IsNoetherian K]

local notation "b" => (j ≫ f ≫ π)
local notation "b'" => (α ≫ b)
local notation "F" => (graphProductMap π f j)
local notation "F'" => (retainedProductInclusion b' π f)
local notation "κ" => (graphTargetParameterMap π f j jA p hRet)
local notation "ρ₁" => (retainedSourceChange b b' (f ≫ π) α rfl)
local notation "ρ₂" => (retainedSourceChange b b' π α rfl)
local notation "τ" => (ρ₂ ≫ κ)
local notation "Δ₁" => (Hom.ker (compactificationGraph (f ≫ π) j))
local notation "Δ₂" => (Hom.ker (compactificationGraph π jA))
local notation "L₁" => (tensorModules (divisorSheaf Δ₁) (SectionData.T c₁))
local notation "L₂" => (tensorModules (divisorSheaf Δ₂) (SectionData.T c₂))
local notation "b₁" => (tensorSection (divisorSheaf Δ₁) (SectionData.T c₁) ⊤
  (divisorSheafGlobalSection Δ₁) (SectionData.bS c₁))
local notation "b₂" => (tensorSection (divisorSheaf Δ₂) (SectionData.T c₂) ⊤
  (divisorSheafGlobalSection Δ₂) (SectionData.bS c₂))

variable [hF : IsFiniteLocallyFree (graphProductMap π f j)]
  [hNB : IsNoetherian (pullback (α ≫ j ≫ f ≫ π) (f ≫ π))]
  [hNA : IsNoetherian (pullback (α ≫ j ≫ f ≫ π) π)]
  [hIA : IsIntegral (pullback (α ≫ j ≫ f ≫ π) π)]
  (U : (pullback (j ≫ f ≫ π) π : Scheme.{u}).Opens)
  [hWU : Nonempty ((retainedSourceChange (j ≫ f ≫ π) (α ≫ j ≫ f ≫ π) π α rfl) ⁻¹ᵁ U)]

local notation "w₁" => (pullback.fst F (Scheme.Opens.ι U))
local notation "w₂" => (Scheme.Opens.ι U ≫ κ)

set_option maxHeartbeats 800000 in
-- Four original section pullbacks and their graph kernels enter the cycle comparison.
include U hF hNB hNA hIA hWU in
/-- The principal divisor of the same norm unit on an integral parameter
component is the difference of the original signed lambda divisors. -/
theorem principalCycle_eq_pairedLambdaCycle (r : Γ(pullback b π, U)) (hr : IsUnit r) :
    letI hD₁ : IsEffectiveCartierDivisor Δ₁ :=
      compactificationGraphIdeal_isEffectiveCartierDivisor (f ≫ π) j
    letI hD₂ : IsEffectiveCartierDivisor Δ₂ :=
      compactificationGraphIdeal_isEffectiveCartierDivisor π jA
    letI hT₁ := c₁.T_invertible
    let TA : (pullback (jA ≫ π) π).Modules := c₂.T
    let hT₂ : IsInvertibleModule (pullback (jA ≫ π) π) TA := c₂.T_invertible
    let LA := Stacks.Divisors.tensorModules (divisorSheaf Δ₂) TA
    let aA : Γ(LA, ⊤) := c₂.aS
    let bA : Γ(TA, ⊤) := c₂.bS
    let gA : U.toScheme ⟶ pullback (jA ≫ π) π := U.ι ≫ κ
    let hLA := @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf _ (divisorSheaf Δ₂) TA
      (@Stacks.Divisors.isInvertible_divisorSheaf _ Δ₂ hD₂) hT₂
    let MA := (Modules.pullback gA).obj LA
    let hMA := @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _ gA LA hLA
    let aAPull : Γ(MA, ⊤) := pullbackGlobalSections gA LA aA
    let bAPull : Γ(MA, ⊤) := pullbackGlobalSections gA LA
      (tensorSection (divisorSheaf Δ₂) TA ⊤ (divisorSheafGlobalSection Δ₂) bA)
    let XU : Scheme.{u} := pullback F U.ι
    let fU : XU ⟶ U.toScheme := pullback.snd F U.ι
    let TB : (pullback b (f ≫ π)).Modules := c₁.T
    let LB := Stacks.Divisors.tensorModules (divisorSheaf Δ₁) TB
    let aB : Γ(LB, ⊤) := c₁.aS
    let bB : Γ(TB, ⊤) := c₁.bS
    let gB : XU ⟶ pullback b (f ≫ π) := pullback.fst F U.ι
    let hLB := @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf _ (divisorSheaf Δ₁) TB
      (@Stacks.Divisors.isInvertible_divisorSheaf _ Δ₁ hD₁) hT₁
    let MB := (Modules.pullback gB).obj LB
    let hMB := @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _ gB LB hLB
    let aBPull : Γ(MB, ⊤) := pullbackGlobalSections gB LB aB
    let bBPull : Γ(MB, ⊤) := pullbackGlobalSections gB LB
      (tensorSection (divisorSheaf Δ₁) TB ⊤ (divisorSheafGlobalSection Δ₁) bB)
    let hFU : IsFiniteLocallyFree fU :=
      isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback F U.ι) hF
    ∀ (ha₁ : @AlgebraicGeometry.zeroScheme XU MB hMB aBPull = ⊤)
      (ha₂ : @AlgebraicGeometry.zeroScheme U.toScheme MA hMA aAPull = ⊤),
    let cB : Γ(XU, ⊤) := @sectionRatioCoefficient XU MB hMB aBPull bBPull ha₁
    let cA : Γ(U.toScheme, ⊤) :=
      @sectionRatioCoefficient U.toScheme MA hMA aAPull bAPull ha₂
    (@normTop XU U.toScheme fU hFU) cB * U.topIso.inv r = cA →
    let I₁ := @AlgebraicGeometry.zeroScheme _ LB hLB aB
    let J₁ := @AlgebraicGeometry.zeroScheme _ TB hT₁ bB
    let I₂ := @AlgebraicGeometry.zeroScheme _ LA hLA aA
    let J₂ := @AlgebraicGeometry.zeroScheme _ TA hT₂ bA
    IsEffectiveCartierDivisor I₁ → IsEffectiveCartierDivisor J₁ →
    IsEffectiveCartierDivisor I₂ → IsEffectiveCartierDivisor J₂ →
    principalCycle (pullback b' π) ((pullback b' π : Scheme.{u}).germToFunctionField
      (ρ₂ ⁻¹ᵁ U) ((ρ₂).app U r)) =
      finiteCyclePushforward F'
          (cartierCycle (I₁.comap ρ₁) - cartierCycle (J₁.comap ρ₁)) -
        (cartierCycle (I₂.comap τ) - cartierCycle (J₂.comap τ)) := by
  dsimp only
  let := c₁.T_invertible
  let := c₂.T_invertible
  let : IsFiniteLocallyFree (pullback.snd F U.ι) :=
    isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback F U.ι) inferInstance
  intro ha₁ ha₂ hnorm hI₁ hJ₁ hI₂ hJ₂
  let I₁ := zeroScheme _ L₁ c₁.aS
  let J₁ := zeroScheme _ c₁.T c₁.bS
  let I₂ := zeroScheme _ L₂ c₂.aS
  let J₂ := zeroScheme _ c₂.T c₂.bS
  have HF := retainedProductInclusion_sourceChange_isPullback b b' α rfl π f
  let : IsFiniteLocallyFree F' :=
    isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback HF inferInstance
  obtain ⟨ha₁', ha₂', hnorm'⟩ := sectionNormRatio_morphismRestrict F F' ρ₁ ρ₂ HF κ
    L₁ L₂ c₁.aS b₁ c₂.aS b₂ U r ha₁ ha₂ hnorm
  have hβ : (α ≫ p) ≫ (jA ≫ π) = b' := by
    simp only [Category.assoc]
    rw [← Category.assoc p jA π, ← hRet, Category.assoc]
  have hτ : τ = retainedSourceChange (jA ≫ π) b' π (α ≫ p) hβ := by
    apply pullback.hom_ext <;> simp only [Category.assoc, graphTargetParameterMap_fst,
      graphTargetParameterMap_snd, retainedSourceChange_fst, retainedSourceChange_fst_assoc,
      retainedSourceChange_snd]
  let : Flat ρ₁ := MorphismProperty.of_isPullback
    (retainedSourceChange_isPullback b b' (f ≫ π) α rfl).flip inferInstance
  let : Flat τ := hτ.symm ▸ MorphismProperty.of_isPullback
    (retainedSourceChange_isPullback (jA ≫ π) b' π (α ≫ p) hβ).flip inferInstance
  have hD₁ := isPullbackDefined_of_flat ρ₁ Δ₁ inferInstance
  have hD₂ := isPullbackDefined_of_flat τ Δ₂ inferInstance
  have hC₁ := isPullbackDefined_of_flat ρ₁ I₁ hI₁
  have hC₂ := isPullbackDefined_of_flat τ I₂ hI₂
  have hP₁ := isPullbackDefined_of_flat ρ₁ J₁ hJ₁
  have hP₂ := isPullbackDefined_of_flat τ J₂ hJ₂
  have hzero₁ : zeroScheme _ L₁ b₁ = Δ₁ * J₁ :=
    (zeroScheme_tensorSection_eq_mul (divisorSheaf Δ₁) c₁.T
      (divisorSheafGlobalSection Δ₁) c₁.bS).trans
      (congrArg (fun I : (pullback b (f ≫ π)).IdealSheafData ↦ I * J₁)
        (zeroScheme_canonicalSection Δ₁))
  have hzero₂ : zeroScheme _ L₂ b₂ = Δ₂ * J₂ :=
    (zeroScheme_tensorSection_eq_mul (divisorSheaf Δ₂) c₂.T
      (divisorSheafGlobalSection Δ₂) c₂.bS).trans
      (congrArg (fun I : (pullback (jA ≫ π) π).IdealSheafData ↦ I * J₂)
        (zeroScheme_canonicalSection Δ₂))
  have hA₁ : zeroScheme _ ((Modules.pullback ρ₁).obj L₁)
      (pullbackGlobalSections ρ₁ L₁ c₁.aS) = I₁.comap ρ₁ :=
    Stacks.Divisors.zeroScheme_pullback ρ₁ L₁ c₁.aS
  have hA₂ : zeroScheme _ ((Modules.pullback τ).obj L₂)
      (pullbackGlobalSections τ L₂ c₂.aS) = I₂.comap τ :=
    Stacks.Divisors.zeroScheme_pullback τ L₂ c₂.aS
  have hB₁ : zeroScheme _ ((Modules.pullback ρ₁).obj L₁)
      (pullbackGlobalSections ρ₁ L₁ b₁) = (Δ₁).comap ρ₁ * J₁.comap ρ₁ :=
    (Stacks.Divisors.zeroScheme_pullback ρ₁ L₁ b₁).trans
      ((congrArg (fun I : (pullback b (f ≫ π)).IdealSheafData ↦ I.comap ρ₁) hzero₁).trans
        (AlgebraicGeometry.comap_mul ρ₁ Δ₁ J₁))
  have hB₂ : zeroScheme _ ((Modules.pullback τ).obj L₂)
      (pullbackGlobalSections τ L₂ b₂) = (Δ₂).comap τ * J₂.comap τ :=
    (Stacks.Divisors.zeroScheme_pullback τ L₂ b₂).trans
      ((congrArg (fun I : (pullback (jA ≫ π) π).IdealSheafData ↦ I.comap τ) hzero₂).trans
        (AlgebraicGeometry.comap_mul τ Δ₂ J₂))
  have htotal₁ := hB₁.symm ▸ isEffectiveCartierDivisor_mul _ _ hD₁ hP₁
  have htotal₂ := hB₂.symm ▸ isEffectiveCartierDivisor_mul _ _ hD₂ hP₂
  have hnum₁ := (congrArg IsEffectiveCartierDivisor hA₁).mpr hC₁
  have hnum₂ := (congrArg IsEffectiveCartierDivisor hA₂).mpr hC₂
  have hcycle := principalCycle_eq_sectionNormRatio F' ((Modules.pullback ρ₁).obj L₁)
    ((Modules.pullback τ).obj L₂)
    (pullbackGlobalSections ρ₁ L₁ c₁.aS) (pullbackGlobalSections ρ₁ L₁ b₁)
    (pullbackGlobalSections τ L₂ c₂.aS) (pullbackGlobalSections τ L₂ b₂)
    hnum₁ htotal₁ hnum₂ htotal₂ (ρ₂ ⁻¹ᵁ U) ((ρ₂).app U r)
    (hr.map ((ρ₂).app U).hom) ha₁' ha₂' hnorm'
  let γ₁ := relativeGraph b' (f ≫ π) (α ≫ j) (Category.assoc α j (f ≫ π))
  let γ₂ := relativeGraph b' π ((α ≫ p) ≫ jA) (by rw [Category.assoc, hβ])
  have hg₁ : γ₁.ker = (Δ₁).comap ρ₁ := by
    exact ker_eq_comap_of_cartesian
      (relativeGraph_sourceChange_isPullback b b' α rfl (f ≫ π) j rfl).flip
  have hg₂ : γ₂.ker = (Δ₂).comap τ := by
    rw [hτ]
    exact ker_eq_comap_of_cartesian
      (relativeGraph_sourceChange_isPullback (jA ≫ π) b' (α ≫ p) hβ π jA rfl).flip
  have hγ : γ₁ ≫ F' = γ₂ := by
    apply pullback.hom_ext
    · simp only [γ₁, γ₂, Category.assoc, retainedProductInclusion_fst, relativeGraph_fst]
    · have hg := congrArg (fun k : Y ⟶ P ↦ α ≫ k) hRet
      simpa [γ₁, γ₂, Category.assoc] using hg
  have hcancel : finiteCyclePushforward F' (cartierCycle ((Δ₁).comap ρ₁)) =
      cartierCycle ((Δ₂).comap τ) := by
    rw [← hg₁, ← hg₂, cartierCycle_ker_eq_pushforward, cartierCycle_ker_eq_pushforward,
      finiteCyclePushforward_comp_apply]
    exact finiteCyclePushforward_congr _ _ hγ _
  rw [hA₁, hB₁, hA₂, hB₂,
    cartierCycle_mul _ _ hD₁ hP₁, cartierCycle_mul _ _ hD₂ hP₂,
    map_sub, map_add, hcancel] at hcycle
  change _ = finiteCyclePushforward F'
      (cartierCycle (I₁.comap ρ₁) - cartierCycle (J₁.comap ρ₁)) -
    (cartierCycle (I₂.comap τ) - cartierCycle (J₂.comap τ))
  rw [hcycle, map_sub]
  abel

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
