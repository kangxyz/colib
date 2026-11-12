/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.SectionNormRatio
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ParameterBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionNormUnit
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumPullback

/-!
# The principal cycle of the original correction norm unit

On the actual compact product the corrected norm ratio gives the two
signed Cartier differences and the original graph divisor.

Adapted from `NativeCorrectionNormAction.lean` under
`Motivic/Transfers/Presheaf/Actions/Pencils` at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

open CategoryTheory CategoryTheory.Limits Stacks.Ample Stacks.Chow Stacks.Divisors Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

local instance {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] :
    IsInvertibleModule X (divisorSheaf D) := Stacks.Divisors.isInvertible_divisorSheaf D

variable {S X Y P C A Z D₁ D₂ : Scheme.{u}} [IsIntegral A]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π] (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d₁ : D₁ ⟶ C) (hd₁ : Disjoint (Set.range j) (Set.range d₁))
  (d₂ : D₂ ⟶ P) (hd₂ : Disjoint (Set.range jA) (Set.range d₂))
  (ha : Disjoint (Set.range a) (Set.range z))
  (c₁ : SectionData q (f ≫ π) j p hB a z s hs H e d₁ hd₁ ha)
  (c₂ : SectionData q π jA (𝟙 X) hA a z z (Category.comp_id z) (IsPullback.of_id_snd)
    e d₂ hd₂ ha)

local notation "b" => (a ≫ q)
local notation "bA" => (jA ≫ π)
local notation "F" => (retainedProductInclusion b π f)
local notation "zA" => (z ≫ jA)
local notation "hA₀" => (hA.trans (Category.id_comp q))
local notation "τ" => (correctionTargetParameterMap q π jA hA₀ a)
local notation "hmark" => (markedSection_original_equation f j zA s
  (pairedMark_isPullback f j jA p hRet z s H))
local notation "T₀" => (pullback b π : Scheme)
local notation "Δ₂" => (Hom.ker (compactificationGraph π jA))
local notation "L₂" => (tensorModules (divisorSheaf Δ₂) (SectionData.T c₂))
local notation "pole" => (tensorSection (divisorSheaf Δ₂) (SectionData.T c₂) ⊤
  (divisorSheafGlobalSection Δ₂) (SectionData.bS c₂))

local notation "ha₀" => (congrArg (a ≫ ·) hA₀)
local notation "I" => (@AlgebraicGeometry.zeroScheme _ c₁.N c₁.N_invertible c₁.nS)
local notation "J" => (@AlgebraicGeometry.zeroScheme _ c₁.N c₁.N_invertible c₁.dS)
local notation "J₂" => (@AlgebraicGeometry.zeroScheme _ c₂.T c₂.T_invertible c₂.bS)
local notation "γ" => (relativeGraph b π (a ≫ jA) ((Category.assoc a jA π).trans ha₀))

/-- The native correction norm unit has the original signed divisor on
the actual compact product. -/
theorem exists_correctionNormPrincipalCycle
    [IsFiniteLocallyFree (retainedProductInclusion (a ≫ q) π f)]
    [IsClosedImmersion (z ≫ jA)] [IsIntegral (pullback (a ≫ q) π)]
    [IsNoetherian (pullback (a ≫ q) π)] [IsNoetherian (pullback (a ≫ q) (f ≫ π))]
    (bI : pullback f d₂ ⟶ D₁) (hbI : bI ≫ d₁ = pullback.fst f d₂)
    (bE : (residualMarkedFiberOpen f j zA s hmark).toScheme ⟶ D₁)
    (hbE : bE ≫ d₁ = residualMarkedFiberMap f j zA s hmark)
    (hL : IsInvertibleModule (pullback bA π) L₂)
    (hSourceNum : IsEffectiveCartierDivisor I) (hSourceDen : IsEffectiveCartierDivisor J)
    (hNum : IsEffectiveCartierDivisor (@AlgebraicGeometry.zeroScheme _ L₂ hL c₂.aS))
    (hDen : IsEffectiveCartierDivisor J₂)
    (hInfinity : Function.Surjective (d₂ ≫ π)) :
    ∃ (U : (T₀).Opens) (hU : Nonempty U) (r : Γ(T₀, U))
      (l : pullback b (d₂ ≫ π) ⨿ pullback b (zA ≫ π) ⟶ U.toScheme),
      letI : Nonempty U := hU
      IsUnit r ∧
      l ≫ U.ι = coprod.desc (retainedProductInclusion b π d₂) (retainedProductInclusion b π zA) ∧
      l.appTop (U.topIso.inv r) = 1 ∧
      principalCycle T₀ ((T₀).germToFunctionField U r) =
        (cartierCycle ((@AlgebraicGeometry.zeroScheme _ L₂ hL c₂.aS).comap τ) -
          cartierCycle ((J₂).comap τ)) -
          (finiteCyclePushforward F (cartierCycle J) - finiteCyclePushforward F (cartierCycle I)) -
          cartierCycle (γ).ker := by
  let := c₁.N_invertible
  let := c₂.T_invertible
  let : IsInvertibleModule (pullback bA π) L₂ := hL
  let I₂ := @AlgebraicGeometry.zeroScheme _ L₂ hL c₂.aS
  obtain ⟨U, hLocalFinite, hPairs⟩ := exists_correctionNormUnit
    q π f j jA p hRet hB hA a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂ bI hbI bE hbE
  let : IsFiniteLocallyFree (pullback.snd F U.ι) := hLocalFinite
  obtain ⟨hn, -, hp, -, hQuotient⟩ := hPairs
  obtain ⟨r, l, hr, hl, hunit, hnorm⟩ := hQuotient
  have hsurj := wholeBoundary_surjective_firstProjection b π d₂ zA U l hl hInfinity
  let : Nonempty (pullback b (d₂ ≫ π) ⨿ pullback b (zA ≫ π) : Scheme.{u}) :=
    ⟨(hsurj (genericPoint A)).choose⟩
  let hU : Nonempty U := ⟨l (Classical.choice inferInstance)⟩
  have hτ : τ = retainedSourceChange bA b π a ha₀ := by
    apply pullback.hom_ext <;> simp only [correctionTargetParameterMap_fst,
      correctionTargetParameterMap_snd, retainedSourceChange_fst, retainedSourceChange_snd]
  let : Flat τ := hτ.symm ▸ MorphismProperty.of_isPullback
    (retainedSourceChange_isPullback bA b π a ha₀).flip inferInstance
  have hΔ : (γ).ker = (Δ₂).comap τ := by
    rw [hτ]
    exact ker_eq_comap_of_cartesian
      (relativeGraph_sourceChange_isPullback bA b a ha₀ π jA rfl).flip
  have hΔ₂ := isPullbackDefined_of_flat τ Δ₂ inferInstance
  have hI₂ := isPullbackDefined_of_flat τ I₂ hNum
  have hJ₂ := isPullbackDefined_of_flat τ J₂ hDen
  have hpole : zeroScheme _ L₂ pole = Δ₂ * J₂ :=
    (zeroScheme_tensorSection_eq_mul (divisorSheaf Δ₂) c₂.T
      (divisorSheafGlobalSection Δ₂) c₂.bS).trans
      (congrArg (fun K : (pullback bA π).IdealSheafData ↦ K * J₂)
        (zeroScheme_canonicalSection Δ₂))
  let M := (Modules.pullback τ).obj L₂
  let n₂ := pullbackGlobalSections τ L₂ pole
  let d₂s := pullbackGlobalSections τ L₂ c₂.aS
  have hPoleA : zeroScheme (T₀) M n₂ = (Δ₂).comap τ * (J₂).comap τ :=
    (Stacks.Divisors.zeroScheme_pullback τ L₂ pole).trans
      ((congrArg (fun K : (pullback bA π).IdealSheafData ↦ K.comap τ) hpole).trans
        (AlgebraicGeometry.comap_mul τ Δ₂ J₂))
  have hNumA : zeroScheme (T₀) M d₂s = I₂.comap τ :=
    Stacks.Divisors.zeroScheme_pullback τ L₂ c₂.aS
  have hn₂ := (congrArg IsEffectiveCartierDivisor hPoleA).mpr
    (isEffectiveCartierDivisor_mul _ _ hΔ₂ hJ₂)
  have hd₂s := (congrArg IsEffectiveCartierDivisor hNumA).mpr hI₂
  have hpp := zeroScheme_pullbackSquare_eq_top τ (U.ι ≫ τ) U.ι (𝟙 _) (by simp)
    L₂ pole hp
  have hcoeff := sectionRatioCoefficient_appTop_of_pullbackSquare τ (U.ι ≫ τ) U.ι
    (𝟙 _) (by simp) L₂ pole c₂.aS hp hpp
  have hnorm' := hnorm.trans (by simpa only [Hom.id_appTop, CommRingCat.id_apply] using hcoeff)
  have hcycle := principalCycle_eq_sectionNormRatio F c₁.N M c₁.nS c₁.dS n₂ d₂s
    hSourceNum hSourceDen hn₂ hd₂s U r hr hn hpp hnorm'
  change _ = finiteCyclePushforward F (cartierCycle I - cartierCycle J) -
    (cartierCycle (zeroScheme (T₀) M n₂) - cartierCycle (zeroScheme (T₀) M d₂s)) at hcycle
  have hDiv : principalCycle T₀ ((T₀).germToFunctionField U r) =
      (cartierCycle (I₂.comap τ) - cartierCycle ((J₂).comap τ)) -
        (finiteCyclePushforward F (cartierCycle J) - finiteCyclePushforward F (cartierCycle I)) -
        cartierCycle (γ).ker := by
    rw [hcycle, hPoleA, hNumA, cartierCycle_mul _ _ hΔ₂ hJ₂, map_sub, hΔ]
    abel
  exact ⟨U, hU, r, l, hr, hl, hunit, hDiv⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

end
