/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedZeroSourceChange
public import Colib.AlgebraicGeometry.Correspondences.Moving.PrincipalOrderOpenPushforward
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.OpenRestriction
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeCycle
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Actions.PrincipalOrder
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormCycle
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SectionCorrespondences
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.WholeSectionCartier

/-!
# The original lambda difference on a parameter component

The normalized unit acts through the exact difference of the two original
lambda correspondences. Closed supports are changed by flat pullback and
finite pushforward through their literal retained products.

Adapted from `OriginalComponentLambdaDifferenceAction.lean` under
`Motivic/Transfers/Presheaf/Actions/Pencils` at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.Chow Stacks.Divisors Stacks.Morphisms

universe u w

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

open Cor.PrincipalOrder

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

local instance {U : Scheme.{u}} (D : U.IdealSheafData) [IsEffectiveCartierDivisor D] :
    IsInvertibleModule U (divisorSheaf D) := Stacks.Divisors.isInvertible_divisorSheaf D

variable {k : Type u} [Field k] {S X Y P C A Z D₁ D₂ K V : Scheme.{u}}
  [IsAffine S] [IsAffine X] [IsAffine Y] [IsAffine A] [IsAffine K] [IsAffine V]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsProper π] (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) [Flat p] (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a] [SmoothOfRelativeDimension 1 ((a ≫ jA) ≫ π)]
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d₁ : D₁ ⟶ C) (hd₁ : Disjoint (Set.range j) (Set.range d₁))
  (d₂ : D₂ ⟶ P) (hd₂ : Disjoint (Set.range jA) (Set.range d₂))
  (ha : Disjoint (Set.range a) (Set.range z))
  (c₁ : SectionData q (f ≫ π) j p hB a z s hs H e d₁ hd₁ ha)
  (c₂ : SectionData q π jA (𝟙 X) hA a z z (Category.comp_id z) (IsPullback.of_id_snd)
    e d₂ hd₂ ha)
  (α : K ⟶ Y) [IsOpenImmersion α] [IsIntegral K]
  (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ f ≫ π)]
  (g : V ⟶ A) (hg : v ≫ f = g ≫ (a ≫ jA))
  (hc₁ : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d₁ ∨ x ∈ Set.range (s ≫ j))
  (hc₂ : ∀ x : P, x ∈ Set.range (a ≫ jA) ∨ x ∈ Set.range d₂ ∨
    x ∈ Set.range (z ≫ jA))

local notation "b" => (j ≫ f ≫ π)
local notation "b'" => (α ≫ b)
local notation "bA" => (jA ≫ π)
local notation "rB" => (v ≫ f ≫ π)
local notation "rA" => ((a ≫ jA) ≫ π)
local notation "F" => (graphProductMap π f j)
local notation "F'" => (retainedProductInclusion b' π f)
local notation "κ" => (graphTargetParameterMap π f j jA p hRet)
local notation "ρ₁" => (retainedSourceChange b b' (f ≫ π) α rfl)
local notation "ρ₂" => (retainedSourceChange b b' π α rfl)
local notation "τ" => (ρ₂ ≫ κ)
local notation "iB" => (retainedProductInclusion b (f ≫ π) v)
local notation "iA" => (retainedProductInclusion bA π (a ≫ jA))
local notation "iB'" => (retainedProductInclusion b' (f ≫ π) v)
local notation "iA'" => (retainedProductInclusion b' π (a ≫ jA))
local notation "T'" => (pullback b' π : Scheme)
local notation "A'" => (retainedProduct b' π (a ≫ jA))
local notation "Δ₁" => (Hom.ker (compactificationGraph (f ≫ π) j))
local notation "Δ₂" => (Hom.ker (compactificationGraph π jA))
local notation "L₁" => (tensorModules (divisorSheaf Δ₁) (SectionData.T c₁))
local notation "L₂" => (tensorModules (divisorSheaf Δ₂) (SectionData.T c₂))

local instance smoothPairedLambdaSource : Smooth b := SmoothOfRelativeDimension.smooth 1 b
local instance smoothPairedLambdaParameter : Smooth bA := SmoothOfRelativeDimension.smooth 1 bA
local instance smoothPairedLambdaRetainedSource : Smooth rB := SmoothOfRelativeDimension.smooth 1 rB
local instance smoothPairedLambdaRetainedTarget : Smooth rA := SmoothOfRelativeDimension.smooth 1 rA

local notation "K₀" => (SmoothSite.mk (b' ≫ t))
local notation "Y₀" => (SmoothSite.mk (b ≫ t))
local notation "X₀" => (SmoothSite.mk (bA ≫ t))
local notation "V₀" => (SmoothSite.mk (rB ≫ t))
local notation "A₀" => (SmoothSite.mk (rA ≫ t))

local notation "hK" => (show (α ≫ p) ≫ bA = b' from by
  simp only [Category.assoc]
  rw [← Category.assoc p jA π, ← hRet, Category.assoc])
local notation "hg'" => (show g ≫ rA = rB from by
  rw [← Category.assoc g (a ≫ jA) π, ← hg, Category.assoc])
local notation "α₀" => (SmoothSite.homMk (X := K₀) (Y := Y₀) α (Category.assoc α b t).symm)
local notation "p₀" => (SmoothSite.homMk (X := K₀) (Y := X₀) (α ≫ p)
  ((Category.assoc (α ≫ p) bA t).symm.trans (congrArg (fun w ↦ w ≫ t) hK)))
local notation "g₀" => (SmoothSite.homMk (X := V₀) (Y := A₀) g
  ((Category.assoc g rA t).symm.trans (congrArg (fun w ↦ w ≫ t) hg')))
local notation "hBase" => ((retainedProductInclusion_fst_assoc b' π (a ≫ jA) (b' ≫ t)).trans
  (pullback.condition_assoc (f := b') (g := rA) t))
local notation "m" => (forgetBaseProductMap t b' rA)

variable [IsFiniteLocallyFree (graphProductMap π f j)]
  [IsLocallyNoetherian (pullback (j ≫ f ≫ π) (f ≫ π))]
  [IsLocallyNoetherian (pullback (jA ≫ π) π)]
  [IsNoetherian (pullback (α ≫ j ≫ f ≫ π) (f ≫ π))]
  [IsNoetherian (pullback (α ≫ j ≫ f ≫ π) π)]
  [IsIntegral (pullback (α ≫ j ≫ f ≫ π) π)]
  [Nonempty (retainedProduct (α ≫ j ≫ f ≫ π) π (a ≫ jA))]
  (U : (pullback (j ≫ f ≫ π) π : Scheme.{u}).Opens)
  [Nonempty ((retainedSourceChange (j ≫ f ≫ π) (α ≫ j ≫ f ≫ π) π α rfl) ⁻¹ᵁ U)]

local notation "W" => (ρ₂ ⁻¹ᵁ U)
local notation "w₁" => (pullback.fst F (Scheme.Opens.ι U))
local notation "w₂" => (Scheme.Opens.ι U ≫ κ)

set_option maxHeartbeats 800000 in
-- The two actual graph compositions compare the four whole support cycles.
omit [IsIntegral K] in
include hRet hg hc₁ hc₂ in
/-- The same two whole spans give the actual principal correspondence on
the original component, after the retained target and field-base maps. -/
theorem componentLambdaDifference_eq_principal (r : Γ(pullback b π, U)) (hr : IsUnit r)
    (hW : (Set.range iA')ᶜ ⊆ (W : Set T')) :
    letI : IsAffine (K₀).left := inferInstanceAs (IsAffine K)
    letI : IsAffine A' := retainedProduct_affine b' π (a ≫ jA)
    letI : SmoothOfRelativeDimension 1 (iA' ≫ pullback.fst b' π) :=
      retainedProduct_smooth b' π (a ≫ jA)
    letI := c₁.T_invertible
    letI := c₂.T_invertible
    letI : IsFiniteLocallyFree (pullback.snd F U.ι) :=
      isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback F U.ι) inferInstance
    ∀ (ha₁ : graphNumeratorGeneratesOnPullback w₁ Δ₁ c₁.T c₁.aS)
      (ha₂ : graphNumeratorGeneratesOnPullback w₂ Δ₂ c₂.T c₂.aS),
    normTop (pullback.snd F U.ι)
        (graphSectionRatioCoefficientOfGenerating w₁ Δ₁ c₁.T c₁.aS c₁.bS ha₁) *
        U.topIso.inv r = graphSectionRatioCoefficientOfGenerating w₂ Δ₂ c₂.T c₂.aS c₂.bS ha₂ →
    (((Cor.graphFunctor k).map α₀ ≫ c₁.lambda t v hc₁) ≫ (Cor.graphFunctor k).map g₀) -
      (Cor.graphFunctor k).map p₀ ≫ c₂.lambda t (a ≫ jA) hc₂ =
      correspondence (X := K₀) (Y := A₀) (pullback.fst b' π) iA' W hW ((ρ₂).app U r)
        (hr.map ((ρ₂).app U).hom) (pullback.snd b' rA) hBase := by
  let := c₁.T_invertible
  let := c₂.T_invertible
  let : IsFiniteLocallyFree (pullback.snd F U.ι) :=
    isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback F U.ι) inferInstance
  intro ha₁ ha₂ hnorm
  let : IsAffine (K₀).left := inferInstanceAs (IsAffine K)
  let : IsNoetherian K := inferInstanceAs (IsNoetherian (K₀).left)
  let : IsAffine A' := retainedProduct_affine b' π (a ≫ jA)
  let : SmoothOfRelativeDimension 1 (iA' ≫ pullback.fst b' π) :=
    retainedProduct_smooth b' π (a ≫ jA)
  let : IsIntegral A' := isIntegral_of_isOpenImmersion iA'
  let : IsNoetherian A' :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian iA'
      toCompactSpace := inferInstance }
  let ι₁ := retainedSourceChange b b' rB α rfl
  let ι₂ := retainedSourceChange bA b' rA (α ≫ p) hK
  have hτ : τ = retainedSourceChange bA b' π (α ≫ p) hK := by
    apply pullback.hom_ext <;> simp only [Category.assoc, graphTargetParameterMap_fst,
      graphTargetParameterMap_snd, retainedSourceChange_fst, retainedSourceChange_fst_assoc,
      retainedSourceChange_snd]
  have h₁ : ι₁ ≫ iB = iB' ≫ ρ₁ :=
    retainedSourceChange_comp_retainedProductInclusion b b' α rfl (f ≫ π) v
  have h₂ : ι₂ ≫ iA = iA' ≫ τ := by
    rw [hτ]
    exact retainedSourceChange_comp_retainedProductInclusion bA b' (α ≫ p) hK π (a ≫ jA)
  let I₁ := zeroScheme _ L₁ c₁.aS
  let J₁ := zeroScheme _ c₁.T c₁.bS
  let I₂ := zeroScheme _ L₂ c₂.aS
  let J₂ := zeroScheme _ c₂.T c₂.bS
  have hwhole₁ := SectionData.firstFactors_wholeCartier q (f ≫ π) j p hB a z s hs H
    e d₁ hd₁ ha c₁ v hc₁
  have hwhole₂ := SectionData.firstFactors_wholeCartier q π jA (𝟙 X) hA a z z
    (Category.comp_id z) IsPullback.of_id_snd e d₂ hd₂ ha c₂ (a ≫ jA) hc₂
  have hCycle := principalCycle_eq_pairedLambdaCycle q π f j jA p hRet hB hA a z s hs H e
    d₁ hd₁ d₂ hd₂ ha c₁ c₂ α U r hr ha₁ ha₂ hnorm
    hwhole₁.1.1 hwhole₁.2.1 hwhole₂.1.1 hwhole₂.2.1
  change _ = finiteCyclePushforward F'
      (cartierCycle (I₁.comap ρ₁) - cartierCycle (J₁.comap ρ₁)) -
    (cartierCycle (I₂.comap τ) - cartierCycle (J₂.comap τ)) at hCycle
  have hFinite₁ := c₁.retainedFirstFactors_comap_finite_relativeCartier v hc₁
  have hFinite₂ := c₂.retainedFirstFactors_comap_finite_relativeCartier (a ≫ jA) hc₂
  have : IsFinite ((I₁.comap iB).subschemeι ≫ pullback.fst b rB) := hFinite₁.1.1
  have : IsFinite ((J₁.comap iB).subschemeι ≫ pullback.fst b rB) := hFinite₁.2.1
  have : Flat ((I₁.comap iB).subschemeι ≫ pullback.fst b rB) := hFinite₁.1.2.2
  have : Flat ((J₁.comap iB).subschemeι ≫ pullback.fst b rB) := hFinite₁.2.2.2
  have : IsFinite ((I₂.comap iA).subschemeι ≫ pullback.fst bA rA) := hFinite₂.1.1
  have : IsFinite ((J₂.comap iA).subschemeι ≫ pullback.fst bA rA) := hFinite₂.2.1
  have : Flat ((I₂.comap iA).subschemeι ≫ pullback.fst bA rA) := hFinite₂.1.2.2
  have : Flat ((J₂.comap iA).subschemeι ≫ pullback.fst bA rA) := hFinite₂.2.2.2
  let : IsFinite (((I₁.comap iB).comap ι₁).subschemeι ≫ pullback.fst b' rB) :=
    retainedSupportSource_isFinite b b' rB α rfl (I₁.comap iB)
  let : IsFinite (((J₁.comap iB).comap ι₁).subschemeι ≫ pullback.fst b' rB) :=
    retainedSupportSource_isFinite b b' rB α rfl (J₁.comap iB)
  let : Flat (((I₁.comap iB).comap ι₁).subschemeι ≫ pullback.fst b' rB) :=
    retainedSupportSource_flat b b' rB α rfl (I₁.comap iB)
  let : Flat (((J₁.comap iB).comap ι₁).subschemeι ≫ pullback.fst b' rB) :=
    retainedSupportSource_flat b b' rB α rfl (J₁.comap iB)
  let : IsFinite (((I₂.comap iA).comap ι₂).subschemeι ≫ pullback.fst b' rA) :=
    retainedSupportSource_isFinite bA b' rA (α ≫ p) hK (I₂.comap iA)
  let : IsFinite (((J₂.comap iA).comap ι₂).subschemeι ≫ pullback.fst b' rA) :=
    retainedSupportSource_isFinite bA b' rA (α ≫ p) hK (J₂.comap iA)
  let : Flat (((I₂.comap iA).comap ι₂).subschemeι ≫ pullback.fst b' rA) :=
    retainedSupportSource_flat bA b' rA (α ≫ p) hK (I₂.comap iA)
  let : Flat (((J₂.comap iA).comap ι₂).subschemeι ≫ pullback.fst b' rA) :=
    retainedSupportSource_flat bA b' rA (α ≫ p) hK (J₂.comap iA)
  let m₁ := productSecondMap b' rA rB g (hg').symm
  have hm₁ : m₁ ≫ iA' = iB' ≫ F' := by
    apply pullback.hom_ext <;>
      simp only [m₁, Category.assoc, productSecondMap_fst,
        productSecondMap_snd_assoc, retainedProductInclusion_fst, retainedProductInclusion_snd,
        retainedProductInclusion_snd_assoc, hg]
  have hsrc (I : (pullback b (f ≫ π)).IdealSheafData)
      [IsFinite ((I.comap iB).subschemeι ≫ pullback.fst b rB)]
      [Flat ((I.comap iB).subschemeι ≫ pullback.fst b rB)]
      (hI : Set.range I.subschemeι ⊆ Set.range iB) :
      let D := (I.comap iB).comap ι₁
      letI := retainedSupportSource_isFinite b b' rB α rfl (I.comap iB)
      letI := retainedSupportSource_flat b b' rB α rfl (I.comap iB)
      letI := isNoetherian_of_finiteType (D.subschemeι ≫ pullback.fst b' rB)
      letI := Cor.isFinite_relativeSupportTargetMap b' rB rA D g hg'
      ∀ x : A', finiteCyclePushforward (D.subschemeι ≫ m₁)
        (AlgebraicCycle.fundamentalCycle D.subscheme) x =
          finiteCyclePushforward F' (cartierCycle (I.comap ρ₁)) (iA' x) := by
    dsimp only
    let D := (I.comap iB).comap ι₁
    let := retainedSupportSource_isFinite b b' rB α rfl (I.comap iB)
    let := retainedSupportSource_flat b b' rB α rfl (I.comap iB)
    let := isNoetherian_of_finiteType (D.subschemeι ≫ pullback.fst b' rB)
    let := Cor.isFinite_relativeSupportTargetMap b' rB rA D g hg'
    intro x
    have hD : D = (I.comap ρ₁).comap iB' :=
      (IdealSheafData.comap_comp I ι₁ iB).symm.trans
        ((congrArg (fun w ↦ I.comap w) h₁).trans (IdealSheafData.comap_comp I iB' ρ₁))
    obtain ⟨eD, heD⟩ := exists_openSupportIso iB' (I.comap ρ₁) D hD
      (wholeSupport_sourceChange b b' α rfl (f ≫ π) v I hI)
    exact (finiteCyclePushforward_cartierCycle_apply_of_supportIso (I.comap ρ₁) F' iA'
      (D.subschemeι ≫ m₁) eD (by
        rw [Category.assoc, hm₁, ← Category.assoc D.subschemeι iB' F', ← heD,
          Category.assoc]) x).symm
  have htgt (I : (pullback bA π).IdealSheafData) (hI : IsEffectiveCartierDivisor I) (x : A') :
      cartierCycle ((I.comap iA).comap ι₂) x = cartierCycle (I.comap τ) (iA' x) := by
    rw [← IdealSheafData.comap_comp, h₂, IdealSheafData.comap_comp]
    let : Flat τ := hτ.symm ▸ MorphismProperty.of_isPullback
      (retainedSourceChange_isPullback bA b' π (α ≫ p) hK).flip inferInstance
    exact cartierCycle_apply_of_isOpenImmersion _ (isPullbackDefined_of_flat τ I hI) iA' x
  let f₀ := (pullback.fst b' π)
  let r₀ := (ρ₂).app U r
  let hr₀ := hr.map ((ρ₂).app U).hom
  have hm₀ : m ≫ pullback.fst (K₀).hom (A₀).hom = iA' ≫ f₀ :=
    (forgetBaseProductMap_fst t b' rA).trans (retainedProductInclusion_fst b' π (a ≫ jA)).symm
  have hPrincipal := correspondence_val_eq_pushforward_of_closed (X := K₀) (Y := A₀)
    f₀ iA' W hW r₀ hr₀ (pullback.snd b' rA) hBase m hm₀
    (forgetBaseProductMap_snd t b' rA)
  let sourceSpan (I : (pullback b rB).IdealSheafData)
      [IsFinite (I.subschemeι ≫ pullback.fst b rB)]
      [Flat (I.subschemeι ≫ pullback.fst b rB)] : Cor.mk Y₀ ⟶ Cor.mk V₀ :=
    Cor.ofFiniteFlatSpan (I.subschemeι ≫ pullback.fst b rB)
      (I.subschemeι ≫ pullback.snd b rB) (Cor.relativeSupport_legs_over_base b rB t I)
  let targetSpan (I : (pullback bA rA).IdealSheafData)
      [IsFinite (I.subschemeι ≫ pullback.fst bA rA)]
      [Flat (I.subschemeι ≫ pullback.fst bA rA)] : Cor.mk X₀ ⟶ Cor.mk A₀ :=
    Cor.ofFiniteFlatSpan (I.subschemeι ≫ pullback.fst bA rA)
      (I.subschemeι ≫ pullback.snd bA rA) (Cor.relativeSupport_legs_over_base bA rA t I)
  have hLambdaB : c₁.lambda t v hc₁ = sourceSpan (I₁.comap iB) - sourceSpan (J₁.comap iB) := rfl
  have hLambdaA : c₂.lambda t (a ≫ jA) hc₂ = targetSpan (I₂.comap iA) - targetSpan (J₂.comap iA) :=
    rfl
  apply Subtype.ext
  rw [hPrincipal, hLambdaB, hLambdaA, Preadditive.comp_sub, Preadditive.sub_comp,
    Preadditive.comp_sub]
  dsimp only [sourceSpan, targetSpan]
  rw [Cor.graph_comp_retainedSupport t b b' rB α rfl (I₁.comap iB),
    Cor.graph_comp_retainedSupport t b b' rB α rfl (J₁.comap iB),
    Cor.graph_comp_retainedSupport t bA b' rA (α ≫ p) hK (I₂.comap iA),
    Cor.graph_comp_retainedSupport t bA b' rA (α ≫ p) hK (J₂.comap iA)]
  change (finiteCorrespondences (K₀).hom (A₀).hom).subtype (_ - _) = _
  rw [map_sub, map_sub, map_sub]
  have hValB₁ := Cor.ofFiniteFlatSpan_relativeCycle_comp_graph_val t b' rB rA
    ((I₁.comap iB).comap ι₁) g hg'
  have hValB₂ := Cor.ofFiniteFlatSpan_relativeCycle_comp_graph_val t b' rB rA
    ((J₁.comap iB).comap ι₁) g hg'
  have hValA₁ := Cor.ofFiniteFlatSpan_relativeCycle_val t b' rA ((I₂.comap iA).comap ι₂)
  have hValA₂ := Cor.ofFiniteFlatSpan_relativeCycle_val t b' rA ((J₂.comap iA).comap ι₂)
  refine (congrArg₂ Sub.sub (congrArg₂ Sub.sub hValB₁ hValB₂)
    (congrArg₂ Sub.sub hValA₁ hValA₂)).trans ?_
  let push := finiteCyclePushforward m
  change (push _ - push _) - (push _ - push _) = push _
  have hmap (c d : AlgebraicCycle A' ℤ) : push c - push d = push (c - d) :=
    (map_sub push c d).symm
  simp only [hmap]
  apply congrArg push
  apply Function.locallyFinsuppWithin.ext
  intro x
  simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, principalCycle_apply,
    ord_dominantFunctionFieldMap_of_isOpenImmersion]
  have hB := congrArg₂ Sub.sub (hsrc I₁ hwhole₁.1.2 x) (hsrc J₁ hwhole₁.2.2 x)
  have hA := congrArg₂ Sub.sub (htgt I₂ hwhole₂.1.1 x) (htgt J₂ hwhole₂.2.1 x)
  have hCoeff := congrArg (fun d ↦ d (iA' x)) hCycle
  simp only [map_sub, Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply,
    principalCycle_apply] at hCoeff
  exact (congrArg₂ Sub.sub hB hA).trans hCoeff.symm

set_option maxHeartbeats 400000 in
-- The component correspondence retains the dependent section coefficients.
include hRet hg hc₁ hc₂ in
/-- The normalized boundary unit makes the exact original E3 difference act
by zero on the specified integral parameter component. -/
theorem transfer_componentLambdaDifference_eq_zero
    (Pst : PresheafWithTransfers.{w} k) (hPst : Pst.IsA1Invariant)
    (r : Γ(pullback b π, U)) (hr : IsUnit r) {D : Scheme.{u}} [Nonempty D]
    (l : D ⟶ (W).toScheme) (hcover : (Set.range iA')ᶜ ⊆ Set.range (l ≫ (W).ι))
    (hl : l.appTop ((W).topIso.inv ((ρ₂).app U r)) = 1) :
    letI := c₁.T_invertible
    letI := c₂.T_invertible
    letI : IsFiniteLocallyFree (pullback.snd F U.ι) :=
      isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback F U.ι) inferInstance
    ∀ (ha₁ : graphNumeratorGeneratesOnPullback w₁ Δ₁ c₁.T c₁.aS)
      (ha₂ : graphNumeratorGeneratesOnPullback w₂ Δ₂ c₂.T c₂.aS),
    normTop (pullback.snd F U.ι)
        (graphSectionRatioCoefficientOfGenerating w₁ Δ₁ c₁.T c₁.aS c₁.bS ha₁) *
        U.topIso.inv r = graphSectionRatioCoefficientOfGenerating w₂ Δ₂ c₂.T c₂.aS c₂.bS ha₂ →
    Pst.transfer ((((Cor.graphFunctor k).map α₀ ≫ c₁.lambda t v hc₁) ≫
        (Cor.graphFunctor k).map g₀) -
        (Cor.graphFunctor k).map p₀ ≫ c₂.lambda t (a ≫ jA) hc₂) = 0 := by
  let := c₁.T_invertible
  let := c₂.T_invertible
  let : IsFiniteLocallyFree (pullback.snd F U.ι) :=
    isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback F U.ι) inferInstance
  intro ha₁ ha₂ hnorm
  let : IsAffine (K₀).left := inferInstanceAs (IsAffine K)
  let : IsIntegral (K₀).left := inferInstanceAs (IsIntegral K)
  let : IsAffine A' := retainedProduct_affine b' π (a ≫ jA)
  let : IsNoetherian A' :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian iA'
      toCompactSpace := inferInstance }
  let : SmoothOfRelativeDimension 1 (iA' ≫ pullback.fst b' π) :=
    retainedProduct_smooth b' π (a ≫ jA)
  let hW := canonical_boundary_cover iA' W l hcover
  rw [componentLambdaDifference_eq_principal t q π f j jA p hRet hB hA a z s hs H e
    d₁ hd₁ d₂ hd₂ ha c₁ c₂ α v g hg hc₁ hc₂ U r hr hW ha₁ ha₂ hnorm]
  exact PresheafWithTransfers.transfer_principalOrder_open_eq_zero Pst hPst K₀ A₀
    (pullback.fst b' π) iA' W ((ρ₂).app U r) (hr.map ((ρ₂).app U).hom) l hcover hl
    (pullback.snd b' rA) hBase

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
