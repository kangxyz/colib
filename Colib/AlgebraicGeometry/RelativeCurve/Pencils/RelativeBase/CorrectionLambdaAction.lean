/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedGraphSpan
public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedZeroSourceChange
public import Colib.AlgebraicGeometry.Correspondences.Moving.PrincipalOrderOpenPushforward
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.OpenRestriction
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeCycle
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeIdealProduct
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Actions.PrincipalOrder
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ParameterBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionNormCycle
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SectionCorrespondences
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.WholeSectionCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumPullback

/-!
# The original correction action on the puncture

The second norm unit has divisor equal to the target lambda minus the source
correction and the original graph. The whole Cartier zero schemes supply
their actual multiplicities, including all residue degrees.

Adapted from `NativeCorrectionNormAction.lean` under
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

open Cor.PrincipalOrder PresheafWithTransfers

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

local instance {U : Scheme.{u}} (D : U.IdealSheafData) [IsEffectiveCartierDivisor D] :
    IsInvertibleModule U (divisorSheaf D) := Stacks.Divisors.isInvertible_divisorSheaf D

/-- The retained target projection preserves the actual structure map. -/
theorem correctionRetainedMap_over_base {k : Type u} [Field k] {S X P A : Scheme.{u}}
    (t : S ⟶ Spec (.of k)) (q : X ⟶ S) (π : P ⟶ S) (j : X ⟶ P) (a : A ⟶ X) :
    retainedProductInclusion (a ≫ q) π (a ≫ j) ≫ pullback.fst (a ≫ q) π ≫ (a ≫ q) ≫ t =
      pullback.snd (a ≫ q) ((a ≫ j) ≫ π) ≫ ((a ≫ j) ≫ π) ≫ t :=
  (retainedProductInclusion_fst_assoc (a ≫ q) π (a ≫ j) ((a ≫ q) ≫ t)).trans
    (pullback.condition_assoc (f := a ≫ q) (g := (a ≫ j) ≫ π) t)

variable {k : Type u} [Field k] {S X Y P C A Z D₁ D₂ V : Scheme.{u}}
  [IsAffine S] [IsAffine X] [IsAffine A] [IsIntegral A] [IsAffine V]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsProper π] [SmoothOfRelativeDimension 1 π] (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a] [SmoothOfRelativeDimension 1 ((a ≫ jA) ≫ π)]
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d₁ : D₁ ⟶ C) (hd₁ : Disjoint (Set.range j) (Set.range d₁))
  (d₂ : D₂ ⟶ P) [IsClosedImmersion (z ≫ jA)]
  (hd₂ : Disjoint (Set.range jA) (Set.range d₂))
  (ha : Disjoint (Set.range a) (Set.range z))
  (c₁ : SectionData q (f ≫ π) j p hB a z s hs H e d₁ hd₁ ha)
  (c₂ : SectionData q π jA (𝟙 X) hA a z z (Category.comp_id z) (IsPullback.of_id_snd)
    e d₂ hd₂ ha)
  (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ f ≫ π)]
  (g : V ⟶ A) (hg : v ≫ f = g ≫ (a ≫ jA))
  (hc₁ : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d₁ ∨ x ∈ Set.range (s ≫ j))
  (hc₂ : ∀ x : P, x ∈ Set.range (a ≫ jA) ∨ x ∈ Set.range d₂ ∨
    x ∈ Set.range (z ≫ jA))

local notation "b" => (a ≫ q)
local notation "bA" => (jA ≫ π)
local notation "rB" => (v ≫ f ≫ π)
local notation "rA" => ((a ≫ jA) ≫ π)
local notation "F" => (retainedProductInclusion b π f)
local notation "zA" => (z ≫ jA)
local notation "hA₀" => (hA.trans (Category.id_comp q))
local notation "τ" => (correctionTargetParameterMap q π jA hA₀ a)
local notation "hmark" => (markedSection_original_equation f j zA s
  (pairedMark_isPullback f j jA p hRet z s H))
local notation "T₀" => (pullback b π : Scheme)
local notation "A'" => (retainedProduct b π (a ≫ jA))
local notation "iB" => (retainedProductInclusion b (f ≫ π) v)
local notation "iA" => (retainedProductInclusion bA π (a ≫ jA))
local notation "iA'" => (retainedProductInclusion b π (a ≫ jA))
local notation "Δ₂" => (Hom.ker (compactificationGraph π jA))
local notation "L₂" => (tensorModules (divisorSheaf Δ₂) (SectionData.T c₂))
local notation "pole" => (tensorSection (divisorSheaf Δ₂) (SectionData.T c₂) ⊤
  (divisorSheafGlobalSection Δ₂) (SectionData.bS c₂))

local instance smoothCorrectionLambdaProjection : Smooth q := SmoothOfRelativeDimension.smooth 1 q
local instance smoothCorrectionLambdaParameter : Smooth bA := SmoothOfRelativeDimension.smooth 1 bA
local instance smoothCorrectionLambdaRetainedSource : Smooth rB :=
  SmoothOfRelativeDimension.smooth 1 rB
local instance smoothCorrectionLambdaRetainedTarget : Smooth rA :=
  SmoothOfRelativeDimension.smooth 1 rA

local notation "A₀" => (SmoothSite.mk (b ≫ t))
local notation "X₀" => (SmoothSite.mk (bA ≫ t))
local notation "V₀" => (SmoothSite.mk (rB ≫ t))
local notation "A₁" => (SmoothSite.mk (rA ≫ t))

local notation "ha₀" => (congrArg (a ≫ ·) hA₀)
local notation "hg'" => (show g ≫ rA = rB from by
  rw [← Category.assoc g (a ≫ jA) π, ← hg, Category.assoc])
local notation "g₀" => (SmoothSite.homMk (X := V₀) (Y := A₁) g
  ((Category.assoc g rA t).symm.trans (congrArg (fun w ↦ w ≫ t) hg')))
local notation "a₀" => (SmoothSite.homMk (X := A₀) (Y := X₀) a
  ((Category.assoc a bA t).symm.trans (congrArg (fun w ↦ w ≫ t) ha₀)))
local notation "id₀" => (SmoothSite.homMk (X := A₀) (Y := A₁) (𝟙 A)
  ((Category.id_comp (rA ≫ t)).trans
    (congrArg (fun w ↦ w ≫ t) ((Category.assoc a jA π).trans ha₀))))

set_option cleanup.letToHave false

section Correspondence

omit [IsClosedImmersion (z ≫ jA)]
include hc₁ hc₂ hg

set_option maxHeartbeats 1100000 in
-- Compare the entire Cartier supports before evaluating the cycles.
/-- The two native signed corrections and the original graph have the
principal correspondence of the actual correction norm unit. -/
theorem correctionLambdaDifference_eq_principal
    [IsIntegral (pullback (a ≫ q) π)] [IsNoetherian A] [IsNoetherian X]
    [IsNoetherian (pullback (a ≫ q) π)] [IsNoetherian (pullback (a ≫ q) (f ≫ π))]
    [IsNoetherian (retainedProduct (a ≫ q) π (a ≫ jA))]
    (U : (pullback b π : Scheme.{u}).Opens) [Nonempty U] (r : Γ(T₀, U)) (hr : IsUnit r)
    (hW : (Set.range iA')ᶜ ⊆ (U : Set T₀))
    (hL : IsInvertibleModule (pullback bA π) L₂) :
    letI := c₁.N_invertible
    letI := c₂.T_invertible
    letI : IsAffine (A₀).left := inferInstanceAs (IsAffine A)
    letI : IsAffine A' := retainedProduct_affine b π (a ≫ jA)
    letI : SmoothOfRelativeDimension 1 (iA' ≫ pullback.fst b π) :=
      retainedProduct_smooth b π (a ≫ jA)
    let I := @AlgebraicGeometry.zeroScheme _ c₁.N c₁.N_invertible c₁.nS
    let J := @AlgebraicGeometry.zeroScheme _ c₁.N c₁.N_invertible c₁.dS
    let I₂ := @AlgebraicGeometry.zeroScheme _ L₂ hL c₂.aS
    let J₂ := @AlgebraicGeometry.zeroScheme _ c₂.T c₂.T_invertible c₂.bS
    let γ := relativeGraph b π (a ≫ jA) ((Category.assoc a jA π).trans ha₀)
    principalCycle T₀ ((T₀).germToFunctionField U r) =
        (cartierCycle (I₂.comap τ) - cartierCycle (J₂.comap τ)) -
          (finiteCyclePushforward F (cartierCycle J) - finiteCyclePushforward F (cartierCycle I)) -
          cartierCycle γ.ker →
    ((Cor.graphFunctor k).map a₀ ≫ c₂.lambda t (a ≫ jA) hc₂ -
      c₁.psi t v hc₁ ≫ (Cor.graphFunctor k).map g₀) - (Cor.graphFunctor k).map id₀ =
      correspondence (X := A₀) (Y := A₁) (pullback.fst b π) iA' U hW r hr
        (pullback.snd b rA) (correctionRetainedMap_over_base t q π jA a) := by
  dsimp only
  intro hDiv
  let := c₁.N_invertible
  let := c₂.T_invertible
  let : IsAffine (A₀).left := inferInstanceAs (IsAffine A)
  let : IsIntegral (A₀).left := inferInstanceAs (IsIntegral A)
  let : IsAffine A' := retainedProduct_affine b π (a ≫ jA)
  let : SmoothOfRelativeDimension 1 (iA' ≫ pullback.fst b π) :=
    retainedProduct_smooth b π (a ≫ jA)
  let γ' := relativeGraph b rA (𝟙 A) (by rw [Category.id_comp, Category.assoc, ha₀])
  let γ := relativeGraph b π (a ≫ jA) (by rw [Category.assoc, ha₀])
  let : Nonempty A' := ⟨γ' (genericPoint A)⟩
  let : IsIntegral A' := isIntegral_of_isOpenImmersion iA'
  let : IsDominant iA' :=
    ((tfae_isDominant_of_isIntegral iA').out 1 2).mpr (genericPoint_eq_of_isOpenImmersion iA')
  have hγ : γ' ≫ iA' = γ := by
    apply pullback.hom_ext <;> simp only [γ', γ, Category.assoc, retainedProductInclusion_fst,
      retainedProductInclusion_snd, relativeGraph_fst, relativeGraph_snd,
      relativeGraph_snd_assoc, Category.id_comp]
  have hτ : τ = retainedSourceChange bA b π a ha₀ := by
    apply pullback.hom_ext <;> simp only [correctionTargetParameterMap_fst,
      correctionTargetParameterMap_snd, retainedSourceChange_fst, retainedSourceChange_snd]
  let : Flat τ := hτ.symm ▸ MorphismProperty.of_isPullback
    (retainedSourceChange_isPullback bA b π a ha₀).flip inferInstance
  have hΔ : γ.ker = (Δ₂).comap τ := by
    rw [hτ]
    exact ker_eq_comap_of_cartesian
      (relativeGraph_sourceChange_isPullback bA b a ha₀ π jA rfl).flip
  have hγret : γ'.ker = γ.ker.comap iA' := by
    have H' : IsPullback γ' (𝟙 A) iA' γ :=
      IsPullback.of_vert_isIso_mono ⟨by rw [hγ, Category.id_comp]⟩
    exact ker_eq_comap_of_cartesian H'
  let : IsInvertibleModule (pullback bA π) L₂ := hL
  let I := zeroScheme _ c₁.N c₁.nS
  let J := zeroScheme _ c₁.N c₁.dS
  let I₂ := zeroScheme _ L₂ c₂.aS
  let J₂ := zeroScheme _ c₂.T c₂.bS
  have hwhole := SectionData.correctionFactors_wholeCartier q (f ≫ π) j p hB a z s hs H
    e d₁ hd₁ ha c₁ v hc₁
  have hwhole₂ := SectionData.firstFactors_wholeCartier q π jA (𝟙 X) hA a z z
    (Category.comp_id z) IsPullback.of_id_snd e d₂ hd₂ ha c₂ (a ≫ jA) hc₂
  have hΔ₂ := isPullbackDefined_of_flat τ Δ₂ inferInstance
  let u := retainedSourceChange bA b rA a ha₀
  have hu : u ≫ iA = iA' ≫ τ := by
    rw [hτ]
    exact retainedSourceChange_comp_retainedProductInclusion bA b a ha₀ π (a ≫ jA)
  let mB := productSecondMap b rA rB g (hg').symm
  have hmB : mB ≫ iA' = iB ≫ F := by
    apply pullback.hom_ext <;>
      simp only [mB, Category.assoc, productSecondMap_fst,
        productSecondMap_snd_assoc, retainedProductInclusion_fst, retainedProductInclusion_snd,
        retainedProductInclusion_snd_assoc, hg]
  have hFinite := c₁.retainedCorrectionFactors_comap_finite_relativeCartier v hc₁
  have hFinite₂ := c₂.retainedFirstFactors_comap_finite_relativeCartier (a ≫ jA) hc₂
  have : IsFinite ((I.comap iB).subschemeι ≫ pullback.fst b rB) := hFinite.1.1
  have : Flat ((I.comap iB).subschemeι ≫ pullback.fst b rB) := hFinite.1.2.2
  have : IsFinite ((J.comap iB).subschemeι ≫ pullback.fst b rB) := hFinite.2.1
  have : Flat ((J.comap iB).subschemeι ≫ pullback.fst b rB) := hFinite.2.2.2
  have : IsFinite ((I₂.comap iA).subschemeι ≫ pullback.fst bA rA) := hFinite₂.1.1
  have : Flat ((I₂.comap iA).subschemeι ≫ pullback.fst bA rA) := hFinite₂.1.2.2
  have : IsFinite ((J₂.comap iA).subschemeι ≫ pullback.fst bA rA) := hFinite₂.2.1
  have : Flat ((J₂.comap iA).subschemeι ≫ pullback.fst bA rA) := hFinite₂.2.2.2
  let : IsFinite (((I₂.comap iA).comap u).subschemeι ≫ pullback.fst b rA) :=
    retainedSupportSource_isFinite bA b rA a ha₀ (I₂.comap iA)
  let : IsFinite (((J₂.comap iA).comap u).subschemeι ≫ pullback.fst b rA) :=
    retainedSupportSource_isFinite bA b rA a ha₀ (J₂.comap iA)
  let : Flat (((I₂.comap iA).comap u).subschemeι ≫ pullback.fst b rA) :=
    retainedSupportSource_flat bA b rA a ha₀ (I₂.comap iA)
  let : Flat (((J₂.comap iA).comap u).subschemeι ≫ pullback.fst b rA) :=
    retainedSupportSource_flat bA b rA a ha₀ (J₂.comap iA)
  have hsrc (I₀ : (pullback b (f ≫ π)).IdealSheafData)
      [IsFinite ((I₀.comap iB).subschemeι ≫ pullback.fst b rB)]
      (hI : Set.range I₀.subschemeι ⊆ Set.range iB) :
      let D := I₀.comap iB
      letI := Cor.isFinite_relativeSupportTargetMap b rB rA D g hg'
      letI := isNoetherian_of_finiteType (D.subschemeι ≫ pullback.fst b rB)
      ∀ x : A', finiteCyclePushforward (D.subschemeι ≫ mB)
        (AlgebraicCycle.fundamentalCycle D.subscheme) x =
          finiteCyclePushforward F (cartierCycle I₀) (iA' x) := by
    dsimp only
    let D := I₀.comap iB
    let := Cor.isFinite_relativeSupportTargetMap b rB rA D g hg'
    let := isNoetherian_of_finiteType (D.subschemeι ≫ pullback.fst b rB)
    intro x
    obtain ⟨eD, heD⟩ := exists_openSupportIso iB I₀ D rfl hI
    exact (finiteCyclePushforward_cartierCycle_apply_of_supportIso I₀ F iA'
      (D.subschemeι ≫ mB) eD (by
        rw [Category.assoc, hmB, ← Category.assoc D.subschemeι iB F, ← heD,
          Category.assoc]) x).symm
  have htgt (I₀ : (pullback bA π).IdealSheafData)
      (hI : IsEffectiveCartierDivisor I₀) (x : A') :
      cartierCycle ((I₀.comap iA).comap u) x = cartierCycle (I₀.comap τ) (iA' x) := by
    rw [← IdealSheafData.comap_comp, hu, IdealSheafData.comap_comp]
    exact cartierCycle_apply_of_isOpenImmersion _ (isPullbackDefined_of_flat τ I₀ hI) iA' x
  have hγcycle (x : A') : cartierCycle γ'.ker x = cartierCycle γ.ker (iA' x) := by
    rw [hγret]
    exact cartierCycle_apply_of_isOpenImmersion _
      ((congrArg IsEffectiveCartierDivisor hΔ).mpr hΔ₂) iA' x
  let m : A' ⟶ pullback (b ≫ t) (rA ≫ t) := forgetBaseProductMap t b rA
  let : IsClosedImmersion m := inferInstanceAs (IsClosedImmersion (forgetBaseProductMap t b rA))
  have hm₁ : m ≫ pullback.fst (b ≫ t) (rA ≫ t) = iA' ≫ pullback.fst b π :=
    (forgetBaseProductMap_fst t b rA).trans (retainedProductInclusion_fst b π (a ≫ jA)).symm
  have hm₂ : m ≫ pullback.snd (b ≫ t) (rA ≫ t) = pullback.snd b rA :=
    forgetBaseProductMap_snd t b rA
  let δ : Cor.mk A₀ ⟶ Cor.mk A₁ :=
    (Cor.graphFunctor k).map a₀ ≫ c₂.lambda t (a ≫ jA) hc₂ -
      c₁.psi t v hc₁ ≫ (Cor.graphFunctor k).map g₀
  have hbase : iA' ≫ pullback.fst b π ≫ (A₀).hom = pullback.snd b rA ≫ (A₁).hom :=
    correctionRetainedMap_over_base t q π jA a
  let principal : Cor.mk A₀ ⟶ Cor.mk A₁ :=
    correspondence (X := A₀) (Y := A₁) (pullback.fst b π) iA' U hW r hr
      (pullback.snd b rA) hbase
  have hPrincipal : principal.val =
      finiteCyclePushforward m (principalCycle A'
        (dominantFunctionFieldMap iA' ((T₀).germToFunctionField U r))) :=
    correspondence_val_eq_pushforward_of_closed (X := A₀) (Y := A₁)
      (pullback.fst b π) iA' U hW r hr (pullback.snd b rA) hbase m hm₁ hm₂
  have hφ : (𝟙 A) ≫ rA = b := by rw [Category.id_comp, Category.assoc, ha₀]
  let G := relativeGraphIdeal b rA (𝟙 A) hφ
  let eG := relativeGraphSupportIso b rA (𝟙 A) hφ
  have heG : eG.hom = G.subschemeι ≫ pullback.fst b rA :=
    relativeGraphSupportIso_hom_base b rA (𝟙 A) hφ
  let : IsFinite (G.subschemeι ≫ pullback.fst b rA) :=
    (congrArg IsFinite heG).mp (inferInstanceAs (IsFinite eG.hom))
  let : Flat (G.subschemeι ≫ pullback.fst b rA) :=
    (congrArg Flat heG).mp (inferInstanceAs (Flat eG.hom))
  let originalMap : A₀ ⟶ A₁ := id₀
  let graph : Cor.mk A₀ ⟶ Cor.mk A₁ := (Cor.graphFunctor k).map originalMap
  have hId : (𝟙 A) ≫ (b ≫ t) = (𝟙 A) ≫ (rA ≫ t) :=
    (Category.id_comp _).trans (MorphismProperty.Over.w originalMap).symm
  have hGraphId : Cor.ofFiniteFlatSpanRaw (b ≫ t) (rA ≫ t) (𝟙 A) (𝟙 A) hId =
      (Cor.graphFunctor k).map originalMap :=
    Cor.ofFiniteFlatSpan_id_left (k := k) originalMap
  have hGraph : Cor.retainedIdealSpan (k := k) t b rA G = graph :=
    (Cor.ofFiniteFlatSpanRaw_relativeGraph_eq_id_left t b rA (𝟙 A) hφ hId).trans hGraphId
  let correctionSpan (I₀ : (pullback b rB).IdealSheafData)
      [IsFinite (I₀.subschemeι ≫ pullback.fst b rB)]
      [Flat (I₀.subschemeι ≫ pullback.fst b rB)] : Cor.mk A₀ ⟶ Cor.mk V₀ :=
    Cor.ofFiniteFlatSpan (I₀.subschemeι ≫ pullback.fst b rB)
      (I₀.subschemeι ≫ pullback.snd b rB) (Cor.relativeSupport_legs_over_base b rB t I₀)
  let targetSpan (I₀ : (pullback bA rA).IdealSheafData)
      [IsFinite (I₀.subschemeι ≫ pullback.fst bA rA)]
      [Flat (I₀.subschemeι ≫ pullback.fst bA rA)] : Cor.mk X₀ ⟶ Cor.mk A₁ :=
    Cor.ofFiniteFlatSpan (I₀.subschemeι ≫ pullback.fst bA rA)
      (I₀.subschemeι ≫ pullback.snd bA rA) (Cor.relativeSupport_legs_over_base bA rA t I₀)
  have hψ : c₁.psi t v hc₁ = correctionSpan (J.comap iB) - correctionSpan (I.comap iB) := rfl
  have hLambda : c₂.lambda t (a ≫ jA) hc₂ = targetSpan (I₂.comap iA) - targetSpan (J₂.comap iA) :=
    rfl
  change δ - graph = principal
  apply Subtype.ext
  rw [hPrincipal, ← hGraph]
  dsimp only [δ]
  rw [hLambda, hψ, Preadditive.comp_sub, Preadditive.sub_comp]
  dsimp only [correctionSpan, targetSpan]
  rw [Cor.graph_comp_retainedSupport t bA b rA a ha₀ (I₂.comap iA),
    Cor.graph_comp_retainedSupport t bA b rA a ha₀ (J₂.comap iA)]
  change (finiteCorrespondences (A₀).hom (A₁).hom).subtype ((_ - _) - _) = _
  rw [map_sub, map_sub, map_sub, map_sub]
  have hValA₁ := Cor.ofFiniteFlatSpan_relativeCycle_val t b rA ((I₂.comap iA).comap u)
  have hValA₂ := Cor.ofFiniteFlatSpan_relativeCycle_val t b rA ((J₂.comap iA).comap u)
  have hValB₁ := Cor.ofFiniteFlatSpan_relativeCycle_comp_graph_val t b rB rA
    (J.comap iB) g hg'
  have hValB₂ := Cor.ofFiniteFlatSpan_relativeCycle_comp_graph_val t b rB rA
    (I.comap iB) g hg'
  have hValGraph := Cor.ofFiniteFlatSpan_relativeCycle_val t b rA G
  refine (congrArg₂ Sub.sub (congrArg₂ Sub.sub (congrArg₂ Sub.sub hValA₁ hValA₂)
    (congrArg₂ Sub.sub hValB₁ hValB₂)) hValGraph).trans ?_
  let push := finiteCyclePushforward m
  change ((push _ - push _) - (push _ - push _)) - push _ = push _
  have hmap (c d : AlgebraicCycle A' ℤ) : push c - push d = push (c - d) :=
    (map_sub push c d).symm
  simp only [hmap]
  apply congrArg push
  apply Function.locallyFinsuppWithin.ext
  intro x
  change ((_ - _) - (_ - _) - cartierCycle γ'.ker) x = _
  simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, principalCycle_apply,
    ord_dominantFunctionFieldMap_of_isOpenImmersion]
  have hA := congrArg₂ Sub.sub (htgt I₂ hwhole₂.1.1 x) (htgt J₂ hwhole₂.2.1 x)
  have hB := congrArg₂ Sub.sub (hsrc J hwhole.2.2 x) (hsrc I hwhole.1.2 x)
  have hCoeff := congrArg (fun d ↦ d (iA' x)) hDiv
  simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, principalCycle_apply] at hCoeff
  exact (congrArg₂ Sub.sub (congrArg₂ Sub.sub hA hB) (hγcycle x)).trans hCoeff.symm

end Correspondence

set_option maxHeartbeats 650000 in
-- The original graph and both signed whole supports are compared in this proof.
/-- The target lambda action minus the correction action is the original
graph action on the puncture. -/
theorem transfer_lambda_sub_correction_eq_graph
    [IsFiniteLocallyFree (retainedProductInclusion (a ≫ q) π f)]
    [IsIntegral (pullback (a ≫ q) π)]
    (bI : pullback f d₂ ⟶ D₁) (hbI : bI ≫ d₁ = pullback.fst f d₂)
    (bE : (residualMarkedFiberOpen f j zA s hmark).toScheme ⟶ D₁)
    (hbE : bE ≫ d₁ = residualMarkedFiberMap f j zA s hmark)
    (Pst : PresheafWithTransfers.{w} k) (hPst : Pst.IsA1Invariant)
    (hInfinity : Function.Surjective (d₂ ≫ π)) :
    let XA : SmoothSite (Spec (.of k)) := A₀
    let XX : SmoothSite (Spec (.of k)) := X₀
    let XV : SmoothSite (Spec (.of k)) := V₀
    let YA : SmoothSite (Spec (.of k)) := A₁
    let openMap : XA ⟶ XX := a₀
    let correctionMap : XV ⟶ YA := g₀
    let originalMap : XA ⟶ YA := id₀
    let lambdaA : Cor.mk XX ⟶ Cor.mk YA := c₂.lambda t (a ≫ jA) hc₂
    let psiB : Cor.mk XA ⟶ Cor.mk XV := c₁.psi t v hc₁
    let target : Cor.mk XA ⟶ Cor.mk YA := (Cor.graphFunctor k).map openMap ≫ lambdaA
    let source : Cor.mk XA ⟶ Cor.mk YA := psiB ≫ (Cor.graphFunctor k).map correctionMap
    let graph : Cor.mk XA ⟶ Cor.mk YA := (Cor.graphFunctor k).map originalMap
    Pst.transfer (target - source) = Pst.transfer graph := by
  dsimp only
  let := c₁.N_invertible
  let := c₂.T_invertible
  let : IsAffine (A₀).left := inferInstanceAs (IsAffine A)
  let : IsIntegral (A₀).left := inferInstanceAs (IsIntegral A)
  let : IsNoetherian A := inferInstanceAs (IsNoetherian (A₀).left)
  let : IsNoetherian X := inferInstanceAs (IsNoetherian (X₀).left)
  let : IsNoetherian (pullback b (f ≫ π)) :=
    isNoetherian_of_finiteType (pullback.fst b (f ≫ π))
  let : IsNoetherian T₀ := isNoetherian_of_finiteType (pullback.fst b π)
  let : IsNoetherian (pullback bA π) := isNoetherian_of_finiteType (pullback.fst bA π)
  let : IsAffine A' := retainedProduct_affine b π (a ≫ jA)
  let : IsNoetherian A' :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian iA'
      toCompactSpace := inferInstance }
  let : SmoothOfRelativeDimension 1 (iA' ≫ pullback.fst b π) :=
    retainedProduct_smooth b π (a ≫ jA)
  let hD : IsEffectiveCartierDivisor Δ₂ := compactificationGraphIdeal_isEffectiveCartierDivisor π jA
  let hL : IsInvertibleModule (pullback bA π) L₂ :=
    @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf _ (divisorSheaf Δ₂) c₂.T
      (@Stacks.Divisors.isInvertible_divisorSheaf _ Δ₂ hD) c₂.T_invertible
  let : IsInvertibleModule (pullback bA π) L₂ := hL
  let I := zeroScheme _ c₁.N c₁.nS
  let J := zeroScheme _ c₁.N c₁.dS
  let I₂ := zeroScheme _ L₂ c₂.aS
  let J₂ := zeroScheme _ c₂.T c₂.bS
  have hwhole := SectionData.correctionFactors_wholeCartier q (f ≫ π) j p hB a z s hs H
    e d₁ hd₁ ha c₁ v hc₁
  have hwhole₂ := SectionData.firstFactors_wholeCartier q π jA (𝟙 X) hA a z z
    (Category.comp_id z) IsPullback.of_id_snd e d₂ hd₂ ha c₂ (a ≫ jA) hc₂
  obtain ⟨U, hU, r, l, hr, hl, hunit, hDiv⟩ := exists_correctionNormPrincipalCycle
    q π f j jA p hRet hB hA a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂ bI hbI bE hbE
    hL hwhole.1.1 hwhole.2.1 hwhole₂.1.1 hwhole₂.2.1 hInfinity
  let : Nonempty U := hU
  have hcover := wholeBoundary_cover_of_secondFactor b π (a ≫ jA) d₂ zA U l hl hc₂
  have hsurj := wholeBoundary_surjective_firstProjection b π d₂ zA U l hl hInfinity
  let : Nonempty (pullback b (d₂ ≫ π) ⨿ pullback b (zA ≫ π) : Scheme.{u}) :=
    ⟨(hsurj (genericPoint A)).choose⟩
  let hbase := correctionRetainedMap_over_base t q π jA a
  have hCorr := correctionLambdaDifference_eq_principal t q π f j jA p hB hA a z s hs H
    e d₁ hd₁ d₂ hd₂ ha c₁ c₂ v g hg hc₁ hc₂ U r hr
    (canonical_boundary_cover iA' U l hcover) hL hDiv
  have hZero := transfer_principalOrder_open_eq_zero Pst hPst A₀ A₁
    (pullback.fst b π) iA' U r hr l hcover hunit (pullback.snd b rA) hbase
  have heq := congrArg (fun x : Cor.mk A₀ ⟶ Cor.mk A₁ ↦ Pst.transfer x) hCorr
  rw [transfer_sub, hZero] at heq
  exact sub_eq_zero.mp heq

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
