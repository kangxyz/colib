/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedGraphSpan
public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedPencilDifference
public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedZeroSourceChange
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeIdealProduct

/-!
# Signed endpoints from the generated family's exact whole zero ideals

The genuine family may retain any actual invertible-module spelling. Its proven
zero-ideal equations, rather than an artificial replacement of its line module,
are sufficient for the existing whole span additivity and graph-source APIs.
This is an application of those APIs, not a new cycle or span construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

local instance (A : Scheme.{u}) (M : A.Modules) [hM : IsInvertibleModule A M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property M := hM

variable {k : Type u} [Field k] {S X Y : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t] (q : X ⟶ S) (r : Y ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "W" => SmoothSite.mk (r ≫ t)

variable {T V : Scheme.{u}} (qA : T ⟶ S) (qN : V ⟶ S)
  [Smooth (qA ≫ t)] [IsSeparated (qA ≫ t)] [QuasiCompact (qA ≫ t)]
  [Smooth (qN ≫ t)] [IsSeparated (qN ≫ t)] [QuasiCompact (qN ≫ t)]
  [hSepR : IsSeparated r] [SmoothOfRelativeDimension 1 r]
  (α : X ⟶ T) (hα : α ≫ qA = q) [Flat α]
  (β : X ⟶ V) (hβ : β ≫ qN = q) [Flat β]
  (φ : X ⟶ Y) (hφ : φ ≫ r = q)
  (L P : (pullback q r).Modules)
  [IsInvertibleModule (pullback q r) L] [IsInvertibleModule (pullback q r) P]
  (s₀ s₁ : Γ(L, ⊤)) (u : Γ(P, ⊤))
  (IA IB : (pullback qA r).IdealSheafData) (IN ID : (pullback qN r).IdealSheafData)
  [IsFinite (IA.subschemeι ≫ pullback.fst qA r)] [Flat (IA.subschemeι ≫ pullback.fst qA r)]
  [IsFinite (IB.subschemeι ≫ pullback.fst qA r)] [Flat (IB.subschemeι ≫ pullback.fst qA r)]
  [IsFinite (IN.subschemeι ≫ pullback.fst qN r)] [Flat (IN.subschemeι ≫ pullback.fst qN r)]
  [IsFinite (ID.subschemeι ≫ pullback.fst qN r)] [Flat (ID.subschemeι ≫ pullback.fst qN r)]

local notation "jA" => retainedSourceChange qA q r α hα
local notation "jN" => retainedSourceChange qN q r β hβ
local notation "AA" => IA.comap jA
local notation "BB" => IB.comap jA
local notation "NN" => IN.comap jN
local notation "DD" => ID.comap jN
local notation "G" => relativeGraphIdeal q r φ hφ
local notation "Pole" => zeroScheme (pullback q r) P u
local notation "H₀" => zeroScheme (pullback q r) L s₀
local notation "H₁" => zeroScheme (pullback q r) L s₁
local notation "UA" => SmoothSite.mk (qA ≫ t)
local notation "UN" => SmoothSite.mk (qN ≫ t)
local notation "αs" => SmoothSite.homMk (X := U) (Y := UA) α
  (Eq.trans (Eq.symm (Category.assoc α qA t)) (congrArg (fun g => g ≫ t) hα))
local notation "βs" => SmoothSite.homMk (X := U) (Y := UN) β
  (Eq.trans (Eq.symm (Category.assoc β qN t)) (congrArg (fun g => g ≫ t) hβ))
local notation "φs" => SmoothSite.homMk (X := U) (Y := W) φ
  (Eq.trans (Eq.symm (Category.assoc φ r t)) (congrArg (fun g => g ≫ t) hφ))
local notation "lam" => retainedIdealSpan t qA r IA - retainedIdealSpan t qA r IB
local notation "psi" => retainedIdealSpan t qN r ID - retainedIdealSpan t qN r IN

set_option maxHeartbeats 500000 in
-- Elaborate the two endpoints and the four actual flat source changes in one proof.
/-- The arbitrary actual family line is retained. Its proved full zero ideals
suffice to derive both signed endpoints with the two original source maps. -/
theorem retainedIdealDifference_source_endpoints
    (h : RetainedPencilWitnesses (k := k) t q r L P s₀ s₁ u)
    (hA : IsEffectiveCartierDivisor AA) (hB : IsEffectiveCartierDivisor BB)
    (hN : IsEffectiveCartierDivisor NN) (hD : IsEffectiveCartierDivisor DD)
    (hP : IsEffectiveCartierDivisor Pole)
    (h₀ : H₀ = G * Pole) (h₁ : H₁ = AA * NN) (hu : Pole = BB * DD) :
    let δ : Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W :=
      retainedPencilDifferenceFromWitnesses (k := k) t q r L P s₀ s₁ u h
    (graphFunctor k).map (nativeAffineSection (.of k) U 0) ≫ δ = (graphFunctor k).map φs ∧
    (graphFunctor k).map (nativeAffineSection (.of k) U 1) ≫ δ =
      (graphFunctor k).map αs ≫ lam - (graphFunctor k).map βs ≫ psi := by
  let sourceSite : SmoothSite (Spec (.of k)) := U
  let targetSite : SmoothSite (Spec (.of k)) := W
  let graph : sourceSite ⟶ targetSite := φs
  have := retainedSupportSource_isFinite qA q r α hα IA
  have := retainedSupportSource_flat qA q r α hα IA
  have := retainedSupportSource_isFinite qA q r α hα IB
  have := retainedSupportSource_flat qA q r α hα IB
  have := retainedSupportSource_isFinite qN q r β hβ IN
  have := retainedSupportSource_flat qN q r β hβ IN
  have := retainedSupportSource_isFinite qN q r β hβ ID
  have := retainedSupportSource_flat qN q r β hβ ID
  let hZero := nativeRetainedZero_finite_flat (k := k) t q r L s₀ s₁
    (_hFamilyFin := h.familyFinite) (_hFamilyFlat := h.familyFlat)
  let hOne := nativeRetainedOne_finite_flat (k := k) t q r L s₀ s₁
    (_hFamilyFin := h.familyFinite) (_hFamilyFlat := h.familyFlat)
  let := hZero.1
  let := hZero.2
  let := hOne.1
  let := hOne.2
  let := h.poleFinite
  let := h.poleFlat
  have hGraphFin : IsFinite ((G).subschemeι ≫ pullback.fst q r) := by
    rw [← relativeGraphSupportIso_hom_base]
    infer_instance
  have hGraphFlat : Flat ((G).subschemeι ≫ pullback.fst q r) := by
    rw [← relativeGraphSupportIso_hom_base]
    infer_instance
  have hZeroEq := (retainedPencilDifferenceFromWitnesses_zero (k := k) t q r L P s₀ s₁ u h).eq
  have hOneEq := (retainedPencilDifferenceFromWitnesses_one (k := k) t q r L P s₀ s₁ u h).eq
  constructor
  · rw [hZeroEq]
    change retainedIdealSpan t q r H₀ - retainedIdealSpan t q r Pole = _
    rw [retainedSpan_add_of_ideal_product t q r G Pole H₀
        (isLocallyPrincipal_of_isEffectiveCartierDivisor G inferInstance) hP h₀,
      add_sub_cancel_right]
    let : IsNoetherian X := isNoetherian_of_finiteType_of_isNoetherian (q ≫ t)
    let : IsFinite ((G).subschemeι ≫ pullback.fst q r) := hGraphFin
    let : Flat ((G).subschemeι ≫ pullback.fst q r) := hGraphFlat
    have hId : (𝟙 X) ≫ (q ≫ t) = φ ≫ (r ≫ t) := by
      simpa only [Category.id_comp, Category.assoc] using
        (congrArg (fun f => f ≫ t) hφ).symm
    have hGraph : ofFiniteFlatSpanRaw (q ≫ t) (r ≫ t) (𝟙 X) φ hId =
        (graphFunctor k).map graph := ofFiniteFlatSpan_id_left (k := k) graph
    exact (ofFiniteFlatSpanRaw_relativeGraph_eq_id_left t q r φ hφ hId).trans hGraph
  · rw [hOneEq]
    let sourceA : SmoothSite (Spec (.of k)) := UA
    let sourceN : SmoothSite (Spec (.of k)) := UN
    let graphA : sourceSite ⟶ sourceA := αs
    let graphN : sourceSite ⟶ sourceN := βs
    let aSpan : Cor.mk sourceA ⟶ Cor.mk targetSite := retainedIdealSpan (k := k) t qA r IA
    let bSpan : Cor.mk sourceA ⟶ Cor.mk targetSite := retainedIdealSpan (k := k) t qA r IB
    let nSpan : Cor.mk sourceN ⟶ Cor.mk targetSite := retainedIdealSpan (k := k) t qN r IN
    let dSpan : Cor.mk sourceN ⟶ Cor.mk targetSite := retainedIdealSpan (k := k) t qN r ID
    let aaSpan : Cor.mk sourceSite ⟶ Cor.mk targetSite := retainedIdealSpan (k := k) t q r AA
    let bbSpan : Cor.mk sourceSite ⟶ Cor.mk targetSite := retainedIdealSpan (k := k) t q r BB
    let nnSpan : Cor.mk sourceSite ⟶ Cor.mk targetSite := retainedIdealSpan (k := k) t q r NN
    let ddSpan : Cor.mk sourceSite ⟶ Cor.mk targetSite := retainedIdealSpan (k := k) t q r DD
    let numerator : Cor.mk sourceSite ⟶ Cor.mk targetSite := retainedIdealSpan (k := k) t q r H₁
    let pole : Cor.mk sourceSite ⟶ Cor.mk targetSite := retainedIdealSpan (k := k) t q r Pole
    have haSpan : (graphFunctor k).map graphA ≫ aSpan = aaSpan :=
      graph_comp_retainedSupport (k := k) t qA q r α hα IA
    have hbSpan : (graphFunctor k).map graphA ≫ bSpan = bbSpan :=
      graph_comp_retainedSupport (k := k) t qA q r α hα IB
    have hnSpan : (graphFunctor k).map graphN ≫ nSpan = nnSpan :=
      graph_comp_retainedSupport (k := k) t qN q r β hβ IN
    have hdSpan : (graphFunctor k).map graphN ≫ dSpan = ddSpan :=
      graph_comp_retainedSupport (k := k) t qN q r β hβ ID
    have hGraphA : (graphFunctor k).map graphA ≫ (aSpan - bSpan) = aaSpan - bbSpan :=
      (Preadditive.comp_sub _ _ _).trans (congrArg₂ (· - ·) haSpan hbSpan)
    have hGraphN : (graphFunctor k).map graphN ≫ (dSpan - nSpan) = ddSpan - nnSpan :=
      (Preadditive.comp_sub _ _ _).trans (congrArg₂ (· - ·) hdSpan hnSpan)
    have hNumerator : numerator = aaSpan + nnSpan :=
      retainedSpan_add_of_ideal_product t q r AA NN H₁
        (isLocallyPrincipal_of_isEffectiveCartierDivisor AA hA) hN h₁
    have hPole : pole = bbSpan + ddSpan :=
      retainedSpan_add_of_ideal_product t q r BB DD Pole
        (isLocallyPrincipal_of_isEffectiveCartierDivisor BB hB) hD hu
    change numerator - pole =
      (graphFunctor k).map graphA ≫ (aSpan - bSpan) -
        (graphFunctor k).map graphN ≫ (dSpan - nSpan)
    calc
      _ = (aaSpan + nnSpan) - (bbSpan + ddSpan) := congrArg₂ (· - ·) hNumerator hPole
      _ = (aaSpan - bbSpan) - (ddSpan - nnSpan) := by abel
      _ = _ := congrArg₂ (· - ·) hGraphA.symm hGraphN.symm

end AlgebraicGeometry.Cor
