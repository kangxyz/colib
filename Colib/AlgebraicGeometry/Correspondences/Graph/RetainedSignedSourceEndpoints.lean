/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedZeroSourceChange
public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedTensorDifference

/-!
# The actual retained tensor family over two independent sources

The first pair lives over T, the second pair over V, and both pull back to the
common source X. Neither source map is assumed to be an open immersion or the
puncture of the other. The four hypotheses compare actual whole zero ideals
with their actual comaps; `zeroScheme_eq_comap_of_section_iso` supplies these
from section-preserving line comparisons. No correspondence endpoint is an
input. The conclusion identifies the genuine polynomial-family-minus-pole with
both source graphs and retains the original signs.

This is the native version of the signed source endpoint in
`Motivic/AlgebraicGeometry/Correspondences/Moving/Pencils/SignedSourceEndpoints.lean`
(blob `81844c665922764c96de0dd51260c8e7d06c85c5`) and its graph start in
`Motivic/AlgebraicGeometry/Correspondences/Moving/Pencils/DiagonalSigned.lean`
(blob `333aacc7b2dbc1248fa61427314381a069718c3b`), both at
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open Scheme Scheme.PolynomialSectionPencil Scheme.RelativeCurvePencil
open Scheme.SmoothSite.Contraction

variable {k : Type u} [Field k] {S X T V Y : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t]
  (q : X ⟶ S) (qA : T ⟶ S) (qN : V ⟶ S) (r : Y ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (qA ≫ t)] [IsSeparated (qA ≫ t)] [QuasiCompact (qA ≫ t)]
  [Smooth (qN ≫ t)] [IsSeparated (qN ≫ t)] [QuasiCompact (qN ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  [IsSeparated r] [SmoothOfRelativeDimension 1 r]
  (α : X ⟶ T) (hα : α ≫ qA = q) [Flat α]
  (β : X ⟶ V) (hβ : β ≫ qN = q) [Flat β]
  (φ : X ⟶ Y) (hφ : φ ≫ r = q)
  (M N : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property N]

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "UA" => SmoothSite.mk (qA ≫ t)
local notation "UN" => SmoothSite.mk (qN ≫ t)
local notation "W" => SmoothSite.mk (r ≫ t)
local notation "C" => pullback q r
local notation "G" => relativeGraphIdeal q r φ hφ
local notation "F" => divisorSheaf G
local notation "L" => tensorModules (tensorModules F M) N
local notation "LP" => tensorModules M N
local notation "jA" => retainedSourceChange qA q r α hα
local notation "jN" => retainedSourceChange qN q r β hβ
local notation "αs" => (show U ⟶ UA from
  SmoothSite.homMk α (by simp only [← Category.assoc, hα]))
local notation "βs" => (show U ⟶ UN from
  SmoothSite.homMk β (by simp only [← Category.assoc, hβ]))
local notation "φs" => (show U ⟶ W from
  SmoothSite.homMk φ (by simp only [← Category.assoc, hφ]))

variable (a : Γ(tensorModules F M, ⊤)) (b : Γ(M, ⊤)) (n d : Γ(N, ⊤))
  (IA IB : (pullback qA r).IdealSheafData) (IN ID : (pullback qN r).IdealSheafData)
  [IsFinite (IA.subschemeι ≫ pullback.fst qA r)]
  [Flat (IA.subschemeι ≫ pullback.fst qA r)]
  [IsFinite (IB.subschemeι ≫ pullback.fst qA r)]
  [Flat (IB.subschemeι ≫ pullback.fst qA r)]
  [IsFinite (IN.subschemeι ≫ pullback.fst qN r)]
  [Flat (IN.subschemeι ≫ pullback.fst qN r)]
  [IsFinite (ID.subschemeι ≫ pullback.fst qN r)]
  [Flat (ID.subschemeι ≫ pullback.fst qN r)]
  (ha : zeroScheme C (tensorModules F M) a = IA.comap jA)
  (hb : zeroScheme C M b = IB.comap jA)
  (hn : zeroScheme C N n = IN.comap jN)
  (hd : zeroScheme C N d = ID.comap jN)

local notation "s₀" => tensorSection (tensorModules F M) N ⊤
  (tensorSection F M ⊤ (divisorSheafGlobalSection G) b) d
local notation "s₁" => tensorSection (tensorModules F M) N ⊤ a n
local notation "pole" => tensorSection M N ⊤ b d
local notation "P" => zeroScheme C LP pole
local notation "familySourceNative" => familySource (q ≫ t) (pullback.fst q r) L s₀ s₁ ≫
  (nativeParameterIso (.of k) U).inv
local notation "δ" => retainedPencilDifference t q r L LP s₀ s₁ pole
local notation "lam" =>
  ofFiniteFlatSpan (X := UA) (Y := W)
    (IA.subschemeι ≫ pullback.fst qA r) (IA.subschemeι ≫ pullback.snd qA r)
    (by simp only [Category.assoc, pullback.condition_assoc]) -
  ofFiniteFlatSpan (X := UA) (Y := W)
    (IB.subschemeι ≫ pullback.fst qA r) (IB.subschemeι ≫ pullback.snd qA r)
    (by simp only [Category.assoc, pullback.condition_assoc])
local notation "psi" =>
  ofFiniteFlatSpan (X := UN) (Y := W)
    (ID.subschemeι ≫ pullback.fst qN r) (ID.subschemeι ≫ pullback.snd qN r)
    (by simp only [Category.assoc, pullback.condition_assoc]) -
  ofFiniteFlatSpan (X := UN) (Y := W)
    (IN.subschemeι ≫ pullback.fst qN r) (IN.subschemeι ≫ pullback.snd qN r)
    (by simp only [Category.assoc, pullback.condition_assoc])

variable [IsFinite familySourceNative] [Flat familySourceNative]
  [IsFinite (P.subschemeι ≫ pullback.fst q r)] [Flat (P.subschemeι ≫ pullback.fst q r)]

include ha hb hn hd in
/-- The actual one endpoint is the first source's numerator minus pole, minus
the second source's pole minus numerator. The two source maps are independent. -/
theorem retainedTensorDifference_one_source_graphs
    (hnc : IsEffectiveCartierDivisor (zeroScheme C N n))
    (hdc : IsEffectiveCartierDivisor (zeroScheme C N d)) :
    (graphFunctor k).map (nativeAffineSection (.of k) U 1) ≫ δ =
      (graphFunctor k).map αs ≫ lam - (graphFunctor k).map βs ≫ psi := by
  haveI hAf : IsFinite ((zeroScheme C (tensorModules F M) a).subschemeι ≫
      pullback.fst q r) := by
    rw [ha]
    exact retainedSupportSource_isFinite qA q r α hα IA
  haveI hAfl : Flat ((zeroScheme C (tensorModules F M) a).subschemeι ≫
      pullback.fst q r) := by
    rw [ha]
    exact retainedSupportSource_flat qA q r α hα IA
  haveI hBf : IsFinite ((zeroScheme C M b).subschemeι ≫ pullback.fst q r) := by
    rw [hb]
    exact retainedSupportSource_isFinite qA q r α hα IB
  haveI hBfl : Flat ((zeroScheme C M b).subschemeι ≫ pullback.fst q r) := by
    rw [hb]
    exact retainedSupportSource_flat qA q r α hα IB
  haveI hNf : IsFinite ((zeroScheme C N n).subschemeι ≫ pullback.fst q r) := by
    rw [hn]
    exact retainedSupportSource_isFinite qN q r β hβ IN
  haveI hNfl : Flat ((zeroScheme C N n).subschemeι ≫ pullback.fst q r) := by
    rw [hn]
    exact retainedSupportSource_flat qN q r β hβ IN
  haveI hDf : IsFinite ((zeroScheme C N d).subschemeι ≫ pullback.fst q r) := by
    rw [hd]
    exact retainedSupportSource_isFinite qN q r β hβ ID
  haveI hDfl : Flat ((zeroScheme C N d).subschemeι ≫ pullback.fst q r) := by
    rw [hd]
    exact retainedSupportSource_flat qN q r β hβ ID
  rw [retainedTensorDifference_one t q r φ hφ M N a b n d hnc hdc,
    Preadditive.comp_sub, Preadditive.comp_sub,
    graph_comp_retainedSupport t qA q r α hα IA,
    graph_comp_retainedSupport t qA q r α hα IB,
    graph_comp_retainedSupport t qN q r β hβ ID,
    graph_comp_retainedSupport t qN q r β hβ IN]
  simp only [ha, hb, hn, hd]

include ha hb hn hd in
/-- Both endpoints belong to the genuine polynomial-family-minus-constant-pole
correspondence. No endpoint equality or lifting conclusion is assumed. -/
theorem retainedTensorDifference_source_endpoints
    (hbc : IsEffectiveCartierDivisor (zeroScheme C M b))
    (hnc : IsEffectiveCartierDivisor (zeroScheme C N n))
    (hdc : IsEffectiveCartierDivisor (zeroScheme C N d)) :
    (graphFunctor k).map (nativeAffineSection (.of k) U 0) ≫ δ =
        (graphFunctor k).map φs ∧
      (graphFunctor k).map (nativeAffineSection (.of k) U 1) ≫ δ =
        (graphFunctor k).map αs ≫ lam - (graphFunctor k).map βs ≫ psi := by
  exact ⟨retainedTensorDifference_zero t q r φ hφ M N a b n d hbc hdc,
    retainedTensorDifference_one_source_graphs t q qA qN r α hα β hβ φ hφ M N a b n d
      IA IB IN ID ha hb hn hd hnc hdc⟩

end AlgebraicGeometry.Cor
