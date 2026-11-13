/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ChartBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormMark

/-!
# Marked factors of the paired norm chart

The original marked and residual schemes keep their actual maps after
base change to the chart. The target graph is Cartier on the full mark.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S X Y P C Z W : Scheme.{u}}
  (q : X ⟶ S) (π : P ⟶ S) (f : C ⟶ P)
  (j : Y ⟶ C) (jA : X ⟶ P) [IsOpenImmersion jA]
  (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (w : W ⟶ pullback (j ≫ f ≫ π) π)

local notation "b" => (j ≫ f ≫ π)
local notation "zA" => (z ≫ jA)
local notation "Hmark" => (pairedMark_isPullback f j jA p hRet z s H)
local notation "F" => (graphProductMap π f j)
local notation "κ" => (graphTargetParameterMap π f j jA p hRet)
local notation "mZ" => (retainedProductInclusion b π zA)
local notation "w₁" => (pullback.fst F w)
local notation "w₂" => (w ≫ κ)
local notation "iZ" => (pullback.snd mZ w)
local notation "Δ₂" => (Hom.ker (compactificationGraph π jA))

/-- The chart's actual marked source arrow factors through the original mark. -/
theorem pairedNormChart_sourceMark_factor :
    let J := retainedProductInclusion b (f ≫ π) j
    let s₀ := productMarkedSection b π f zA j s Hmark
    let H₀ := productMarkedSection_isPullback b π f zA j s Hmark
    let Jw := pullback.snd J w₁
    let sw := baseChangeMarkedSection F J mZ s₀ H₀ w
    (sw ≫ Jw) ≫ w₁ =
      (pullback.fst mZ w ≫ pairedMarkToSource π f j jA p hRet z s hs) ≫
        markedProductMap (f ≫ π) j s := by
  let J := retainedProductInclusion b (f ≫ π) j
  let s₀ := productMarkedSection b π f zA j s Hmark
  let H₀ := productMarkedSection_isPullback b π f zA j s Hmark
  let Jw := pullback.snd J w₁
  let sw := baseChangeMarkedSection F J mZ s₀ H₀ w
  let e₁ := pairedMarkToSource π f j jA p hRet z s hs
  let u := pullback.fst mZ w
  change (sw ≫ Jw) ≫ w₁ = (u ≫ e₁) ≫ markedProductMap (f ≫ π) j s
  have hsw' : sw ≫ pullback.fst J w₁ = u ≫ s₀ :=
    baseChangeMarkedSection_fst F J mZ s₀ H₀ w
  have he₁ : e₁ ≫ markedProductMap (f ≫ π) j s = s₀ ≫ J :=
    pairedMarkToSource_markedProductMap π f j jA p hRet z s hs H
  have hJ : Jw ≫ w₁ = pullback.fst J w₁ ≫ J :=
    (pullback.condition (f := J) (g := w₁)).symm
  calc
    _ = sw ≫ (Jw ≫ w₁) := Category.assoc _ _ _
    _ = sw ≫ (pullback.fst J w₁ ≫ J) := congrArg (fun k ↦ sw ≫ k) hJ
    _ = (sw ≫ pullback.fst J w₁) ≫ J := (Category.assoc _ _ _).symm
    _ = (u ≫ s₀) ≫ J := congrArg (fun k ↦ k ≫ J) hsw'
    _ = u ≫ (s₀ ≫ J) := Category.assoc _ _ _
    _ = u ≫ (e₁ ≫ markedProductMap (f ≫ π) j s) := congrArg (fun k ↦ u ≫ k) he₁.symm
    _ = _ := (Category.assoc _ _ _).symm

omit [IsOpenImmersion jA] in
include hRet in
/-- The chart's target mark factors through the original target mark. -/
theorem pairedNormChart_targetMark_factor :
    iZ ≫ w₂ =
      (pullback.fst mZ w ≫ pairedMarkToTarget q π f j jA p hB hA z) ≫
        markedProductMap π jA z := by
  let e₂ := pairedMarkToTarget q π f j jA p hB hA z
  let u := pullback.fst mZ w
  have he₂ : e₂ ≫ markedProductMap π jA z = mZ ≫ κ :=
    pairedMarkToTarget_markedProductMap q π f j jA p hRet hB hA z
  calc
    _ = (iZ ≫ w) ≫ κ := (Category.assoc _ _ _).symm
    _ = (u ≫ mZ) ≫ κ := congrArg (fun k ↦ k ≫ κ)
      (pullback.condition (f := mZ) (g := w)).symm
    _ = u ≫ (mZ ≫ κ) := Category.assoc _ _ _
    _ = u ≫ (e₂ ≫ markedProductMap π jA z) := congrArg (fun k ↦ u ≫ k) he₂.symm
    _ = _ := (Category.assoc _ _ _).symm

section Residual

variable [IsFinite f]

local notation "hmark" => (markedSection_original_equation f j zA s Hmark)

/-- Factorization of the actual residual chart through the source boundary. -/
abbrev PairedNormChartResidualFactor {D : Scheme.{u}} (d : D ⟶ C) : Prop :=
    let J := retainedProductInclusion b (f ≫ π) j
    let s₀ := productMarkedSection b π f zA j s Hmark
    let H₀ := productMarkedSection_isPullback b π f zA j s Hmark
    let Jw := pullback.snd J w₁
    let sw := baseChangeMarkedSection F J mZ s₀ H₀ w
    let hsw := markedSection_baseChange_equation F J mZ s₀ H₀ w
    let r := residualMarkedFiberMap (pullback.snd F w) Jw iZ sw hsw
    ∃ v : (residualMarkedFiberOpen (pullback.snd F w) Jw iZ sw hsw).toScheme ⟶
        pullback (pullback.snd b (f ≫ π)) d,
      r ≫ w₁ = v ≫ pullback.fst (pullback.snd b (f ≫ π)) d

/-- The paired chart uses the original residual factor through its exact
source boundary. -/
theorem exists_pairedNormChart_residual_factor {D : Scheme.{u}} (d : D ⟶ C)
    (l : (residualMarkedFiberOpen f j zA s hmark).toScheme ⟶ D)
    (hl : l ≫ d = residualMarkedFiberMap f j zA s hmark) :
    PairedNormChartResidualFactor π f j jA p hRet z s H w d := by
  exact exists_chartResidualBoundary_factor (B := Y) b π f w j zA s Hmark d l hl

/-- One original residual factor supplies the actual factor on every chart. -/
theorem pairedNormChart_residual_factor_family {D : Scheme.{u}} (d : D ⟶ C)
    (l : (residualMarkedFiberOpen f j zA s hmark).toScheme ⟶ D) :
    l ≫ d = residualMarkedFiberMap f j zA s hmark →
    ∀ (W' : Scheme.{u}) (w' : W' ⟶ pullback (j ≫ f ≫ π) π),
      PairedNormChartResidualFactor π f j jA p hRet z s H w' d :=
  fun hl _ w' ↦ exists_pairedNormChart_residual_factor π f j jA p hRet z s H w' d l hl

end Residual

variable [IsOpenImmersion w] [IsOpenImmersion j]
  [IsSeparated q] [IsSeparated π] [IsSeparated (f ≫ π)]
  [SmoothOfRelativeDimension 1 (j ≫ f ≫ π)]

include hs H hB hA in
/-- The graph on the marked chart is Cartier by base change along the actual open. -/
theorem pairedNormChart_targetMark_cartier :
    IsEffectiveCartierDivisor (((Δ₂).comap w₂).comap iZ) := by
  let u := pullback.fst mZ w
  let : IsOpenImmersion u := inferInstanceAs (IsOpenImmersion (pullback.fst mZ w))
  have hcomp : iZ ≫ w₂ = u ≫ mZ ≫ κ :=
    ((Category.assoc iZ w κ).symm.trans
      (congrArg (fun k ↦ k ≫ κ) (pullback.condition (f := mZ) (g := w)).symm)).trans
        (Category.assoc u mZ κ)
  have hcomap : ((Δ₂).comap w₂).comap iZ = ((Δ₂).comap (mZ ≫ κ)).comap u :=
    (IdealSheafData.comap_comp Δ₂ iZ w₂).symm.trans
      ((congrArg (fun k ↦ (Δ₂).comap k) hcomp).trans
        (IdealSheafData.comap_comp Δ₂ u (mZ ≫ κ)))
  exact (congrArg IsEffectiveCartierDivisor hcomap).mpr
    (isPullbackDefined_of_flat u _
      (isEffectiveCartierDivisor_pairedTargetMark q π f j jA p hRet hB hA z s hs H))

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

end
