/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ProductResidual

/-!
# Whole boundary maps on an actual norm chart

The chart inverse of a target boundary and the residual component of its
marked fiber factor through the original source boundary, with the literal
maps into the finite relative product.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S B P C X Y Z D E W : Scheme.{u}} (b : B ⟶ S) (π : P ⟶ S) (f : C ⟶ P)
  (w : W ⟶ pullback b π)

local notation "F" => (retainedProductInclusion b π f)
local notation "w₁" => (pullback.fst F w)
local notation "pW" => (pullback.snd F w)

/-- The inverse boundary product uses the actual original boundary map. -/
theorem exists_productInverseBoundary_factor (d : D ⟶ C) (z : Z ⟶ P)
    (l : pullback f z ⟶ D) (hl : l ≫ d = pullback.fst f z) :
    let m := retainedProductInclusion b π z
    ∃ v : pullback F m ⟶ pullback (pullback.snd b (f ≫ π)) d,
      pullback.fst F m = v ≫ pullback.fst (pullback.snd b (f ≫ π)) d := by
  dsimp only
  let H := productInverseBoundary_isPullback b π f (pullback.fst f z) z
    (pullback.snd f z) (IsPullback.of_hasPullback f z)
  let u := H.isoPullback.inv
  let t := u ≫ pullback.snd b (pullback.fst f z ≫ f ≫ π) ≫ l
  have hu : u ≫ retainedProductInclusion b (f ≫ π) (pullback.fst f z) =
      pullback.fst F (retainedProductInclusion b π z) := H.isoPullback_inv_fst
  have ht : pullback.fst F (retainedProductInclusion b π z) ≫ pullback.snd b (f ≫ π) =
      t ≫ d := by
    rw [← hu, Category.assoc, retainedProductInclusion_snd]
    simp only [t, Category.assoc, hl]
  exact ⟨pullback.lift _ t ht, (pullback.lift_fst _ _ _).symm⟩

/-- The full inverse of the chart boundary uses the actual chosen source
boundary map, with the whole original scheme structure. -/
theorem exists_chartInverseBoundary_factor (d : D ⟶ C) (z : Z ⟶ P)
    (l : pullback f z ⟶ D) (hl : l ≫ d = pullback.fst f z) :
    let m := retainedProductInclusion b π z
    let i := pullback.snd m w
    ∃ v : pullback pW i ⟶ pullback (pullback.snd b (f ≫ π)) d,
      pullback.fst pW i ≫ w₁ = v ≫ pullback.fst (pullback.snd b (f ≫ π)) d := by
  dsimp only
  let m := retainedProductInclusion b π z
  let i := pullback.snd m w
  let a := pullback.fst pW i ≫ w₁
  let c := pullback.snd pW i ≫ pullback.fst m w
  have h : a ≫ F = c ≫ m := by
    dsimp only [a, c]
    calc
      _ = (pullback.fst pW i ≫ pW) ≫ w := by
        rw [Category.assoc, pullback.condition (f := F) (g := w), ← Category.assoc]
      _ = (pullback.snd pW i ≫ i) ≫ w := by rw [pullback.condition (f := pW) (g := i)]
      _ = _ := by
        rw [Category.assoc, ← pullback.condition (f := m) (g := w), ← Category.assoc]
  obtain ⟨v, hv⟩ := exists_productInverseBoundary_factor b π f d z l hl
  refine ⟨pullback.lift a c h ≫ v, ?_⟩
  rw [Category.assoc, ← hv, pullback.lift_fst]

/-- A second-factor boundary maps into the original target boundary under
the specified first-parameter change. -/
theorem exists_productTargetBoundary_factor
    (q : X ⟶ S) (κ : pullback b π ⟶ pullback q π)
    (hκ : κ ≫ pullback.snd q π = pullback.snd b π) (z : Z ⟶ P) :
    ∃ v : pullback b (z ≫ π) ⟶ pullback (pullback.snd q π) z,
      retainedProductInclusion b π z ≫ κ = v ≫ pullback.fst (pullback.snd q π) z := by
  let a := retainedProductInclusion b π z ≫ κ
  have h : a ≫ pullback.snd q π = pullback.snd b (z ≫ π) ≫ z := by
    simp only [a, Category.assoc, hκ, retainedProductInclusion_snd]
  exact ⟨pullback.lift a _ h, (pullback.lift_fst _ _ _).symm⟩

/-- The target chart boundary maps into the original second-factor boundary
after the specified first-parameter change. -/
theorem exists_chartTargetBoundary_factor
    (q : X ⟶ S) (κ : pullback b π ⟶ pullback q π)
    (hκ : κ ≫ pullback.snd q π = pullback.snd b π) (z : Z ⟶ P) :
    let m := retainedProductInclusion b π z
    let i := pullback.snd m w
    ∃ v : pullback m w ⟶ pullback (pullback.snd q π) z,
      i ≫ w ≫ κ = v ≫ pullback.fst (pullback.snd q π) z := by
  dsimp only
  let m := retainedProductInclusion b π z
  obtain ⟨v, hv⟩ := exists_productTargetBoundary_factor b π q κ hκ z
  refine ⟨pullback.fst m w ≫ v, ?_⟩
  rw [← Category.assoc, ← pullback.condition (f := m) (g := w), Category.assoc,
    hv, ← Category.assoc]

variable [IsFinite f] (j : Y ⟶ C) (z : Z ⟶ P) (s : Z ⟶ Y)
  (H : IsPullback s (𝟙 Z) (j ≫ f) z)

local notation "J" => (retainedProductInclusion b (f ≫ π) j)
local notation "m" => (retainedProductInclusion b π z)
local notation "i" => (pullback.snd m w)
local notation "s₀" => (productMarkedSection b π f z j s H)
local notation "H₀" => (productMarkedSection_isPullback b π f z j s H)
local notation "hs₀" => (markedSection_original_equation F J m s₀ H₀)
local notation "J₁" => (pullback.snd J w₁)
local notation "s₁" => (baseChangeMarkedSection F J m s₀ H₀ w)
local notation "hs₁" => (markedSection_baseChange_equation F J m s₀ H₀ w)
local notation "hs" => (markedSection_original_equation f j z s H)
local notation "E₁" => (residualMarkedFiberOpen pW J₁ i s₁ hs₁)

/-- The full residual product factors through the original source boundary. -/
theorem exists_productResidualBoundary_factor (d : D ⟶ C)
    (l : (residualMarkedFiberOpen f j z s hs).toScheme ⟶ D)
    (hl : l ≫ d = residualMarkedFiberMap f j z s hs) :
    ∃ v : (residualMarkedFiberOpen F J m s₀ hs₀).toScheme ⟶
        pullback (pullback.snd b (f ≫ π)) d,
      residualMarkedFiberMap F J m s₀ hs₀ = v ≫ pullback.fst (pullback.snd b (f ≫ π)) d := by
  let a := residualMarkedFiberMap F J m s₀ hs₀
  let c := productResidualToOriginal b π f j z s H ≫ l
  have hc : a ≫ pullback.snd b (f ≫ π) = c ≫ d := by
    simp only [a, c, Category.assoc, hl, productResidualToOriginal_map]
  exact ⟨pullback.lift a c hc, (pullback.lift_fst _ _ _).symm⟩

/-- The whole residual fiber on the actual chart factors through the original
source boundary which contains the original residual scheme. -/
theorem exists_chartResidualBoundary_factor (d : D ⟶ C)
    (l : (residualMarkedFiberOpen f j z s hs).toScheme ⟶ D)
    (hl : l ≫ d = residualMarkedFiberMap f j z s hs) :
    ∃ v : (E₁).toScheme ⟶ pullback (pullback.snd b (f ≫ π)) d,
      residualMarkedFiberMap pW J₁ i s₁ hs₁ ≫ w₁ =
        v ≫ pullback.fst (pullback.snd b (f ≫ π)) d := by
  obtain ⟨v, hv⟩ := exists_productResidualBoundary_factor b π f j z s H d l hl
  refine ⟨residualMarkedFiberBaseChangeMap F J m s₀ H₀ w ≫ v, ?_⟩
  rw [Category.assoc, ← hv, residualMarkedFiberBaseChangeMap_map]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
