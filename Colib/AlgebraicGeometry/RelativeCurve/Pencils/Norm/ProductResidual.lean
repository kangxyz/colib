/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Marked.BaseChange
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ProductBoundary

/-!
# The whole residual factor of the finite product

The residual open of the finite relative product maps into the original
residual open by the actual second projection. It retains the original
scheme-theoretic map into the compactification.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S B P C Y Z : Scheme.{u}} (b : B ⟶ S) (π : P ⟶ S) (f : C ⟶ P)
  (j : Y ⟶ C) (z : Z ⟶ P) (s : Z ⟶ Y) (H : IsPullback s (𝟙 Z) (j ≫ f) z)

local notation "F" => (retainedProductInclusion b π f)
local notation "J" => (retainedProductInclusion b (f ≫ π) j)
local notation "m" => (retainedProductInclusion b π z)
local notation "s₀" => (productMarkedSection b π f z j s H)
local notation "H₀" => (productMarkedSection_isPullback b π f z j s H)
local notation "hs" => (Scheme.markedSection_original_equation f j z s H)
local notation "hs₀" => (Scheme.markedSection_original_equation F J m s₀ H₀)

/-- The second coordinate of the full inverse fiber maps into the original full fiber. -/
def productMarkedFiberToOriginal : pullback F m ⟶ pullback f z :=
  pullback.lift (pullback.fst F m ≫ pullback.snd b (f ≫ π))
    (pullback.snd F m ≫ pullback.snd b (z ≫ π)) (by
      simpa only [Category.assoc, retainedProductInclusion_snd] using
        congrArg (fun a ↦ a ≫ pullback.snd b π) (pullback.condition (f := F) (g := m)))

variable [IsFinite f]

local notation "E" => (residualMarkedFiberOpen f j z s hs)
local notation "E₀" => (residualMarkedFiberOpen F J m s₀ hs₀)

private theorem range_productResidualToOriginal :
    Set.range ((E₀).ι ≫ productMarkedFiberToOriginal b π f z) ⊆ Set.range (E).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Opens.range_ι]
  change productMarkedFiberToOriginal b π f z x.val ∉ Set.range (markedFiberSection f j z s hs)
  intro hx
  obtain ⟨y, hy⟩ := (Scheme.mem_range_markedFiberSection_iff f j z s hs H _).mp hx
  have hy' : j y = (pullback.snd b (f ≫ π)) (pullback.fst F m x.val) := by
    simpa only [← Hom.comp_apply, productMarkedFiberToOriginal, pullback.lift_fst] using hy
  obtain ⟨a, -, ha⟩ := Scheme.exists_preimage_of_isPullback
    (retainedProductInclusion_isPullback b (f ≫ π) j) y (pullback.fst F m x.val) hy'
  exact x.property ((Scheme.mem_range_markedFiberSection_iff F J m s₀ hs₀ H₀ _).mpr ⟨a, ha⟩)

/-- The actual residual product lands in the original entire residual open. -/
@[no_expose]
def productResidualToOriginal : (E₀).toScheme ⟶ (E).toScheme :=
  IsOpenImmersion.lift (E).ι ((E₀).ι ≫ productMarkedFiberToOriginal b π f z)
    (range_productResidualToOriginal b π f j z s H)

/-- The residual comparison preserves its original structural map to the compactification. -/
@[reassoc (attr := simp)]
theorem productResidualToOriginal_map :
    productResidualToOriginal b π f j z s H ≫ residualMarkedFiberMap f j z s hs =
      residualMarkedFiberMap F J m s₀ hs₀ ≫ pullback.snd b (f ≫ π) := by
  have h := IsOpenImmersion.lift_fac (E).ι ((E₀).ι ≫ productMarkedFiberToOriginal b π f z)
    (range_productResidualToOriginal b π f j z s H)
  change productResidualToOriginal b π f j z s H ≫ (E).ι = _ at h
  change productResidualToOriginal b π f j z s H ≫ ((E).ι ≫ pullback.fst f z) =
    ((E₀).ι ≫ pullback.fst F m) ≫ pullback.snd b (f ≫ π)
  rw [← Category.assoc, h]
  simp only [Category.assoc, productMarkedFiberToOriginal, pullback.lift_fst]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
