/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalBoundaryFramePullback
public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryFrameNaturality

/-! # Two actual pullbacks of the original canonical difference boundary frame

The nested module target is retained. There is no replacement by a composition
comparison for the chosen Cartier pullback isomorphism.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace Stacks.Divisors

/-- The original canonical frame is transported through two actual squares using
only the one-step theorem and native target naturality. -/
theorem differenceSheafBoundaryIso_pullback_two_squares
    {B₀ B₁ B₂ X₀ X₁ X₂ : Scheme.{u}}
    (b₁ : B₁ ⟶ B₀) (b₂ : B₂ ⟶ B₁)
    (i₀ : B₀ ⟶ X₀) (i₁ : B₁ ⟶ X₁) (i₂ : B₂ ⟶ X₂)
    (f₁ : X₁ ⟶ X₀) (f₂ : X₂ ⟶ X₁)
    (w₁ : b₁ ≫ i₀ = i₁ ≫ f₁) (w₂ : b₂ ≫ i₁ = i₂ ≫ f₂)
    (D E : X₀.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    [IsPullbackDefined f₁ D] [IsPullbackDefined f₁ E]
    [IsPullbackDefined f₂ (D.comap f₁)] [IsPullbackDefined f₂ (E.comap f₁)]
    (hD : ∀ y : B₀, i₀ y ∉ D.support) (hE : ∀ y : B₀, i₀ y ∉ E.support) :
    let hD₁ := avoids_support_comap_square b₁ i₀ i₁ f₁ w₁ D hD
    let hE₁ := avoids_support_comap_square b₁ i₀ i₁ f₁ w₁ E hE
    let ρ₁ := differenceSheafPullbackIso f₁ D E
    let ρ₂ := differenceSheafPullbackIso f₂ (D.comap f₁) (E.comap f₁)
    (Scheme.Modules.pullback i₂).mapIso ((Scheme.Modules.pullback f₂).mapIso ρ₁ ≪≫ ρ₂) ≪≫
      differenceSheafBoundaryIso i₂ ((D.comap f₁).comap f₂) ((E.comap f₁).comap f₂)
        (avoids_support_comap_square b₂ i₁ i₂ f₂ w₂ (D.comap f₁) hD₁)
        (avoids_support_comap_square b₂ i₁ i₂ f₂ w₂ (E.comap f₁) hE₁) =
    pullbackBoundaryTrivialization b₂ i₁ i₂ f₂ w₂
      ((Scheme.Modules.pullback f₁).obj (differenceSheaf D E))
      (pullbackBoundaryTrivialization b₁ i₀ i₁ f₁ w₁ (differenceSheaf D E)
        (differenceSheafBoundaryIso i₀ D E hD hE)) := by
  intro hD₁ hE₁ ρ₁ ρ₂
  have h₁ := differenceSheafBoundaryIso_pullback_square b₁ i₀ i₁ f₁ w₁ D E hD hE
  have h₂ := differenceSheafBoundaryIso_pullback_square b₂ i₁ i₂ f₂ w₂
    (D.comap f₁) (E.comap f₁) hD₁ hE₁
  rw [Functor.mapIso_trans, Iso.trans_assoc]
  rw [h₂]
  rw [pullbackBoundaryTrivialization_naturality b₂ i₁ i₂ f₂ w₂ ρ₁]
  rw [h₁]

end Stacks.Divisors
