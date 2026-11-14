/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.OpenBaseChange
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Pullback of a two-open cover to the projective line -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable {V X : Scheme.{u}} (j : V ⟶ X) (T : X.Opens)

local notation "P" Z => projectiveSpaceOver 1 Z
local notation "π" Z => (projectiveSpaceOver 1 Z ↘ Z)
local notation "J" => projectiveSpaceOverMap 1 j

/-- The native projective-line base change of an open immersion is an open immersion. -/
instance projectiveLineMap_isOpenImmersion [IsOpenImmersion j] :
    IsOpenImmersion J :=
  MorphismProperty.of_isPullback (isPullback_projectiveSpaceOverMap 1 j).flip inferInstance

/-- The two literal descriptions of the pulled-back intersection agree. -/
theorem projectiveLine_preimage_preimage :
    J ⁻¹ᵁ ((π X) ⁻¹ᵁ T) = (π V) ⁻¹ᵁ (j ⁻¹ᵁ T) := by
  have h : J ≫ (π X) = (π V) ≫ j := projectiveSpaceOverMap_fst 1 j
  rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.comp_preimage]

/-- The original cover pulls back to a cover of the canonical projective line. -/
theorem projectiveLine_baseOpenCover
    (h : ∀ x : X, x ∈ Set.range j ∨ x ∈ T) :
    ∀ z : P X, z ∈ Set.range J ∨ z ∈ (π X) ⁻¹ᵁ T := by
  intro z
  rcases h ((π X) z) with ⟨v, hv⟩ | hz
  · left
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_projectiveSpaceOverMap 1 j) z v hv.symm
    exact ⟨w, hw⟩
  · exact Or.inr hz

end AlgebraicGeometry.Scheme
