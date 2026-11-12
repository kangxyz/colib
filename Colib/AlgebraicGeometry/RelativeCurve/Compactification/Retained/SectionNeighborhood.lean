/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.PrescribedNeighborhood

/-!
# Retaining two actual sections on the finite-boundary neighborhood

Intersect the finite-boundary neighborhood with the inverse images of the retained open under
the two original sections. Both sections factor through that same retained open, with explicit
morphism equations. The sections need only meet the original chart at the selected base point.
The closed boundary remains the original scheme with its original scheme structure.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- One base shrink retains two original sections and makes the original closed boundary
finite. The displayed factorization equations identify the actual section morphisms. -/
@[colib_tag "COL-1067"]
theorem exists_finite_closed_retained_boundary_preserving_two_sections
    {C S B D : Scheme.{u}} (q : C ⟶ S) [IsProper q] (b : B ⟶ C)
    [IsFinite (b ≫ q)] (U V : C.Opens)
    (hboundary : (U : Set C)ᶜ ⊆ Set.range b) (s : S)
    (hwhole : ∀ x : C, q x = s → x ∈ U → x ∈ V)
    (i : D ⟶ C) [IsClosedImmersion i] (hi : Set.range i ⊆ (V : Set C)ᶜ)
    (σ₀ σ₁ : S ⟶ C) (hσ₀ : σ₀ ≫ q = 𝟙 S) (hσ₁ : σ₁ ≫ q = 𝟙 S)
    (h₀ : σ₀ s ∈ U) (h₁ : σ₁ s ∈ U) :
    ∃ (T : S.Opens) (τ₀ τ₁ : T.toScheme ⟶ V.toScheme),
      s ∈ T ∧ IsFinite ((i ≫ q) ∣_ T) ∧
      τ₀ ≫ V.ι = T.ι ≫ σ₀ ∧ τ₁ ≫ V.ι = T.ι ≫ σ₁ ∧
      τ₀ ≫ V.ι ≫ q = T.ι ∧ τ₁ ≫ V.ι ≫ q = T.ι := by
  obtain ⟨T₁, hs₁, hfinite⟩ :=
    exists_finite_closed_retained_boundary q b U V hboundary s hwhole i hi
  let T := T₁ ⊓ (σ₀ ⁻¹ᵁ V) ⊓ (σ₁ ⁻¹ᵁ V)
  have hT₀ : T ≤ σ₀ ⁻¹ᵁ V := inf_le_left.trans inf_le_right
  have hT₁ : T ≤ σ₁ ⁻¹ᵁ V := inf_le_right
  have hs₀V : σ₀ s ∈ V := hwhole (σ₀ s)
    (congrArg (fun f : S ⟶ S => f s) hσ₀) h₀
  have hs₁V : σ₁ s ∈ V := hwhole (σ₁ s)
    (congrArg (fun f : S ⟶ S => f s) hσ₁) h₁
  have : IsFinite ((i ≫ q) ∣_ T₁) := hfinite
  refine ⟨T, σ₀.resLE V T hT₀, σ₁.resLE V T hT₁, ⟨⟨hs₁, hs₀V⟩, hs₁V⟩,
    finite_morphismRestrict_of_le _ (inf_le_left.trans inf_le_left),
    σ₀.resLE_comp_ι hT₀, σ₁.resLE_comp_ι hT₁, ?_, ?_⟩
  · rw [← Category.assoc, σ₀.resLE_comp_ι, Category.assoc, hσ₀, Category.comp_id]
  · rw [← Category.assoc, σ₁.resLE_comp_ι, Category.assoc, hσ₁, Category.comp_id]

end AlgebraicGeometry.Scheme.RelativeCurve
