/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.BoundaryNeighborhood

/-!
# One base neighborhood retains the full boundary and a prescribed finite scheme

The base open avoids the closed image of the prescribed scheme outside the retained open.
Intersecting with the finite-boundary neighborhood keeps the whole prescribed scheme,
including its nilpotents, and the original closed boundary, without replacing either scheme.

Adapted from the Motivic source `RelativeCurve/Compactification/Retained/BoundaryPrescribedScheme`
at the 2026-10-21 checkpoint. The closed-image argument is made directly on the original map.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve

set_option backward.isDefEq.respectTransparency.types false in
/-- Finiteness of an actual base restriction persists on a smaller base open. -/
theorem finite_morphismRestrict_of_le {X S : Scheme.{u}} (f : X ⟶ S)
    {U V : S.Opens} (hVU : V ≤ U) [IsFinite (f ∣_ U)] : IsFinite (f ∣_ V) := by
  have h : IsFinite (f ∣_ U.ι ''ᵁ (U.ι ⁻¹ᵁ V)) :=
    (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
      (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mp inferInstance
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVU
  exact he ▸ h

/-- The same base shrink makes the original closed boundary finite and retains the entire
prescribed finite scheme in the chosen open. No reduced replacement is made. -/
@[colib_tag "COL-1067"]
theorem exists_finite_closed_retained_boundary_preserving_scheme
    {C S B D Z : Scheme.{u}} (q : C ⟶ S) [IsProper q] (b : B ⟶ C)
    [IsFinite (b ≫ q)] (U V : C.Opens)
    (hboundary : (U : Set C)ᶜ ⊆ Set.range b) (s : S)
    (hwhole : ∀ x : C, q x = s → x ∈ U → x ∈ V)
    (i : D ⟶ C) [IsClosedImmersion i] (hi : Set.range i ⊆ (V : Set C)ᶜ)
    (z : Z ⟶ C) [IsFinite (z ≫ q)]
    (hz : ∀ x : Z, (z ≫ q) x = s → z x ∈ V) :
    ∃ T : S.Opens, s ∈ T ∧ IsFinite ((i ≫ q) ∣_ T) ∧
      ∀ x : Z, (z ≫ q) x ∈ T → z x ∈ V := by
  obtain ⟨T₁, hs₁, hfinite⟩ :=
    exists_finite_closed_retained_boundary q b U V hboundary s hwhole i hi
  let T₂ : S.Opens :=
    ⟨((z ≫ q) '' ((z ⁻¹ᵁ V : Z.Opens) : Set Z)ᶜ)ᶜ,
      ((z ≫ q).isClosedMap _ (z ⁻¹ᵁ V).isOpen.isClosed_compl).isOpen_compl⟩
  have hs₂ : s ∈ T₂ := by
    rintro ⟨x, hx, he⟩
    exact hx (hz x he)
  have : IsFinite ((i ≫ q) ∣_ T₁) := hfinite
  refine ⟨T₁ ⊓ T₂, ⟨hs₁, hs₂⟩, finite_morphismRestrict_of_le _ inf_le_left, ?_⟩
  intro x hx
  by_contra hn
  exact hx.2 ⟨x, hn, rfl⟩

/-- The canonical full complement and the full prescribed finite scheme use one base open. -/
@[colib_tag "COL-1067"]
theorem exists_finite_retainedBoundary_preserving_scheme
    {C S B Z : Scheme.{u}} (q : C ⟶ S) [IsProper q] (b : B ⟶ C)
    [IsFinite (b ≫ q)] (U V : C.Opens)
    (hboundary : (U : Set C)ᶜ ⊆ Set.range b) (s : S)
    (hwhole : ∀ x : C, q x = s → x ∈ U → x ∈ V)
    (z : Z ⟶ C) [IsFinite (z ≫ q)] (hzU : Set.range z ⊆ U) :
    ∃ T : S.Opens, s ∈ T ∧ IsFinite ((retainedBoundaryInclusion V ≫ q) ∣_ T) ∧
      ∀ x : Z, (z ≫ q) x ∈ T → z x ∈ V :=
  exists_finite_closed_retained_boundary_preserving_scheme q b U V hboundary s hwhole
    (retainedBoundaryInclusion V) (range_retainedBoundaryInclusion V).le z
    (fun x hx => hwhole (z x) hx (hzU ⟨x, rfl⟩))

end AlgebraicGeometry.Scheme.RelativeCurve
