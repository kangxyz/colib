/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.SectionNeighborhood
import Colib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.PrincipalNeighborhood
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open CategoryTheory AlgebraicGeometry Scheme.RelativeCurve

universe u

/-- Arbitrary original closed-boundary scheme structure is retained, together with two actual
section maps. No reducedness or normality assumptions on the boundary are required. -/
example {C S B D : Scheme.{u}} (q : C ⟶ S) [IsProper q] (b : B ⟶ C)
    [IsFinite (b ≫ q)] (U V : C.Opens)
    (hboundary : (U : Set C)ᶜ ⊆ Set.range b) (s : S)
    (hwhole : ∀ x : C, q x = s → x ∈ U → x ∈ V)
    (i : D ⟶ C) [IsClosedImmersion i] (hi : Set.range i = (V : Set C)ᶜ)
    (σ₀ σ₁ : S ⟶ C) (hσ₀ : σ₀ ≫ q = 𝟙 S) (hσ₁ : σ₁ ≫ q = 𝟙 S)
    (h₀ : σ₀ s ∈ U) (h₁ : σ₁ s ∈ U) :
    ∃ (T : S.Opens) (τ₀ τ₁ : T.toScheme ⟶ V.toScheme),
      s ∈ T ∧ IsFinite ((i ≫ q) ∣_ T) ∧
      τ₀ ≫ V.ι = T.ι ≫ σ₀ ∧ τ₁ ≫ V.ι = T.ι ≫ σ₁ ∧
      τ₀ ≫ V.ι ≫ q = T.ι ∧ τ₁ ≫ V.ι ≫ q = T.ι :=
  exists_finite_closed_retained_boundary_preserving_two_sections
    q b U V hboundary s hwhole i hi.le σ₀ σ₁ hσ₀ hσ₁ h₀ h₁

/-- The principal shrink keeps the genuine retained affine smooth curve smooth and affine,
while making its full boundary finite and retaining the prescribed finite scheme. -/
example (R : Type u) [CommRing R] {C B Z : Scheme.{u}}
    (q : C ⟶ Spec (.of R)) [IsProper q] (b : B ⟶ C) [IsFinite (b ≫ q)]
    (U V : C.Opens) [IsAffine V.toScheme] [SmoothOfRelativeDimension 1 (V.ι ≫ q)]
    (hboundary : (U : Set C)ᶜ ⊆ Set.range b) (s : Spec (.of R))
    (hwhole : ∀ x : C, q x = s → x ∈ U → x ∈ V)
    (z : Z ⟶ C) [IsFinite (z ≫ q)] (hzU : Set.range z ⊆ U) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      IsFinite ((retainedBoundaryInclusion V ≫ q) ∣_ PrimeSpectrum.basicOpen r) ∧
      IsAffine (((V.ι ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme) ∧
      SmoothOfRelativeDimension 1 ((V.ι ≫ q) ∣_ PrimeSpectrum.basicOpen r) ∧
      ∀ x : Z, (z ≫ q) x ∈ PrimeSpectrum.basicOpen r → z x ∈ V := by
  obtain ⟨r, hr, hf, ha, hz⟩ :=
    exists_principal_finite_retainedBoundary_preserving_scheme
      R q b U V hboundary s hwhole z hzU
  have hsm : SmoothOfRelativeDimension 1 ((V.ι ≫ q) ∣_ PrimeSpectrum.basicOpen r) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict (V.ι ≫ q) (PrimeSpectrum.basicOpen r)).flip inferInstance
  exact ⟨r, hr, hf, ha, hsm, hz⟩

#print axioms AlgebraicGeometry.Scheme.RelativeCurve.finite_retained_complement_fiber
#print axioms AlgebraicGeometry.Scheme.RelativeCurve.exists_finite_closed_retained_boundary
#print axioms AlgebraicGeometry.Scheme.RelativeCurve.exists_finite_retainedBoundary
#print axioms
  AlgebraicGeometry.Scheme.RelativeCurve.exists_finite_closed_retained_boundary_preserving_scheme
#print axioms AlgebraicGeometry.Scheme.RelativeCurve.exists_finite_retainedBoundary_preserving_scheme
#print axioms
  AlgebraicGeometry.Scheme.RelativeCurve.exists_finite_closed_retained_boundary_preserving_two_sections
#print axioms
  AlgebraicGeometry.Scheme.RelativeCurve.exists_principal_finite_retainedBoundary_preserving_scheme
