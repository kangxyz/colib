/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Presentation.FiniteCoordinates

open CategoryTheory AlgebraicGeometry Scheme.RelativeCurve

universe u

/-- The same-fibre ideal-comap condition supplied by the original parameter theorem suffices
for the actual geometric producer, with the original polynomial map unchanged. -/
example (k R B : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.Smooth k B]
    (f : Polynomial R →+* B) (hf : f.Finite)
    (W : (Spec (.of B)).Opens) [IsAffine W.toScheme]
    [SmoothOfRelativeDimension 1
      (W.ι ≫ Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)))]
    (P : PrimeSpectrum B)
    (hW : ∀ Q : PrimeSpectrum B,
      Ideal.comap (f.comp Polynomial.C) P.asIdeal =
        Ideal.comap (f.comp Polynomial.C) Q.asIdeal → Q ∈ W)
    {Z : Scheme.{u}} (z : Z ⟶ Spec (.of B))
    [IsFinite (z ≫ Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)))] :
    ∃ (N : Scheme.{u}) (i : Spec (.of B) ⟶ N) (π : N ⟶ projectiveLine R)
      (t : R) (hi : IsOpenImmersion i), letI := hi;
      IsNormal N ∧ IsFinite π ∧ IsProper (π ≫ (projectiveLine R ↘ Spec (.of R))) ∧
      i ≫ π = Spec.map (CommRingCat.ofHom f) ≫ projectiveLineXChart R ∧
      Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)) P ∈ PrimeSpectrum.basicOpen t ∧
      IsFinite ((retainedBoundaryInclusion (i ''ᵁ W) ≫ π ≫
        (projectiveLine R ↘ Spec (.of R))) ∣_ PrimeSpectrum.basicOpen t) ∧
      IsAffine ((((i ''ᵁ W).ι ≫ π ≫ (projectiveLine R ↘ Spec (.of R))) ⁻¹ᵁ
        PrimeSpectrum.basicOpen t).toScheme) := by
  have hwhole : ∀ x : Spec (.of B),
      Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)) x =
        Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)) P → x ∈ W := by
    intro x hx
    exact hW x (congrArg PrimeSpectrum.asIdeal hx.symm)
  obtain ⟨N, D, i, π, b, e, t, hi, hN, hn, hnormal, hπ, hp, hb, hfinite, hpb,
    hr, hfac, hbase, ht, ha, hsm, hnew, ha', hz⟩ :=
    exists_good_neighborhood_of_finite_polynomial_coordinates k R B f hf W
      (Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)) P) hwhole z
  exact ⟨N, i, π, t, hi, hnormal, hπ, hp, hfac, ht, hnew, ha'⟩

#print axioms AlgebraicGeometry.Scheme.exists_normal_projectiveLine_cover_of_finite_coordinate
#print axioms AlgebraicGeometry.Scheme.exists_normal_projectiveLine_cover_of_finite_polynomial_map
#print axioms AlgebraicGeometry.Scheme.RelativeCurve.affine_smooth_image
#print axioms AlgebraicGeometry.Scheme.RelativeCurve.whole_fiber_image
#print axioms
  AlgebraicGeometry.Scheme.RelativeCurve.exists_compact_retained_principal_neighborhood
#print axioms
  AlgebraicGeometry.Scheme.RelativeCurve.exists_good_neighborhood_of_finite_polynomial_coordinates
