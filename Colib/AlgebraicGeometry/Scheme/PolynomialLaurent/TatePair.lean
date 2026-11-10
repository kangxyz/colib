/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Polynomial.Ideal

/-!
# The native Laurent open is the complement of the zero section

The existing `laurentToPolynomial` is the actual localization map from the Laurent
spectrum to the polynomial spectrum. Its image is the principal open of `X`, hence
the complement of the actual zero section. Evaluation at one gives compatible
basepoints for this open immersion. Both structure morphisms are smooth, separated
and quasi-compact over every commutative ring.

This is the scheme pair used for `T = A¹ / (A¹ - 0)`. No quotient or motivic
equivalence is asserted here. The affine schemes and their coordinate maps remain
the native `Spec` constructions, without another affine-line or torus model.

The smoothness and Laurent identity-section arguments are adapted from
`Motivic/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Torus.lean` at revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

variable (R : CommRingCat.{u})

/-- The structure morphism of the actual polynomial spectrum. -/
def polynomialProjection : Spec (.of (Polynomial R)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

/-- The structure morphism of the actual Laurent spectrum. -/
def laurentProjection : Spec (.of (LaurentPolynomial R)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom LaurentPolynomial.C)

/-- The existing localization map is a morphism over the coefficient spectrum. -/
@[reassoc (attr := simp)]
theorem laurentToPolynomial_projection :
    laurentToPolynomial R ≫ polynomialProjection R = laurentProjection R := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  ext r : 2
  exact Polynomial.toLaurent_C r

instance : Smooth (polynomialProjection R) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  change (algebraMap R (Polynomial R)).Smooth
  rw [RingHom.smooth_algebraMap]
  exact ⟨inferInstance, inferInstance⟩

instance : Smooth (laurentProjection R) := by
  rw [← laurentToPolynomial_projection]
  infer_instance

instance : IsSeparated (polynomialProjection R) := by
  unfold polynomialProjection
  infer_instance

instance : IsSeparated (laurentProjection R) := by
  unfold laurentProjection
  infer_instance

instance : QuasiCompact (polynomialProjection R) := by
  unfold polynomialProjection
  infer_instance

instance : QuasiCompact (laurentProjection R) := by
  unfold laurentProjection
  infer_instance

/-- Evaluation at a coefficient gives the actual section of the polynomial spectrum. -/
def polynomialSection (a : R) : Spec R ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))

/-- The zero section is evaluation at zero. -/
abbrev polynomialZeroSection : Spec R ⟶ Spec (.of (Polynomial R)) :=
  polynomialSection R 0

/-- The basepoint one is evaluation at one. -/
abbrev polynomialOneSection : Spec R ⟶ Spec (.of (Polynomial R)) :=
  polynomialSection R 1

instance (a : R) : IsClosedImmersion (polynomialSection R a) :=
  IsClosedImmersion.spec_of_surjective _ (Polynomial.eval_surjective a)

@[reassoc (attr := simp)]
theorem polynomialSection_projection (a : R) :
    polynomialSection R a ≫ polynomialProjection R = 𝟙 (Spec R) := by
  have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom a) = 𝟙 R := by
    ext r
    exact Polynomial.eval_C
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, h, Spec.map_id]

@[reassoc (attr := simp)]
theorem polynomialZeroSection_projection :
    polynomialZeroSection R ≫ polynomialProjection R = 𝟙 (Spec R) :=
  polynomialSection_projection R 0

@[reassoc (attr := simp)]
theorem polynomialOneSection_projection :
    polynomialOneSection R ≫ polynomialProjection R = 𝟙 (Spec R) :=
  polynomialSection_projection R 1

/-- The Laurent identity section is evaluation of its coordinate at the unit one. -/
def laurentOneSection : Spec R ⟶ Spec (.of (LaurentPolynomial R)) :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id R) 1))

instance : IsClosedImmersion (laurentOneSection R) :=
  IsClosedImmersion.spec_of_surjective _ (fun r =>
    ⟨LaurentPolynomial.C r, LaurentPolynomial.eval₂_C _ _ _⟩)

/-- The chosen basepoints commute with the original open immersion. -/
@[reassoc (attr := simp)]
theorem laurentOneSection_toPolynomial :
    laurentOneSection R ≫ laurentToPolynomial R = polynomialOneSection R := by
  have h : CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R) ≫
      CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id R) 1) =
        CommRingCat.ofHom (Polynomial.evalRingHom (1 : R)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact LaurentPolynomial.eval₂_toLaurent (RingHom.id R) 1 p
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, h]
  rfl

@[reassoc (attr := simp)]
theorem laurentOneSection_projection :
    laurentOneSection R ≫ laurentProjection R = 𝟙 (Spec R) := by
  rw [← laurentToPolynomial_projection, ← Category.assoc,
    laurentOneSection_toPolynomial, polynomialOneSection_projection]

/-- The image of the existing Laurent open is exactly the principal open of `X`. -/
theorem laurentToPolynomial_opensRange :
    (laurentToPolynomial R).opensRange =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (LaurentPolynomial R)
    (Polynomial.X : Polynomial R)

/-- The actual zero section has image the vanishing locus of the polynomial coordinate. -/
theorem range_polynomialZeroSection :
    Set.range (polynomialZeroSection R) =
      PrimeSpectrum.zeroLocus ({Polynomial.X} : Set (Polynomial R)) := by
  change Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R))) = _
  rw [range_comap_of_surjective _ _ (Polynomial.eval_surjective 0),
    Polynomial.ker_evalRingHom]
  simp only [map_zero, sub_zero, PrimeSpectrum.zeroLocus_span]

/-- The Laurent spectrum is precisely the complement of the actual zero section. -/
theorem laurentToPolynomial_range_eq_compl_zeroSection :
    Set.range (laurentToPolynomial R) = (Set.range (polynomialZeroSection R))ᶜ := by
  rw [range_polynomialZeroSection]
  exact (PrimeSpectrum.localization_away_comap_range (LaurentPolynomial R)
    (Polynomial.X : Polynomial R)).trans
      (PrimeSpectrum.basicOpen_eq_zeroLocus_compl (Polynomial.X : Polynomial R))

end AlgebraicGeometry.Scheme.PolynomialLaurent

attribute [colib_tag "COL-0386"]
  AlgebraicGeometry.Scheme.PolynomialLaurent.laurentToPolynomial_range_eq_compl_zeroSection
