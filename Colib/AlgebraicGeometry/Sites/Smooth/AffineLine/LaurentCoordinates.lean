/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.PuncturedCoordinates
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.LineOpenMaps
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentProjection

/-!
# Actual Laurent coordinates on the relative punctured line

The affine Laurent chart carries the forward coordinate (T).
The comparison with the native torus cylinder preserves the original
coefficient restrictions.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/AffineLine/LaurentChart.lean`
and `Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/RelativeLaurentProductMap.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra.Smooth k R] [Algebra k S] [Algebra.Smooth k S]

/-- Smoothness of the Laurent algebra follows from its actual affine open map. -/
theorem laurent_smooth : Algebra.Smooth k (LaurentPolynomial R) := by
  let : Algebra.Smooth R R[X] := {}
  have : Smooth (polynomialProjection (.of R)) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have h : Smooth (laurentProjection (.of R)) := by
    rw [← laurentToPolynomial_projection]
    infer_instance
  rw [laurentProjection, HasRingHomProperty.Spec_iff (P := @Smooth)] at h
  let : Algebra.Smooth R (LaurentPolynomial R) := RingHom.smooth_algebraMap.mp h
  exact Algebra.Smooth.comp k R (LaurentPolynomial R)

attribute [local instance] laurent_smooth

/-- The native Laurent spectrum is the original principal open of the line. -/
def laurentSchemeIso :
    Spec (.of (LaurentPolynomial R)) ≅ (principalOpen (Polynomial.X : R[X])).toScheme :=
  IsOpenImmersion.isoOfRangeEq (laurentToPolynomial (.of R))
    (principalOpen (Polynomial.X : R[X])).ι (by
    rw [Scheme.Opens.range_ι]
    exact PrimeSpectrum.localization_away_comap_range (LaurentPolynomial R) (Polynomial.X : R[X]))

/-- The comparison lies over the original ground field. -/
def laurentSiteIso : sourceSite (k := k) (A := LaurentPolynomial R) ≅
    openSite (k := k) (Polynomial.X : R[X]) :=
  MorphismProperty.Over.isoMk (laurentSchemeIso (R := R)) (by
    change (laurentSchemeIso (R := R)).hom ≫ ((principalOpen (Polynomial.X : R[X])).ι ≫
      (polynomialProjection (.of R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))) = _
    rw [← Category.assoc, laurentSchemeIso, IsOpenImmersion.isoOfRangeEq_hom_fac,
      ← Category.assoc, laurentToPolynomial_projection]
    exact coefficient_base (k := k) (R := R) (A := LaurentPolynomial R))

/-- The larger Laurent coordinate is the actual forward generator. -/
theorem laurentSiteIso_coordinate :
    (laurentSiteIso (k := k) (R := R)).hom.left ≫ (principalOpen (Polynomial.X : R[X])).ι =
      Spec.map (CommRingCat.ofHom
        (eval₂RingHom (algebraMap R (LaurentPolynomial R)) (LaurentPolynomial.T 1))) := by
  change (laurentSchemeIso (R := R)).hom ≫ (principalOpen (Polynomial.X : R[X])).ι = _
  rw [laurentSchemeIso, IsOpenImmersion.isoOfRangeEq_hom_fac]
  change Spec.map (CommRingCat.ofHom
    (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R)) = Spec.map _
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change Polynomial.toLaurent (C r) = Polynomial.eval₂ _ _ (C r)
    rw [eval₂_C]
    exact Polynomial.toLaurent_C r
  · change Polynomial.toLaurent Polynomial.X = Polynomial.eval₂ _ _ Polynomial.X
    rw [eval₂_X]
    exact Polynomial.toLaurent_X

/-- The native punctured cylinder comparison preserves the actual coefficient map. -/
theorem puncturedProductIso_naturality (φ : R →ₐ[k] S) :
    puncturedBaseMap φ ≫ (puncturedProductIso (k := k) (R := R)).hom =
      (puncturedProductIso (k := k) (R := S)).hom ≫
        Contraction.torusCylinder.map (affineMorphism φ) := by
  let : Mono (Contraction.openInclusion.app (affineSite k R)) := by
    apply (forgetScheme (Spec (.of k))).mono_of_mono_map
    change Mono (Contraction.openInclusion.app (affineSite k R)).left
    infer_instance
  apply (cancel_mono (Contraction.openInclusion.app (affineSite k R))).mp
  have hφ : puncturedBaseMap φ ≫ polynomialPunctureInclusion (k := k) (R := R) =
      polynomialPunctureInclusion (k := k) (R := S) ≫ lineMap φ := by
    apply MorphismProperty.Over.Hom.ext
    exact openMapOfLE_inclusion _ _ _ _
  simp only [Category.assoc, Contraction.openInclusion.naturality, puncturedProductIso_open,
    puncturedProductIso_open_assoc]
  rw [← Category.assoc (puncturedBaseMap φ), hφ, Category.assoc, lineCylinderIso_naturality]

end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
