/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.Basic
public import Colib.Algebra.Category.Ring.PolynomialPushout

/-! # Actual polynomial ambient product over the coefficient ring -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Spec/PolynomialQuotient/PolynomialQuotientCoordinates.lean`, blob
`807d29ce5848922f60cd65075c194d31bdadcbb1`.
The active affine cylinder remains the existing native additive group object.
The polynomial spectrum is only an explicit comparison target.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient
variable {k R : Type u} [CommRing k] [CommRing R] (σ : k →+* R)

/-- The polynomial ambient scheme is the original affine-line product. -/
theorem ambient_isPullback :
    IsPullback (polynomialProjection (.of R))
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom σ)))
      (Spec.map (CommRingCat.ofHom σ)) (polynomialProjection (.of k)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.polynomial_isPushout (CommRingCat.ofHom σ))

/-- The canonical isomorphism `Spec R[X] ≅ Spec R ×[Spec k] Spec k[X]` induced by `σ`. -/
def ambientIso : Spec (.of R[X]) ≅
    pullback (Spec.map (CommRingCat.ofHom σ)) (polynomialProjection (.of k)) :=
  (ambient_isPullback σ).isoPullback

@[reassoc (attr := simp)] theorem ambientIso_fst :
    (ambientIso σ).hom ≫ pullback.fst _ _ = polynomialProjection (.of R) :=
  (ambient_isPullback σ).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem ambientIso_snd :
    (ambientIso σ).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom σ)) :=
  (ambient_isPullback σ).isoPullback_hom_snd

end AlgebraicGeometry.PolynomialOpenQuotient
