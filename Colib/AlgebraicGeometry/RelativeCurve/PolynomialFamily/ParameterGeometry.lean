/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeFibers
public import Colib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison

/-! # Geometry of the original polynomial parameter

The parameter used by the pencil is the same affine-line pullback used
by the smooth site. Its geometry follows from the actual comparison over
the coefficient scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.PolynomialSectionPencil

open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction (polynomialAffineLine)

instance geometricallyIntegral_polynomialParameter (R : CommRingCat.{u}) :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))) := by
  have H : IsPullback (polynomialAffineSpaceIso R).hom
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
      (AffineSpace (ULift.{u} Unit) (Spec R) ↘ Spec R) (𝟙 (Spec R)) :=
    IsPullback.of_horiz_isIso
      ⟨(polynomialAffineSpaceIso_hom_over R).trans (Category.comp_id _).symm⟩
  exact MorphismProperty.of_isPullback H inferInstance

variable {R : Type u} [CommRing R] {D : Scheme.{u}} (t : D ⟶ Spec (.of R))

instance projection_isAffineHom : IsAffineHom (projection t) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback t (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))).flip
    inferInstance

instance projection_smooth : Smooth (projection t) := by
  let π := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))
  have hπ : Smooth π := (polynomialAffineLine (.of R)).prop.1.1
  exact MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback t π).flip hπ

instance parameterSpace_isNoetherian [IsNoetherian D] : IsNoetherian (parameterSpace t) :=
  isNoetherian_of_finiteType_of_isNoetherian (projection t)

instance parameterSpace_isIntegral [IsIntegral D] [IsLocallyNoetherian D] :
    IsIntegral (parameterSpace t) := by
  let π := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))
  let : GeometricallyIntegral (projection t) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
      (IsPullback.of_hasPullback t π).flip (geometricallyIntegral_polynomialParameter (.of R))
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projection t)

end AlgebraicGeometry.Scheme.PolynomialSectionPencil
