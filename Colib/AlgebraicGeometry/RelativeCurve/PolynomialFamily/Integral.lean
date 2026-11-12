/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison

/-!
# Integral and Noetherian original polynomial parameter spaces

The polynomial parameter space is the literal pullback used by the principal family.
The existing canonical affine-space comparison supplies geometric integrality and smoothness
of the polynomial projection. Its base change is integral over an integral locally Noetherian
scheme and Noetherian over a Noetherian scheme; no replacement ambient scheme is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

/-- The original polynomial projection is geometrically integral through the existing
canonical comparison with native relative affine space. -/
theorem geometricallyIntegral_polynomialProjection (R : Type u) [CommRing R] :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) := by
  have h : IsPullback (polynomialAffineSpaceIso (.of R)).hom
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
      (AffineSpace (ULift.{u} Unit) (Spec (.of R)) ↘ Spec (.of R)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp only [Category.comp_id, polynomialAffineSpaceIso_hom_over]⟩
  exact MorphismProperty.of_isPullback h inferInstance
/-- The unchanged polynomial pullback over an integral locally Noetherian scheme is integral. -/
theorem isIntegral_parameterSpace {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R))
    [IsIntegral X] [IsLocallyNoetherian X] : IsIntegral (parameterSpace p) := by
  have : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) :=
    geometricallyIntegral_polynomialProjection R
  have : Smooth
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) := by
    rw [← polynomialAffineSpaceIso_hom_over (.of R)]
    infer_instance
  infer_instance
/-- The unchanged polynomial pullback over a Noetherian scheme is Noetherian. -/
theorem isNoetherian_parameterSpace {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R))
    [IsNoetherian X] : IsNoetherian (parameterSpace p) := by
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) := by
    rw [← polynomialAffineSpaceIso_hom_over (.of R)]
    infer_instance
  have : LocallyOfFiniteType (projection p) := inferInstance
  have : QuasiCompact (projection p) := inferInstance
  have : CompactSpace (parameterSpace p) := QuasiCompact.compactSpace_of_compactSpace (projection p)
  have : IsLocallyNoetherian (parameterSpace p) :=
    LocallyOfFiniteType.isLocallyNoetherian (projection p)
  exact {}

end AlgebraicGeometry.PrincipalFamilyUnitOpen
