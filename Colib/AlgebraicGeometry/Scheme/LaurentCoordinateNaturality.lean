/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurent
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-! # Naturality of the native Laurent coordinate

The existing forward coordinate and its inverse evaluate to the images of `T 1` and
`T (-1)` under every ring morphism. No chosen coordinate-image compatibility is required.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

/-- The actual Laurent ring morphism induced by a coefficient morphism. -/
def laurentCoefficientMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    CommRingCat.of (LaurentPolynomial R) ⟶ CommRingCat.of (LaurentPolynomial S) :=
  CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom)

/-- Coefficient change fixes every Laurent monomial. -/
@[simp] theorem laurentCoefficientMap_T {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℤ) :
    (laurentCoefficientMap f).hom (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  change AddMonoidAlgebra.mapRingHom ℤ f.hom (AddMonoidAlgebra.single n 1) =
    AddMonoidAlgebra.single n 1
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

/-- The existing coordinate is the global section determined by the forward monomial. -/
theorem laurentCoordinate_val (R : CommRingCat.{u}) :
    (laurentCoordinate R).val =
      (ΓSpecIso (.of (LaurentPolynomial R))).inv.hom (LaurentPolynomial.T 1) := by
  simp only [laurentCoordinate, IsUnit.unit_spec]

/-- The inverse of the existing coordinate is the actual inverse monomial. -/
theorem laurentCoordinate_inv_val (R : CommRingCat.{u}) :
    ↑((laurentCoordinate R)⁻¹) =
      (ΓSpecIso (.of (LaurentPolynomial R))).inv.hom (LaurentPolynomial.T (-1)) := by
  apply Units.inv_eq_of_mul_eq_one_left
  rw [laurentCoordinate_val, ← map_mul, ← LaurentPolynomial.T_add]
  simp

/-- Arbitrary affine pullback takes the forward coordinate to the actual image of `T`. -/
theorem laurentCoordinate_image {R S : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S) :
    ↑(Units.map (Spec.map h).appTop.hom.toMonoidHom (laurentCoordinate R)) =
      (ΓSpecIso S).inv.hom (h.hom (LaurentPolynomial.T 1)) := by
  change (Spec.map h).appTop.hom (laurentCoordinate R).val = _
  rw [laurentCoordinate_val]
  exact (ConcreteCategory.congr_hom (ΓSpecIso_inv_naturality h)
    (LaurentPolynomial.T 1)).symm

/-- Arbitrary affine pullback also takes the inverse to the image of `T (-1)`. -/
theorem laurentCoordinate_image_inv {R S : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S) :
    ↑((Units.map (Spec.map h).appTop.hom.toMonoidHom (laurentCoordinate R))⁻¹) =
      (ΓSpecIso S).inv.hom (h.hom (LaurentPolynomial.T (-1))) := by
  change (Spec.map h).appTop.hom (↑((laurentCoordinate R)⁻¹)) = _
  rw [laurentCoordinate_inv_val]
  exact (ConcreteCategory.congr_hom (ΓSpecIso_inv_naturality h)
    (LaurentPolynomial.T (-1))).symm

/-- Actual Laurent coefficient pullback preserves the existing forward coordinate unit. -/
theorem laurentCoordinate_coefficient {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Units.map (Spec.map (laurentCoefficientMap f)).appTop.hom.toMonoidHom
      (laurentCoordinate R) = laurentCoordinate S := by
  apply Units.ext
  rw [laurentCoordinate_image, laurentCoefficientMap_T, laurentCoordinate_val]

end AlgebraicGeometry.Scheme.PolynomialLaurent
