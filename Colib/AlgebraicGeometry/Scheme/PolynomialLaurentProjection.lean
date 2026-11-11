/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Scheme.LaurentInclusionSquare
public import Colib.RingTheory.Polynomial.LaurentSquare

/-! # The actual geometric coefficient projections and inverse Laurent chart -/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.PolynomialLaurent

/-- Projection induced by the actual polynomial constant inclusion. -/
def polynomialProjection (R : CommRingCat.{u}) : Spec (.of (Polynomial R)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

/-- Projection induced by the actual Laurent constant inclusion. -/
def laurentProjection (R : CommRingCat.{u}) : Spec (.of (LaurentPolynomial R)) ⟶ Spec R :=
  Spec.map (laurentCoefficientInclusion R)

/-- The inverse-coordinate chart sends the polynomial coordinate to `T (-1)`. -/
def laurentMinus (R : CommRingCat.{u}) :
    Spec (.of (LaurentPolynomial R)) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))

/-- The existing positive chart lies over the original coefficient ring. -/
theorem laurentToPolynomial_projection (R : CommRingCat.{u}) :
    laurentToPolynomial R ≫ polynomialProjection R = laurentProjection R := by
  rw [laurentToPolynomial, polynomialProjection, ← Spec.map_comp,
    CommRingCat.PolynomialLaurent.coefficient_toLaurent]
  rfl

/-- The inverse-coordinate chart has the same actual coefficient projection. -/
theorem laurentMinus_projection (R : CommRingCat.{u}) :
    laurentMinus R ≫ polynomialProjection R = laurentProjection R := by
  rw [laurentMinus, polynomialProjection, ← Spec.map_comp,
    CommRingCat.PolynomialLaurent.coefficient_toLaurent_invert]
  rfl

end AlgebraicGeometry.Scheme.PolynomialLaurent

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/BoundedFlatBassSquare.lean:28-42"
  "ingredient" "Original Bass-square use of geometric coefficient projections and the inverse \
    chart"]
  AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialProjection
  AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
  AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus
