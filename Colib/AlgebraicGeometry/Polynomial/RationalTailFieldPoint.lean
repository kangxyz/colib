/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Polynomial.RationalCoordinateSection
public import Colib.AlgebraicGeometry.ResidueField.FieldPoint
/-! # Rational tail points retain their original ground-field residue

The rational-point hypothesis is explicit. Merely having a morphism from the
spectrum of E does not supply E-linearity. For a genuine E-rational point the
polynomial tail stays E-rational, so its actual image is closed over a finite
extension K and its native K-residue field is separable when E/K is separable.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme
/-- The tail of an actual rational algebra point is still rational over the same field. -/
theorem rationalPoint_polynomialTail_structure
    (E B : Type u) [Field E] [CommRing B] [Algebra E B] (d : ℕ)
    (f : Polynomial (MvPolynomial (Fin d) E) →ₐ[E] B)
    (x : Spec (.of E) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) = 𝟙 _) :
    (x ≫ Spec.map (CommRingCat.ofHom (f.toRingHom.comp Polynomial.C))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap E (MvPolynomial (Fin d) E))) = 𝟙 _ := by
  have hcomp : (f.toRingHom.comp Polynomial.C).comp
      (algebraMap E (MvPolynomial (Fin d) E)) = algebraMap E B := by
    ext a
    exact f.commutes a
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  exact hx
/-- Restrict scalars along the original coefficient extension, retaining the same tail. -/
theorem rationalPoint_polynomialTail_over_ground
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra E B] (d : ℕ)
    (f : Polynomial (MvPolynomial (Fin d) E) →ₐ[E] B)
    (x : Spec (.of E) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) = 𝟙 _) :
    (x ≫ Spec.map (CommRingCat.ofHom (f.toRingHom.comp Polynomial.C))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E))) =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) := by
  have hscalar : Spec.map (CommRingCat.ofHom
      (algebraMap K (MvPolynomial (Fin d) E))) =
      Spec.map (CommRingCat.ofHom (algebraMap E (MvPolynomial (Fin d) E))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K E)) := by
    rw [IsScalarTower.algebraMap_eq K E (MvPolynomial (Fin d) E),
      CommRingCat.ofHom_comp, Spec.map_comp]
  rw [hscalar, ← Category.assoc,
    rationalPoint_polynomialTail_structure E B d f x hx, Category.id_comp]

/-- The rational tail has closed actual image over the original finite ground extension. -/
theorem isClosed_rationalPoint_polynomialTail
    (K E B : Type u) [Field K] [Field E] [Algebra K E] [Module.Finite K E]
    [CommRing B] [Algebra E B] (d : ℕ)
    (f : Polynomial (MvPolynomial (Fin d) E) →ₐ[E] B)
    (x : Spec (.of E) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) = 𝟙 _) :
    IsClosed ({((x ≫ Spec.map (CommRingCat.ofHom (f.toRingHom.comp Polynomial.C)))
      (IsLocalRing.closedPoint E))} : Set (Spec (.of (MvPolynomial (Fin d) E)))) := by
  exact isClosed_image_of_finite_fieldPoint
    (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E)))) _
    (rationalPoint_polynomialTail_over_ground K E B d f x hx)

/-- The same tail image has separable residue for its native structural scalar action. -/
theorem isSeparable_rationalPoint_polynomialTail_residue
    (K E B : Type u) [Field K] [Field E] [Algebra K E] [Algebra.IsSeparable K E]
    [CommRing B] [Algebra E B] (d : ℕ)
    (f : Polynomial (MvPolynomial (Fin d) E) →ₐ[E] B)
    (x : Spec (.of E) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) = 𝟙 _) :
    let p := (x ≫ Spec.map (CommRingCat.ofHom (f.toRingHom.comp Polynomial.C)))
      (IsLocalRing.closedPoint E)
    letI := (fieldToResidue
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E)))) p).hom.toAlgebra
    Algebra.IsSeparable K ((Spec (.of (MvPolynomial (Fin d) E))).residueField p) := by
  exact isSeparable_residueField_of_fieldPoint
    (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E)))) _
    (rationalPoint_polynomialTail_over_ground K E B d f x hx)
/-- Extending the marking field does not change the actual tail image point. -/
theorem polynomialTail_fieldMark_image
    (E Ω B : Type u) [Field E] [Field Ω] [CommRing B] [Algebra E B]
    (φ : E →+* Ω) (d : ℕ)
    (f : Polynomial (MvPolynomial (Fin d) E) →ₐ[E] B)
    (x : Spec (.of E) ⟶ Spec (.of B)) :
    (Spec.map (CommRingCat.ofHom φ) ≫ x ≫
      Spec.map (CommRingCat.ofHom (f.toRingHom.comp Polynomial.C)))
      (IsLocalRing.closedPoint Ω) =
    (x ≫ Spec.map (CommRingCat.ofHom (f.toRingHom.comp Polynomial.C)))
      (IsLocalRing.closedPoint E) := by
  exact congrArg
    (fun p => (x ≫ Spec.map (CommRingCat.ofHom (f.toRingHom.comp Polynomial.C))) p)
    (Subsingleton.elim _ _)
end AlgebraicGeometry.Scheme
