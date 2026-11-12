/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Polynomial.RationalTailFieldPoint
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteSeparableRetainedEtaleSmoothSite
/-! # The actual polynomial tail supplies lower-dimensional induction data

The tail uses identity coordinates in exactly d variables. Its marking comes
from the same rational algebra point; the native coefficient-field residue is
separable even after extending the marking field. Its structure morphism stays
on the original K-site. No lower structural isomorphism is assumed or asserted.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- The lower tail has its actual dimension-d identity étale coordinates. -/
theorem polynomialTail_identityCoordinates_etale (E : Type u) [Field E] (d : ℕ) :
    (AlgHom.id E (MvPolynomial (Fin d) E)).toRingHom.Etale :=
  RingHom.Etale.of_bijective Function.bijective_id

/-- The original rational tail remains separable over E at its extended marking. -/
theorem isSeparable_polynomialTail_extendedMark_residue
    (E Ω B : Type u) [Field E] [Field Ω] [CommRing B] [Algebra E B]
    (φ : E →+* Ω) (d : ℕ)
    (f : Polynomial (MvPolynomial (Fin d) E) →ₐ[E] B)
    (x : Spec (.of E) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) = 𝟙 _) :
    let η := Spec.map (CommRingCat.ofHom φ) ≫ x ≫
      Spec.map (CommRingCat.ofHom (f.toRingHom.comp Polynomial.C))
    letI := (fieldToResidue
      (Spec.map (CommRingCat.ofHom (algebraMap E (MvPolynomial (Fin d) E))))
      (η (IsLocalRing.closedPoint Ω))).hom.toAlgebra
    Algebra.IsSeparable E ((Spec (.of (MvPolynomial (Fin d) E))).residueField
      (η (IsLocalRing.closedPoint Ω))) := by
  dsimp only
  rw [polynomialTail_fieldMark_image E Ω B φ d f x]
  exact isSeparable_rationalPoint_polynomialTail_residue E E B d f x hx

/-- The finite-coefficient tail is an object of the original K smooth site. -/
abbrev polynomialTailOriginalSite
    (K E : Type u) [Field K] [Field E] [Algebra K E]
    [Module.Finite K E] [Algebra.IsSeparable K E] (d : ℕ) :
    SmoothSite (Spec (.of K)) :=
  SmoothSite.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E))))

/-- Its actual coefficient structure restricts to the original K-structure. -/
theorem polynomialTailOriginalSite_coefficient_structure
    (K E : Type u) [Field K] [Field E] [Algebra K E]
    [Module.Finite K E] [Algebra.IsSeparable K E] (d : ℕ) :
    Spec.map (CommRingCat.ofHom (algebraMap E (MvPolynomial (Fin d) E))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K E)) =
        (polynomialTailOriginalSite K E d).hom := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq K E (MvPolynomial (Fin d) E)]
  rfl
end AlgebraicGeometry.Scheme
