/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Polynomial.RationalCoordinateSection
public import Colib.RingTheory.Bertini.RelativePolynomialCoordinateAlgebra

/-! # A section through the original rational relative-coordinate mark -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry QuadraticIncidence MvPolynomial
universe u
namespace AlgebraicGeometry.Scheme

/-- The base mark is the original tail-coordinate image, not a newly selected point. -/
theorem exists_relativeCoordinate_section_through_rational_mark
    {E B : Type u} [CommRing E] [CommRing B] [Algebra E B]
    (d : ℕ) (f : Fin (d + 1) → B)
    (x : Spec (.of E) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) = 𝟙 _) :
    ∃ s : Spec (.of (MvPolynomial (Fin d) E)) ⟶
        Spec (.of (Polynomial (MvPolynomial (Fin d) E))),
      s ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = 𝟙 _ ∧
      x ≫ Spec.map (CommRingCat.ofHom (relativeCoordinateHom E B d f)) =
        (x ≫ Spec.map (CommRingCat.ofHom
          (aeval (R := E) (fun i : Fin d => f i.succ)).toRingHom)) ≫ s := by
  obtain ⟨s, η, hs, hmark⟩ :=
    exists_polynomial_section_through_rational_schemePoint
      (relativeCoordinateAlgHom E B d f) x hx
  have hη : x ≫ Spec.map (CommRingCat.ofHom
      (aeval (R := E) (fun i : Fin d => f i.succ)).toRingHom) = η := by
    have h := congrArg (fun z => z ≫ Spec.map
      (CommRingCat.ofHom (Polynomial.C : MvPolynomial (Fin d) E →+*
        Polynomial (MvPolynomial (Fin d) E)))) hmark
    simpa only [relativeCoordinateAlgHom_toRingHom, Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, relativeCoordinateHom_comp_C,
      hs, Category.comp_id] using h
  exact ⟨s, hs, hmark.trans (congrArg (fun z => z ≫ s) hη.symm)⟩

end AlgebraicGeometry.Scheme
