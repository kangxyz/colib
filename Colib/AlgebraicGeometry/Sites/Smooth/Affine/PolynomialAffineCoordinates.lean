/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.SmoothSite

/-! # Literal polynomial smooth objects and their affine coordinates

This is the dependency-minimal extraction of polynomial_structure and
polynomialAffineIso. It compares the existing original polynomial object only;
it does not introduce an alternative native affine-line or Laurent parameter.
The native-cylinder and scalar-puncture comparisons remain separate obligations.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
local instance : Algebra.Smooth k (Polynomial R) := by
  let : Algebra.Smooth R (Polynomial R) := {}
  exact Algebra.Smooth.comp k R (Polynomial R)

omit [Algebra.Smooth k R] in
/-- The relative polynomial structure map is the literal polynomial algebra map. -/
theorem polynomial_structure :
    Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)) =
        Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial R))) := by
  have h : CommRingCat.ofHom (algebraMap k R) ≫
      CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) =
        CommRingCat.ofHom (algebraMap k (Polynomial R)) := by
    ext r
    rfl
  rw [← Spec.map_comp, h]

/-- The relative polynomial object and its affine algebra model have the same
underlying scheme and the same structure morphism. -/
def polynomialAffineIso : lineSite (k := k) (R := R) ≅ affineSite k (Polynomial R) :=
  MorphismProperty.Over.isoMk (Iso.refl (Spec (.of (Polynomial R)))) (by
    change 𝟙 (Spec (.of (Polynomial R))) ≫
      (affineSite k (Polynomial R)).hom = (lineSite (k := k) (R := R)).hom
    exact (Category.id_comp _).trans (polynomial_structure k R).symm)

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
