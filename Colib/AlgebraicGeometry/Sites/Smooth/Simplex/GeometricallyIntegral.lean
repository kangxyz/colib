/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Sites.Smooth.Simplex.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Geometric integrality of the actual algebraic simplex

The barycentric quotient chart identifies the existing simplex with relative
affine space. Its structure morphism is geometrically integral over every
commutative coefficient ring. The product of an integral locally Noetherian
support with this simplex is therefore integral.

Implementation adapted from `kangxyz/motivic` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Simplex/ExteriorGeometry.lean`,
blob `9e935a2f613b5d91fea9571d077a9ae823a2aac4`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]

/-- The existing polynomial chart with its variables in the scheme universe. -/
def liftedPolynomialEquiv (n : ℕ) :
    CoordinateRing R n ≃ₐ[R] MvPolynomial (ULift.{u} (Fin n)) R :=
  (polynomialEquiv R n).trans (MvPolynomial.renameEquiv R Equiv.ulift.symm)

/-- The actual barycentric simplex is affine space over its coefficient ring. -/
def affineSpaceIso (n : ℕ) :
    Spec (.of (CoordinateRing R n)) ≅
      AffineSpace (ULift.{u} (Fin n)) (Spec (.of R)) :=
  Scheme.Spec.mapIso (liftedPolynomialEquiv R n).symm.toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of R)).symm

@[reassoc (attr := simp)]
theorem affineSpaceIso_hom_over (n : ℕ) :
    (affineSpaceIso R n).hom ≫
      (AffineSpace (ULift.{u} (Fin n)) (Spec (.of R)) ↘ Spec (.of R)) =
        structureMap R n := by
  simp only [affineSpaceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    AffineSpace.SpecIso_inv_over, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map]
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (liftedPolynomialEquiv R n).symm.commutes r

/-- The simplex structure map has geometrically integral fibers. -/
instance structureMap_geometricallyIntegral (n : ℕ) :
    GeometricallyIntegral (structureMap R n) := by
  have sq : IsPullback (affineSpaceIso R n).hom (structureMap R n)
      (AffineSpace (ULift.{u} (Fin n)) (Spec (.of R)) ↘ Spec (.of R))
      (𝟙 (Spec (.of R))) :=
    IsPullback.of_horiz_isIso ⟨by simp only [affineSpaceIso_hom_over, Category.comp_id]⟩
  exact MorphismProperty.of_isPullback sq inferInstance

/-- The current smooth-site simplex retains its geometrically integral structure map. -/
instance smoothSiteObj_geometricallyIntegral (n : ℕ) :
    GeometricallyIntegral (smoothSiteObj R n).hom :=
  inferInstanceAs (GeometricallyIntegral (structureMap R n))

/-- Integral locally Noetherian supports stay integral after adjoining a simplex factor. -/
instance integral_product {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V]
    (p : V ⟶ Spec (.of R)) (n : ℕ) :
    IsIntegral (Limits.pullback p (structureMap R n)) := inferInstance

end AlgebraicSimplex

attribute [colib_tag "COL-0388"]
  AlgebraicSimplex.affineSpaceIso
  AlgebraicSimplex.structureMap_geometricallyIntegral

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Simplex/ExteriorGeometry.lean:36-62" "adaptation"
  "The simplex chart over the base and its geometric integrality"]
  AlgebraicSimplex.structureMap_geometricallyIntegral
