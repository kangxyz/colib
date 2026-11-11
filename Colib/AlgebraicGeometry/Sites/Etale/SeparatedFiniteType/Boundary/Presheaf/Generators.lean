/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.Cokernel

/-! # Original punctured sections jointly detect maps out of the actual boundary -/
/-!
Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/Generators.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `7f92491f34839fb0e5df1e1da8c1d034889a756c`. All generator and image-sieve maps use the
actual native Laurent cylinder and closed inverse-image boundary.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {B : Scheme.{u}} (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  {U Y Z : SmoothSite B} (j : U ⟶ Y) (i : Z ⟶ Y)

/-- The genuine generator map uses the original quotient, sheafification and inverse-image unit. -/
def presheafBoundaryGenerator :
    (baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P ⟶
      ((directImage i.left).obj (presheafBoundary P j i)).obj :=
  presheafBoundaryProjection P j ≫
    ((imageAdjunction i.left).unit.app (presheafBoundaryAmbient P j)).hom

/-- Right cancellation against original punctured-section generators suffices. This follows
from the actual inverse-image adjunction, sheafification and the original cokernel. -/
theorem presheafBoundary_hom_ext
    {G : Sheaf (nisnevichTopology Z.left) AddCommGrpCat.{u + 1}}
    {f g : presheafBoundary P j i ⟶ G}
    (h : presheafBoundaryGenerator P j i ≫ ((directImage i.left).map f).hom =
      presheafBoundaryGenerator P j i ≫ ((directImage i.left).map g).hom) : f = g := by
  apply ((imageAdjunction i.left).homEquiv _ _).injective
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (nisnevichTopology Y.left) _ _
    ((directImage i.left).obj G).property
  apply (cancel_epi (cokernel.π (presheafBoundaryRestriction P j))).mp
  simpa only [Adjunction.homEquiv_unit, ObjectProperty.FullSubcategory.comp_hom,
    presheafBoundaryGenerator,
    presheafBoundaryProjection, Category.assoc] using h

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary

