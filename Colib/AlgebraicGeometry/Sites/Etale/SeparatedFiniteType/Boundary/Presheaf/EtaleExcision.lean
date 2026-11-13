/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.EtaleCoefficient
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.EtaleLocalization
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory


/-! # Étale excision for the boundary of an original presheaf

The order is original punctured sections, objectwise quotient, small ordinary
sheafification, and genuine closed inverse image. No sheaf or homotopy-invariance
premise on the original presheaf is needed for this Cartesian comparison.
-/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/Boundary/Presheaf/EtaleExcision.lean`, blob
`3eec2b3bb94ba4e6e8f33dbbc18e649601bdd858`.
The first three ambient/punctured coefficient comparisons remain the frozen batch02 module. This
file adds only the actual quotient, sheafification and closed inverse-image comparisons.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {B : Scheme.{u}}
  (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  {U Y U' Y' : SmoothSite B}
  (j : U ⟶ Y) (p : Y' ⟶ Y) (j' : U' ⟶ Y') (q : U' ⟶ U)
  [Etale p.left] [IsSeparated p.left] [QuasiCompact p.left]
  (hpb : IsPullback q j' j p)

/-- Excision of the actual objectwise quotient, before sheafification. -/
def presheafNeighborhoodQuotientEtaleIso :
    (etalePostcompose p.left).op ⋙ presheafNeighborhoodQuotient P j ≅
      presheafNeighborhoodQuotient P j' :=
  PreservesCokernel.iso ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      (etalePostcompose p.left).op) (presheafBoundaryRestriction P j) ≪≫
    cokernel.mapIso _ _ (presheafEtaleCoefficientIso P p)
      (presheafEtalePuncturedCoefficientIso P j p j' q hpb)
      (presheafEtaleCoefficient_restriction P j p j' q hpb)

@[reassoc (attr := simp)]
theorem presheafNeighborhoodQuotientEtaleIso_π :
    Functor.whiskerLeft (etalePostcompose p.left).op
        (cokernel.π (presheafBoundaryRestriction P j)) ≫
        (presheafNeighborhoodQuotientEtaleIso P j p j' q hpb).hom =
      (presheafEtalePuncturedCoefficientIso P j p j' q hpb).hom ≫
        cokernel.π (presheafBoundaryRestriction P j') := by
  change ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      (etalePostcompose p.left).op).map (cokernel.π (presheafBoundaryRestriction P j)) ≫
      (presheafNeighborhoodQuotientEtaleIso P j p j' q hpb).hom = _
  simp only [presheafNeighborhoodQuotientEtaleIso, Iso.trans_hom,
    PreservesCokernel.π_iso_hom_assoc, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]

/-- Étale excision of the small sheafification of the original section quotient. -/
def presheafBoundaryAmbientEtaleIso :
    (etaleRestriction p.left).obj (presheafBoundaryAmbient P j) ≅
      presheafBoundaryAmbient P j' :=
  etaleSheafificationIso p.left (presheafNeighborhoodQuotient P j) ≪≫
    (presheafToSheaf (nisnevichTopology Y'.left) AddCommGrpCat.{u + 1}).mapIso
      (presheafNeighborhoodQuotientEtaleIso P j p j' q hpb)

/-- Every original punctured representative is preserved through quotient and unit. -/
@[reassoc (attr := simp)]
theorem presheafBoundaryAmbientEtaleIso_projection :
    Functor.whiskerLeft (etalePostcompose p.left).op (presheafBoundaryProjection P j) ≫
        (presheafBoundaryAmbientEtaleIso P j p j' q hpb).hom.hom =
      (presheafEtalePuncturedCoefficientIso P j p j' q hpb).hom ≫
        presheafBoundaryProjection P j' := by
  simp only [presheafBoundaryProjection, presheafBoundaryAmbientEtaleIso,
    Iso.trans_hom, Functor.mapIso_hom, ObjectProperty.FullSubcategory.comp_hom,
    Functor.whiskerLeft_comp, Category.assoc]
  dsimp only [presheafBoundaryAmbient, presheafNeighborhoodQuotient]
  rw [etaleSheafificationIso_unit_assoc]
  rw [← toSheafify_naturality, ← Category.assoc,
    presheafNeighborhoodQuotientEtaleIso_π]
  simp only [Category.assoc]

/-- Apply genuine closed inverse image after the ambient étale excision comparison. -/
def presheafBoundaryEtaleExcisionIso {Z : SmoothSite B} (i' : Z ⟶ Y') :
    presheafBoundary P j (i' ≫ p) ≅ presheafBoundary P j' i' :=
  ((inverseImageCompIso i'.left p.left).app (presheafBoundaryAmbient P j)).symm ≪≫
    (inverseImage i'.left).mapIso
      ((inverseImageEtaleIso p.left).app (presheafBoundaryAmbient P j)) ≪≫
    (inverseImage i'.left).mapIso (presheafBoundaryAmbientEtaleIso P j p j' q hpb)

include hpb in
/-- Boundary vanishing on an actual étale chart transfers along its specified closed lift. -/
theorem isZero_presheafBoundary_of_etale {Z : SmoothSite B} (i' : Z ⟶ Y')
    (h : IsZero (presheafBoundary P j' i')) :
    IsZero (presheafBoundary P j (i' ≫ p)) :=
  h.of_iso (presheafBoundaryEtaleExcisionIso P j p j' q hpb i')

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
