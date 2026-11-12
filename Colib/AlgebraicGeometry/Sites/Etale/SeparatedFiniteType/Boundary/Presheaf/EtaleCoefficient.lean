/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Etale.Pullback
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.Cokernel

/-! # Étale excision for the boundary of an original presheaf

These are the ambient and punctured comparisons before quotient or sheafification.
No sheaf or homotopy-invariance premise is used. Both projections of the actual
Cartesian scheme comparison are retained.
-/


/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/Boundary/Presheaf/EtaleExcision.lean`, blob
`3eec2b3bb94ba4e6e8f33dbbc18e649601bdd858`.
The canonical native objects and displayed maps are retained. Source candidate only.
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

/-- Original ambient sections are unchanged by étale postcomposition. -/
def presheafEtaleCoefficientIso :
    (etalePostcompose p.left).op ⋙ (toSmoothSite Y).op ⋙ P ≅
      (toSmoothSite Y').op ⋙ P :=
  Functor.isoWhiskerRight (NatIso.op (etaleToSmoothIso p).symm) P

/-- Original punctured sections compare through the actual Cartesian scheme isomorphism. -/
def presheafEtalePuncturedCoefficientIso :
    (etalePostcompose p.left).op ⋙ (baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P ≅
      (baseChange j'.left).op ⋙ (toSmoothSite U').op ⋙ P :=
  Functor.isoWhiskerRight (NatIso.op (etalePuncturedToSmoothIso j p j' q hpb)) P

/-- The Cartesian comparison commutes with restriction before any sheafification. -/
theorem presheafEtaleCoefficient_restriction :
    Functor.whiskerLeft (etalePostcompose p.left).op (presheafBoundaryRestriction P j) ≫
        (presheafEtalePuncturedCoefficientIso P j p j' q hpb).hom =
      (presheafEtaleCoefficientIso P p).hom ≫ presheafBoundaryRestriction P j' := by
  apply NatTrans.ext
  funext V
  change P.map ((restrictionProjection j).app
      ((etalePostcompose p.left).obj V.unop)).op ≫
      P.map ((etalePuncturedToSmoothIso j p j' q hpb).hom.app V.unop).op =
    P.map ((etaleToSmoothIso p).inv.app V.unop).op ≫
      P.map ((restrictionProjection j').app V.unop).op
  rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  change (puncturedNeighborhoodIso j p j' q hpb V.unop).hom ≫
      pullback.fst (V.unop.hom ≫ p.left) j.left =
    pullback.fst V.unop.hom j'.left ≫ 𝟙 V.unop.left
  rw [puncturedNeighborhoodIso_hom_fst]
  exact (Category.comp_id _).symm

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
