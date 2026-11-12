/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.AffineLineRepresentative
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry
public import Colib.CategoryTheory.Sites.Simplicial.FreeCylinder
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Affine-line cylinders of smooth representables

The lifted pointed representable of the actual smooth affine-line product
identifies with the pointed cylinder. The comparison retains the original
scheme projection.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PointedSimplicialPresheaf Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (S : Scheme.{u})

private abbrev liftedSimplicialYoneda :
    SmoothSite S ⥤ (SmoothSite S)ᵒᵖ ⥤ SSet.{u + 1} :=
  CategoryTheory.uliftYoneda.{u + 1} ⋙ discretePresheaf (SmoothSite S)

private def liftedSimplicialYonedaProductIso (U V : SmoothSite S) :
    (liftedSimplicialYoneda S).obj (product U V) ≅
      (liftedSimplicialYoneda S).obj U ⨯ (liftedSimplicialYoneda S).obj V := by
  let F := liftedSimplicialYoneda S
  let : PreservesLimit (pair U V) F := by
    dsimp [F, liftedSimplicialYoneda, CategoryTheory.uliftYoneda, discretePresheaf]
    infer_instance
  exact F.mapIso (categoricalProductIso U V).symm ≪≫ PreservesLimitPair.iso F U V

@[reassoc]
private theorem liftedSimplicialYonedaProductIso_hom_fst (U V : SmoothSite S) :
    (liftedSimplicialYonedaProductIso S U V).hom ≫ prod.fst =
      (liftedSimplicialYoneda S).map (productFst U V) := by
  simp only [liftedSimplicialYonedaProductIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    PreservesLimitPair.iso_hom, Category.assoc, prodComparison_fst, ← Functor.map_comp,
    categoricalProductIso_inv_fst]

private theorem liftedSimplicialYonedaProductIso_inv_fst (U V : SmoothSite S) :
    (liftedSimplicialYonedaProductIso S U V).inv ≫
        (liftedSimplicialYoneda S).map (productFst U V) = prod.fst := by
  rw [← liftedSimplicialYonedaProductIso_hom_fst, Iso.inv_hom_id_assoc]

/-- The pointed affine-line cylinder on a lifted smooth representable is the lifted
pointed representable of its actual affine-line product. -/
@[no_expose]
def liftedAffineLineCylinderIso (U : SmoothSite S) :
    parameterizedCylinder ((liftedSmoothPointedYoneda S).obj U) (affineLineInterval S) ≅
      (liftedSmoothPointedYoneda S).obj ((Contraction.affineLineCylinder (S := S)).obj U) :=
  let e := uliftPointedYonedaIso.{u + 1} (SmoothSite S)
  let I := affineLineInterval S
  parameterizedCylinderIso (e.app U).symm I ≪≫
    freeCylinderIso ((liftedSimplicialYoneda S).obj U) I ≪≫
    (free (SmoothSite S)).mapIso
      (liftedSimplicialYonedaProductIso S U (additiveGroupObject S)).symm ≪≫
    e.app ((Contraction.affineLineCylinder (S := S)).obj U)

/-- The cylinder isomorphism carries its projection to the actual projection of
the smooth scheme product. -/
@[reassoc]
theorem liftedAffineLineCylinderIso_hom_projection (U : SmoothSite S) :
    (liftedAffineLineCylinderIso S U).hom ≫ (liftedSmoothPointedYoneda S).map
        ((Contraction.projection (additiveGroupObject S)).app U) =
      cylinderProjection ((liftedSmoothPointedYoneda S).obj U) (affineLineInterval S) := by
  let e := uliftPointedYonedaIso.{u + 1} (SmoothSite S)
  let F := liftedSimplicialYoneda S
  let V := additiveGroupObject S
  let I := F.obj V
  let f := productFst U V
  change (parameterizedCylinderIso (e.app U).symm I).hom ≫
      (freeCylinderIso (F.obj U) I).hom ≫
      (free (SmoothSite S)).map (liftedSimplicialYonedaProductIso S U V).inv ≫
      e.hom.app (product U V) ≫ (liftedSmoothPointedYoneda S).map f =
      cylinderProjection ((liftedSmoothPointedYoneda S).obj U) I
  rw [← e.hom.naturality f]
  change (parameterizedCylinderIso (e.app U).symm I).hom ≫
      (freeCylinderIso (F.obj U) I).hom ≫
      (free (SmoothSite S)).map (liftedSimplicialYonedaProductIso S U V).inv ≫
      (free (SmoothSite S)).map (F.map f) ≫ e.hom.app U = _
  rw [← Functor.map_comp_assoc, liftedSimplicialYonedaProductIso_inv_fst S U V,
    freeCylinderIso_projection_assoc]
  calc
    _ = ((parameterizedCylinderIso (e.app U).symm I).hom ≫
        cylinderProjection ((free (SmoothSite S)).obj (F.obj U)) I) ≫
        (e.app U).hom := (Category.assoc _ _ _).symm
    _ = (cylinderProjection ((liftedSmoothPointedYoneda S).obj U) I ≫
        (e.app U).symm.hom) ≫ (e.app U).hom :=
      congrArg (fun m => m ≫ (e.app U).hom)
        (parameterizedCylinderIso_hom_projection (e.app U).symm I)
    _ = _ := by simp

end AlgebraicGeometry.MotivicHomotopy
