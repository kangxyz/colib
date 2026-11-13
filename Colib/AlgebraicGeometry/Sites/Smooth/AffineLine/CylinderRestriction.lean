/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # The actual change of base of the smooth affine cylinder -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

variable {S : Scheme.{u}}

local notation "π" => projection (SmoothSite.additiveGroupObject S)

/-- Changing the base of the actual affine cylinder forms its projection
pullback square. -/
theorem affineLineCylinder_map_isPullback {U X : SmoothSite S} (j : U ⟶ X) :
    IsPullback (affineLineCylinder.map j).left ((π).app U).left ((π).app X).left j.left := by
  let T := SmoothSite.additiveGroupObject S
  change IsPullback (SmoothSite.productMap j (𝟙 T)).left
    (SmoothSite.productFst U T).left (SmoothSite.productFst X T).left j.left
  apply IsPullback.of_right (h₁₂ := (SmoothSite.productSnd X T).left)
    (h₂₂ := X.hom) (v₁₃ := T.hom)
  · have h := congrArg (fun f ↦ f.left) (SmoothSite.productMap_snd j (𝟙 T))
    change (SmoothSite.productMap j (𝟙 T)).left ≫ (SmoothSite.productSnd X T).left =
      (SmoothSite.productSnd U T).left ≫ 𝟙 T.left at h
    rw [h, Category.comp_id, MorphismProperty.Over.w j]
    exact (IsPullback.of_hasPullback U.hom T.hom).flip
  · exact congrArg (fun f ↦ f.left) (SmoothSite.productMap_fst j (𝟙 T))
  · exact (IsPullback.of_hasPullback X.hom T.hom).flip

variable {U U' T X : SmoothSite S} (l : U' ⟶ U) (e : T ≅ affineLineCylinder.obj U)
  (m : X ⟶ T) (b : X ⟶ U')
  (H : IsPullback (m ≫ e.hom).left b.left
    ((projection (SmoothSite.additiveGroupObject S)).app U).left l.left)

private theorem cylinderComparisonLeftIso_hom_map :
    (H.isoPullback ≪≫ (affineLineCylinder_map_isPullback l).isoPullback.symm).hom ≫
      (affineLineCylinder.map l).left =
      (m ≫ e.hom).left := by
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    (affineLineCylinder_map_isPullback l).isoPullback_inv_fst, H.isoPullback_hom_fst]

/-- The literal scheme pullback of the original cylinder is its actual smooth
site cylinder over the restricted coefficient base. -/
def cylinderComparisonIso : X ≅ affineLineCylinder.obj U' :=
  MorphismProperty.Over.isoMk
    (H.isoPullback ≪≫ (affineLineCylinder_map_isPullback l).isoPullback.symm) (by
    rw [← MorphismProperty.Over.w (affineLineCylinder.map l), ← Category.assoc,
      cylinderComparisonLeftIso_hom_map, MorphismProperty.Over.w])

/-- The comparison preserves the original inclusion into the old cylinder. -/
@[reassoc]
theorem cylinderComparisonIso_hom_map :
    (cylinderComparisonIso l e m b H).hom ≫ affineLineCylinder.map l = m ≫ e.hom :=
  MorphismProperty.Over.Hom.ext (cylinderComparisonLeftIso_hom_map l e m b H)

end AlgebraicGeometry.Scheme.SmoothSite.Contraction
