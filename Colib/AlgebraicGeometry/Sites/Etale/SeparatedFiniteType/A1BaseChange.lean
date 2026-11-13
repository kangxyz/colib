/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Cokernel
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Actual affine-line base change of étale test objects -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/A1BaseChange.lean`, blob
`1cb18fa9f35e64832c2d8793463ab2e1086327b1`.
The active affine parameter is the existing native additive group object.
The actual pullback-pasting isomorphism preserves its literal projection.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open SmoothSite.Contraction
variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R)) (V : EtaleSeparatedFiniteType X.left)

/-- The actual base-changed test scheme is the actual affine-line cylinder over that test. -/
def a1BaseChangeIso :
    (toSmoothSite (affineLineCylinder.obj X)).obj
      ((baseChange ((projection (SmoothSite.additiveGroupObject (Spec R))).app X).left).obj V) ≅
        affineLineCylinder.obj ((toSmoothSite X).obj V) where
  hom := SmoothSite.homMk
    (pullbackRightPullbackFstIso X.hom (SmoothSite.additiveGroupObject (Spec R)).hom V.hom).hom (by
      change _ ≫ (pullback.fst (V.hom ≫ X.hom) _ ≫ (V.hom ≫ X.hom)) =
        pullback.snd V.hom (pullback.fst X.hom _) ≫ (pullback.fst X.hom _ ≫ X.hom)
      rw [pullbackRightPullbackFstIso_hom_fst_assoc]
      exact pullback.condition_assoc X.hom)
  inv := SmoothSite.homMk
    (pullbackRightPullbackFstIso X.hom (SmoothSite.additiveGroupObject (Spec R)).hom V.hom).inv (by
      change _ ≫ (pullback.snd V.hom (pullback.fst X.hom _) ≫
        (pullback.fst X.hom _ ≫ X.hom)) =
          pullback.fst (V.hom ≫ X.hom) _ ≫ (V.hom ≫ X.hom)
      simp only [pullbackRightPullbackFstIso_inv_snd_fst_assoc])
  hom_inv_id := by
    apply MorphismProperty.Over.Hom.ext
    exact Iso.hom_inv_id _
  inv_hom_id := by
    apply MorphismProperty.Over.Hom.ext
    exact Iso.inv_hom_id _

/-- The comparison preserves the original projection, not just the two scheme objects. -/
@[reassoc]
theorem a1BaseChangeIso_hom_projection :
    (a1BaseChangeIso R X V).hom ≫
        (projection (SmoothSite.additiveGroupObject (Spec R))).app ((toSmoothSite X).obj V) =
      (restrictionProjection
        ((projection (SmoothSite.additiveGroupObject (Spec R))).app X)).app V := by
  apply MorphismProperty.Over.Hom.ext
  exact pullbackRightPullbackFstIso_hom_fst _ _ _

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
