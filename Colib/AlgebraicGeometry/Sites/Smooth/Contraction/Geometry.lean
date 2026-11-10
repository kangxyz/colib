/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Torus

/-!
# The native Laurent cylinders used by contraction

The parameter objects are the existing native Stacks group-scheme base changes.
The restriction is their existing positive Laurent open, and the unit section
is the existing point representing one. No alternative torus model is introduced.

Adapted from `motivic_source_a6805c4`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/AffineLine/Laurent.lean`, and the
literal parameter functor in `Smooth/Products/ParameterProducts.lean`.
Only the geometric producer is supplied here, not a sheaf or invariance theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

variable {S : Scheme.{u}}

/-- The literal relative product with a smooth parameter. -/
def parameterProduct (T : SmoothSite S) : SmoothSite S ⥤ SmoothSite S where
  obj X := product X T
  map f := productMap f (𝟙 T)
  map_id X := productMap_id X T
  map_comp f g := by simpa using productMap_comp f g (𝟙 T) (𝟙 T)

/-- A parameter map acts on the second factor of the actual relative product. -/
def parameterMap {T T' : SmoothSite S} (g : T ⟶ T') :
    parameterProduct T ⟶ parameterProduct T' where
  app X := productMap (𝟙 X) g
  naturality _ _ _ := by apply product_hom_ext <;> simp [parameterProduct]

/-- Projection of the actual parameter product to its source. -/
def projection (T : SmoothSite S) : parameterProduct T ⟶ 𝟭 (SmoothSite S) where
  app X := productFst X T
  naturality _ _ _ := by simp [parameterProduct]

/-- The structural morphism to the actual base object. -/
def toBase (X : SmoothSite S) : X ⟶ base S :=
  homMk X.hom (Category.comp_id _)

@[reassoc (attr := simp)]
theorem comp_toBase {X Y : SmoothSite S} (f : X ⟶ Y) :
    f ≫ toBase Y = toBase X :=
  MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w f)

/-- The affine-line cylinder uses the existing additive group object. -/
abbrev affineLineCylinder : SmoothSite S ⥤ SmoothSite S :=
  parameterProduct (additiveGroupObject S)

/-- The punctured cylinder uses the existing multiplicative group object. -/
abbrev torusCylinder : SmoothSite S ⥤ SmoothSite S :=
  parameterProduct (multiplicativeGroupObject S)

/-- The actual positive Laurent open on every relative cylinder. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/AffineLine/Laurent.lean:88-90"
  "adaptation" "Relative cylinders of the existing native positive Laurent open"]
def openInclusion : torusCylinder (S := S) ⟶ affineLineCylinder :=
  parameterMap (multiplicativeGroupOpen S)

theorem openInclusion_app (X : SmoothSite S) :
    openInclusion.app X = productMap (𝟙 X) (multiplicativeGroupOpen S) := rfl

/-- The underlying map is the actual pullback map of the positive Laurent open. -/
theorem openInclusion_app_left (X : SmoothSite S) :
    (openInclusion.app X).left =
      pullback.map X.hom (multiplicativeGroupObject S).hom
        X.hom (additiveGroupObject S).hom (𝟙 X.left)
        (multiplicativeGroupOpen S).left (𝟙 S)
        (by simp) ((Category.comp_id _).trans
          (MorphismProperty.Over.w (multiplicativeGroupOpen S)).symm) := by
  apply pullback.hom_ext <;>
    simp [openInclusion, parameterMap, productMap, productLift, productFst, productSnd]

instance openInclusion_isOpenImmersion (X : SmoothSite S) :
    IsOpenImmersion (openInclusion.app X).left := by
  rw [openInclusion_app_left]
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion (𝟙 X.left))
    (inferInstance : IsOpenImmersion (multiplicativeGroupOpen S).left)
    (by simp) (MorphismProperty.Over.w (multiplicativeGroupOpen S)).symm

/-- The existing unit point induces a section of each punctured cylinder. -/
def unitSection : 𝟭 (SmoothSite S) ⟶ torusCylinder where
  app X := productLift (𝟙 X) (toBase X ≫ torusOne S)
  naturality X Y f := by
    change f ≫ productLift (𝟙 Y) (toBase Y ≫ torusOne S) =
      productLift (𝟙 X) (toBase X ≫ torusOne S) ≫ productMap f (𝟙 _)
    apply product_hom_ext <;> simp [Category.assoc]

/-- The affine section is the image of the same genuine unit point. -/
def affineOneSection (X : SmoothSite S) : X ⟶ affineLineCylinder.obj X :=
  productLift (𝟙 X) (toBase X ≫ torusOne S ≫ multiplicativeGroupOpen S)

@[reassoc (attr := simp)]
theorem unitSection_projection (X : SmoothSite S) :
    unitSection.app X ≫ (projection (multiplicativeGroupObject S)).app X = 𝟙 X :=
  productLift_fst _ _

@[reassoc (attr := simp)]
theorem openInclusion_projection (X : SmoothSite S) :
    openInclusion.app X ≫ (projection (additiveGroupObject S)).app X =
      (projection (multiplicativeGroupObject S)).app X := by
  simp [openInclusion, parameterMap, projection]

/-- Open restriction and the actual unit section give the same affine point. -/
@[reassoc (attr := simp)]
theorem unitSection_openInclusion (X : SmoothSite S) :
    unitSection.app X ≫ openInclusion.app X = affineOneSection X := by
  apply product_hom_ext <;>
    simp [unitSection, openInclusion, parameterMap, affineOneSection]

/-- The cylinder open retains the forward Laurent coordinate on its parameter. -/
theorem openInclusion_coordinate (X : SmoothSite S) :
    (openInclusion.app X).left.appTop
        ((productSnd X (additiveGroupObject S)).left.appTop
          (additiveGroupBaseChangeCoordinate S)) =
      (productSnd X (multiplicativeGroupObject S)).left.appTop
        (multiplicativeGroupBaseChangeCoordinate S).val := by
  have h := congrArg (fun f => f.left.appTop)
    (productMap_snd (𝟙 X) (multiplicativeGroupOpen S))
  simp only [MorphismProperty.Comma.comp_left, Scheme.Hom.comp_appTop] at h
  have he := ConcreteCategory.congr_hom h (additiveGroupBaseChangeCoordinate S)
  change (openInclusion.app X).left.appTop
      ((productSnd X (additiveGroupObject S)).left.appTop
        (additiveGroupBaseChangeCoordinate S)) =
    (productSnd X (multiplicativeGroupObject S)).left.appTop
      ((multiplicativeGroupOpen S).left.appTop (additiveGroupBaseChangeCoordinate S)) at he
  rw [multiplicativeGroupOpen_appTop_coordinate] at he
  exact he

end AlgebraicGeometry.Scheme.SmoothSite.Contraction
