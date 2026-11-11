/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.A1BaseChange
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry

/-! # The actual cylinder base-change comparison is natural in the original neighborhoods -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/A1BaseChangeNaturality.lean`, blob `4975c0e10364fbaa8203b3129d2d50f993d99f9f`.
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
variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))

/-- Naturality retains the original geometric maps of étale neighborhoods. -/
theorem a1BaseChangeIso_naturality {V W : EtaleSeparatedFiniteType X.left} (f : V ⟶ W) :
    (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).map
        ((baseChange ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app X).left).map f) ≫
      (a1BaseChangeIso R X W).hom =
    (a1BaseChangeIso R X V).hom ≫ SmoothSite.Contraction.affineLineCylinder.map ((toSmoothSite X).map f) := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  all_goals
    simp [a1BaseChangeIso, SmoothSite.Contraction.affineLineCylinder, SmoothSite.Contraction.parameterProduct, SmoothSite.productMap,
      SmoothSite.productLift, SmoothSite.productFst, SmoothSite.productSnd,
      toSmoothSite, baseChange, Category.assoc]

/-- The natural comparison identifies actual base change with literal neighborhood cylinders. -/
def a1BaseChangeNatIso :
    baseChange ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app X).left ⋙
        toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X) ≅
      toSmoothSite X ⋙ SmoothSite.Contraction.affineLineCylinder :=
  NatIso.ofComponents (a1BaseChangeIso R X) (fun f => a1BaseChangeIso_naturality R X f)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
