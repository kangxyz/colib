/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.OrdinaryComparison
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.OrdinaryColimit

/-! # The pointed cylinder diagram computes the existing genuine higher-image point fiber -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Cylinder/OrdinaryComparison.lean`, blob
`9869c01b930cc7c89cd0a004e66a114d59653563`.
Native mathematical objects, original coefficient universes, and actual displayed maps are retained.
Only the final higher-image fiber comparison is adapted here. The diagram comparison is imported
from its frozen native owner.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE
variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
  (Φ : (nisnevichTopology X.left).Point.{u + 1})
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X).left)
      AddCommGrpCat.{u + 1})]

/-- The actual cylinder germ is the actual higher-direct-image point fiber, with no new index. -/
def pointedCylinderColimitFiberIso (n : ℕ) :
    colimit (pointedCylinderValues R Φ
      (cohomologyPresheaf.{u + 1, u + 1} F n) (pointedBase R Φ)) ≅
      Φ.sheafFiber.obj (((directImage
        ((SmoothSite.Contraction.projection
          (SmoothSite.additiveGroupObject (Spec R))).app X).left).rightDerived n).obj
        ((restrict (SmoothSite.Contraction.affineLineCylinder.obj X) AddCommGrpCat).obj F)) :=
  colim.mapIso (pointedCylinderOrdinaryIso R X Φ F n) ≪≫
    (derivedDirectImagePointOrdinaryColimitIso
      ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app X).left Φ
      (injectiveResolution
        ((restrict (SmoothSite.Contraction.affineLineCylinder.obj X) AddCommGrpCat).obj F)) n).symm

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
