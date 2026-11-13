/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.MarkedComparison
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.Marked.PointDetection

/-!
# Actual cylinder germs detect the higher image of the literal projection

This is the marked-fiber step of
`Motivic/Cohomology/A1/StrictInvariance/DegreeInduction.lean` at
`kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`, blob
`4682a11fc6e866da5214677f7c98a9646226d008`.
Vanishing of the cylinder colimits at the marked points of the étale test
objects detects the vanishing of the higher image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X).left)
      AddCommGrpCat.{u + 1})]

/-- Vanishing of the original cylinder germs on all actual test objects kills
the genuine higher direct image. Base residue points alone are not substituted. -/
theorem projectionHigherImage_isZero_of_residueCylinderColimits (n : ℕ)
    (h : ∀ (V : EtaleSeparatedFiniteType X.left) (z : V.left),
      IsZero (colimit (pointedCylinderValues R (X := (toSmoothSite X).obj V)
        (residuePoint V.left z) (cohomologyPresheaf.{u + 1, u + 1} F n)
        (pointedBase R (X := (toSmoothSite X).obj V) (residuePoint V.left z))))) :
    IsZero (((directImage
      ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app X).left
        ).rightDerived n).obj
      ((restrict (SmoothSite.Contraction.affineLineCylinder.obj X)
        AddCommGrpCat.{u + 1}).obj F)) := by
  apply isZero_of_all_marked_residue_fibers
  intro V z
  exact markedProjectionFiber_isZero_of_cylinderColimit R X V z F n (h V z)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
