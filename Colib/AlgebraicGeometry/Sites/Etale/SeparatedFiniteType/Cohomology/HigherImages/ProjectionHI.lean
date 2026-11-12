/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.HigherImages.PointFiberHI
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.Marked.PointDetection

/-!
# Higher projection images from cohomology homotopy invariance

Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/HigherImages/ProjectionHI.lean`, blob
`f30ef1d3f6b985be27a26f54796b352f870e2fd3`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable (k : Type u) [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The actual higher direct image sheaf is zero. The only homotopy-invariance
premise concerns this positive degree of the original ordinary cohomology PST. -/
theorem projectionHigherImage_isZero_of_cohomology_HI
    (X : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (h : (SheafCohomology.withTransfers k F (n + 1)).IsA1Invariant)
    [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf
      (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X).left)
      AddCommGrpCat.{u + 1})] :
    IsZero (((directImage
      ((SmoothSite.Contraction.projection
        (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).left
        ).rightDerived (n + 1)).obj
      ((restrict (SmoothSite.Contraction.affineLineCylinder.obj X)
        AddCommGrpCat.{u + 1}).obj
        ((SheafWithTransfers.toSheaf k).obj F))) := by
  apply isZero_of_all_marked_residue_fibers
  intro V z
  exact projectionPointFiber_isZero_of_cohomology_HI k X (markedResiduePoint V z) F n h

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
