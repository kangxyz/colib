/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Puncture.ProjectionColimit
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.PointedBaseOrdinary

/-! # Genuine punctured projection lifts on the unchanged point index -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Puncture/PointVanishing.lean`, blob
`d51c028d5188833c18a497d17170d17282b79995`.
Actual native objects, original ordinary Ext, and displayed maps are retained.
The degree window is strictly lower where specified. No current-degree HI is
added to a final strict-invariance statement.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE
variable {k : Type u} [Field k] {X U : SmoothSite (Spec (.of k))} (j : U ⟶ X)
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))
  (F : SheafWithTransfers.{u + 1} k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology U.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf
    (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj U).left)
    AddCommGrpCat.{u + 1})]

variable [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf
    (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X).left)
    AddCommGrpCat.{u + 1})]

/-- Persistent puncture fibers and the independent original restriction mono force the
actual projection point fiber to vanish. The punctured comparison is now proved internally. -/
theorem projectionPointFiber_isZero_of_persistent_puncture
    (hF : F.obj.IsA1Invariant) (n : ℕ)
    (hLow : ∀ q : ℕ, 0 < q → q < n + 1 →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hG : PersistentPunctureImageZero j K b p F (n + 1))
    [Mono (colim.map (pointedCylinderRestriction (.of k) j (relativeFieldPoint b K (𝟙 _))
      (cohomologyPresheaf.{u + 1, u + 1} ((SheafWithTransfers.toSheaf k).obj F)
          (n + 1))))] :
    IsZero ((relativeFieldPoint b K (𝟙 _)).sheafFiber.obj
      (((directImage
        ((SmoothSite.Contraction.projection
          (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).left
        ).rightDerived (n + 1)).obj
        ((restrict ((SmoothSite.Contraction.affineLineCylinder.obj X)) AddCommGrpCat.{u + 1}).obj
          ((SheafWithTransfers.toSheaf k).obj F)))) := by
  let := pointedPunctureProjection_colimit_isIso j K b p F hF (n + 1)
    (Nat.succ_pos _) hLow hG
  exact pointedProjectionFiber_isZero_succ (.of k) X (relativeFieldPoint b K (𝟙 _))
    ((SheafWithTransfers.toSheaf k).obj F) j n

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
