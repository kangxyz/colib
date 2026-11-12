/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.PointedBaseOrdinary
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.Basic

/-! # Current-degree homotopy invariance kills actual projection point fibers -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/HigherImages/PointFiberHI.lean`, blob
`3abcf3771b274f658d49fe84ec8170ffd1821ed9`.
This is the original explicitly degree-indexed intermediate implication. In the
outer induction it is applied only to a previously proved positive degree,
including that of the actual contraction. It is not a strict-invariance theorem
with a current-degree HI premise.
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
variable (k : Type u) [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Only the explicitly specified positive degree is assumed homotopy invariant. -/
theorem projectionPointFiber_isZero_of_cohomology_HI
    (X : SmoothSite (Spec (.of k)))
    (Φ : (nisnevichTopology X.left).Point.{u + 1})
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (h : (SheafCohomology.withTransfers k F (n + 1)).IsA1Invariant)
    [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf
      (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X).left)
        AddCommGrpCat.{u + 1})] :
    IsZero (Φ.sheafFiber.obj
      (((directImage
        ((SmoothSite.Contraction.projection
          (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).left).rightDerived (n + 1)).obj
        ((restrict (SmoothSite.Contraction.affineLineCylinder.obj X) AddCommGrpCat.{u + 1}).obj
          ((SheafWithTransfers.toSheaf k).obj F)))) := by
  let A := (SheafWithTransfers.toSheaf k).obj F
  let P := cohomologyPresheaf.{u + 1, u + 1} A (n + 1)
  have hi (Y : SmoothSite (Spec (.of k))) :
      IsIso (A1.projectionPullback (.of k) P Y) :=
    (NatIso.isIso_map_iff (SheafCohomology.withTransfersGraphIso k F (n + 1))
      ((SmoothSite.Contraction.projection
        (SmoothSite.additiveGroupObject (Spec (.of k)))).app Y).op).mp (h Y)
  have happ (V : Φ.fiber.Elementsᵒᵖ) :
      IsIso ((pointedProjection (.of k) Φ P (pointedBase (.of k) Φ)).app V) :=
    hi _
  let : IsIso (pointedProjection (.of k) Φ P (pointedBase (.of k) Φ)) :=
    NatIso.isIso_of_isIso_app _
  have hz := pointedBaseColimit_isZero_succ (.of k) X Φ A n
  have hc : IsZero (colimit (pointedCylinderValues (.of k) Φ P
      (pointedBase (.of k) Φ))) :=
    hz.of_iso (colim.mapIso (asIso
      (pointedProjection (.of k) Φ P (pointedBase (.of k) Φ)))).symm
  exact hc.of_iso (pointedCylinderColimitFiberIso (.of k) X Φ A (n + 1)).symm

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
