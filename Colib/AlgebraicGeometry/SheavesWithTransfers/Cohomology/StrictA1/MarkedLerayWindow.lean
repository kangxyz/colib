/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.LerayWindow
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.FiberDetection

/-!
# Finite-degree ordinary projection from actual marked cylinder vanishing

The marked-fiber and finite Leray steps are composed here, independently of the
geometric rank and degree inductions. The window is `0 < q ≤ N` for
bijectivity and `0 < q < N` for injectivity of the ordinary projection.

Extracted from `Motivic/Cohomology/A1/StrictInvariance/DegreeInduction.lean`
at `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`, blob
`4682a11fc6e866da5214677f7c98a9646226d008`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X).left)
      AddCommGrpCat.{u + 1})]

/-- Actual test-object cylinder vanishing through degree `N` makes the literal
ordinary projection in degree `N` bijective. -/
theorem a1_projection_bijective_of_marked_cylinder_window
    (hF : F.obj.IsA1Invariant) (N : ℕ)
    (hCylinder : ∀ q : ℕ, 0 < q → q ≤ N →
      ∀ (V : EtaleSeparatedFiniteType X.left) (z : V.left),
        IsZero (colimit (pointedCylinderValues (.of k) (X := (toSmoothSite X).obj V)
          (residuePoint V.left z)
          (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) q)
          (pointedBase (.of k) (X := (toSmoothSite X).obj V) (residuePoint V.left z))))) :
    Function.Bijective (A1.projectionPullback (.of k)
      (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) N) X) := by
  apply a1_projection_bijective_of_rightDerived_window X F hF N
  intro q hq hqN
  exact projectionHigherImage_isZero_of_residueCylinderColimits (.of k) X
    ((toSheaf k).obj F) q (hCylinder q hq hqN)

/-- The endpoint-free original cylinder window already makes the same ordinary
projection injective. No degree-`N` vanishing is requested. -/
theorem a1_projection_injective_of_marked_cylinder_window
    (hF : F.obj.IsA1Invariant) (N : ℕ)
    (hCylinder : ∀ q : ℕ, 0 < q → q < N →
      ∀ (V : EtaleSeparatedFiniteType X.left) (z : V.left),
        IsZero (colimit (pointedCylinderValues (.of k) (X := (toSmoothSite X).obj V)
          (residuePoint V.left z)
          (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) q)
          (pointedBase (.of k) (X := (toSmoothSite X).obj V) (residuePoint V.left z))))) :
    Function.Injective (A1.projectionPullback (.of k)
      (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) N) X) := by
  apply a1_projection_injective_of_rightDerived_window X F hF N
  intro q hq hqN
  exact projectionHigherImage_isZero_of_residueCylinderColimits (.of k) X
    ((toSheaf k).obj F) q (hCylinder q hq hqN)

end AlgebraicGeometry.SheafWithTransfers
