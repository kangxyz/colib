/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Original.FirstObstructionNaturality
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.LerayWindow
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.HigherImages.ProjectionHI

/-!
# First-obstruction lifting for homotopy-invariant coefficients

Homotopy invariance of the lower cohomology groups supplies the Leray
window for the original affine-line projection.

Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Obstruction/LiftHI.lean`, blob
`8304891d23c1e0adc900f9b17885c1f59e4e4c9a`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme Stacks.Cohomology.FreeYonedaUnivLE
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1}
    (Sheaf (Scheme.EtaleSeparatedFiniteType.nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1}
    (Sheaf (Scheme.EtaleSeparatedFiniteType.nisnevichTopology
      (SmoothSite.Contraction.affineLineCylinder.obj X).left) AddCommGrpCat.{u + 1})]

local notation "cylinder" => (SmoothSite.Contraction.affineLineCylinder.obj X)
set_option quotPrecheck false in
local notation "projection" =>
  ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X)

/-- Lower-degree ordinary HI gives the actual lower positive right-image window. -/
theorem a1_lower_rightDerived_isZero (N : ℕ)
    (hLow : ∀ q : ℕ, 0 < q → q < N →
      (SheafCohomology.withTransfers k F q).IsA1Invariant) :
    ∀ q : ℕ, 0 < q → q < N →
      IsZero (((directImage (projection).left).rightDerived q).obj
        ((restrict cylinder
            AddCommGrpCat.{u + 1}).obj
          ((toSheaf k).obj F))) := by
  intro q hq hqN
  cases q with
  | zero => omega
  | succ n => exact projectionHigherImage_isZero_of_cohomology_HI k X F n (hLow _ hq hqN)

/-- Only persistent germs of the actual first obstruction remain as the inner-rank input.
Both the degree-zero coefficient iso and the lower higher-image window are proved from HI. -/
theorem a1_exists_open_originalRestriction_lift
    (hF : F.obj.IsA1Invariant) (N : ℕ) (hN : 0 < N)
    (hLow : ∀ q : ℕ, 0 < q → q < N →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (V : EtaleSeparatedFiniteType X.left) [IsNoetherian V.left]
    {Z : Scheme.{u}} (g : V.left ⟶ Z) (z : Z)
    (α : (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) N).obj
      (Opposite.op ((toSmoothSite cylinder).obj ((baseChange (projection).left).obj V))))
    (hα : ∀ y : V.left, g y ⤳ z →
      markedSectionGerm
        (((directImage (projection).left).rightDerived N).obj
          ((restrict cylinder
              AddCommGrpCat.{u + 1}).obj
            ((toSheaf k).obj F))).obj V y
        (originalFirstObstruction (projection)
          ((toSheaf k).obj F) N V α) = 0) :
    ∃ O : Z.Opens, z ∈ O ∧ ∃ β,
      (cohomologyPresheaf.{u + 1, u + 1}
        ((toSheaf k).obj F) N).map
          ((restrictionProjection (projection)).app
            (testOpenObject V (g ⁻¹ᵁ O))).op β =
      (cohomologyPresheaf.{u + 1, u + 1}
        ((toSheaf k).obj F) N).map
          ((toSmoothSite cylinder).map
            ((baseChange (projection).left).map
              (testOpenInclusion V (g ⁻¹ᵁ O)))).op α := by
  let := a1_coefficient_isIso X F hF
  exact exists_open_originalRestriction_lift_of_persistent_obstruction_germs
    projection ((toSheaf k).obj F) N hN V g z
      (a1_lower_rightDerived_isZero X F N hLow) α hα

end AlgebraicGeometry.SheafWithTransfers
