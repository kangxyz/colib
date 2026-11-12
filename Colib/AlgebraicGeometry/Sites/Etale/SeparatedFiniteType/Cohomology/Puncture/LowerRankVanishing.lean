/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Puncture.PointVanishing
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Puncture.LowerRankPersistent
public import Colib.AlgebraicGeometry.Scheme.Stalk.Dimension.Generization

/-! # Lower local rank induction supplies the persistent puncture fibers -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Puncture/LowerRankPersistent.lean`, blob
`11ba2f254a2a6f5de767028d267ad2d5d95050ee`.
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

/-- The inner local-rank induction now supplies every persistent puncture fiber;
only the independent original restriction mono and puncture geometry remain. -/
theorem projectionPointFiber_isZero_of_lowerRank [IsOpenImmersion j.left]
    (hF : F.obj.IsA1Invariant) (n d : ℕ)
    (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = d)
    (hmiss : b p ∉ Set.range j.left)
    (hLow : ∀ q : ℕ, 0 < q → q < n + 1 →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hIH : LowerRankCylinderGermsZero F (n + 1) d)
    [Mono (colim.map (pointedCylinderRestriction (.of k) j (relativeFieldPoint b K (𝟙 _))
      (cohomologyPresheaf.{u + 1, u + 1} ((SheafWithTransfers.toSheaf k).obj F)
          (n + 1))))] :
    IsZero ((relativeFieldPoint b K (𝟙 _)).sheafFiber.obj
      (((directImage
        ((SmoothSite.Contraction.projection
          (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).left
        ).rightDerived (n + 1)).obj
        ((restrict ((SmoothSite.Contraction.affineLineCylinder.obj X)) AddCommGrpCat.{u + 1}).obj
          ((SheafWithTransfers.toSheaf k).obj F)))) :=
  projectionPointFiber_isZero_of_persistent_puncture j K b p F hF n hLow
    (persistentPunctureImageZero_of_lowerRank j K b p F (n + 1) d hd hmiss hIH)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
