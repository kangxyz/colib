/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.MarkedComparison
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Basic

/-! # Genuine punctured projection lifts on the unchanged point index -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Puncture/ProjectionLifts.lean`, blob
`d2d790bdc9d0ed40385739f28e6c699160ada68c`.
Native mathematical objects, original coefficient universes, and actual displayed maps are retained.
Only the original persistent-fiber vanishing proposition is extracted, not its punctured
projection-lift consumer.
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
  [HasExt.{u + 1} (Sheaf (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj U).left)
    AddCommGrpCat.{u + 1})]

/-- The remaining inner induction input is literal marked higher-image fiber vanishing
at the persistent points of each actual punctured neighborhood. -/
def PersistentPunctureImageZero (N : ℕ) : Prop :=
  ∀ (V : EtaleSeparatedFiniteType X.left) (a : (relativeFieldPoint b K (𝟙 _)).fiber.obj V)
    (y : ((baseChange j.left).obj V).left),
    pullback.fst V.hom j.left y ⤳ (relativeFieldPointFiberEquiv b K (𝟙 _) V a).left p →
      IsZero ((markedResiduePoint ((baseChange j.left).obj V) y).sheafFiber.obj
        (((directImage (((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject
          (Spec (.of k)))).app U)).left).rightDerived N).obj
          ((restrict (SmoothSite.Contraction.affineLineCylinder.obj U) AddCommGrpCat.{u + 1}).obj
            ((SheafWithTransfers.toSheaf k).obj F))))

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
