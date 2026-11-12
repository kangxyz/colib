/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.Ordinary

/-!
Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Cohomology/Basic.lean`, blob `08d0ede205f3816f0734d3e5864398bd8e16fc4c`.

 # Canonical transfers on original ordinary cohomology

The transfer Ext universe is supplied internally by proved enough injectives.
Only the original ordinary cohomology's own HasExt bookkeeping is exposed.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite
universe w u
namespace AlgebraicGeometry.SheafCohomology
open _root_.AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE
variable (k : Type u) [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Original ordinary cohomology carries signed transfers without extra Ext assumptions. -/
def withTransfers (F : SheafWithTransfers.{u + 1} k) (n : ℕ) : PresheafWithTransfers.{w} k := by
  let : HasExt.{u + 1} (SheafWithTransfers.{u + 1} k) := hasExt_of_enoughInjectives _
  exact SheafWithTransfers.ordinaryCohomologyTransfers.{u + 1, w, u} k F n

/-- Its graph restriction is the original ordinary cohomology presheaf. -/
def withTransfersGraphIso (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    (PresheafWithTransfers.toPresheaf k).obj (withTransfers k F n) ≅
      cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) n := by
  let : HasExt.{u + 1} (SheafWithTransfers.{u + 1} k) := hasExt_of_enoughInjectives _
  exact SheafWithTransfers.ordinaryCohomologyTransfersGraphIso.{u + 1, w, u} k F n

/-- The graph action is literally the original restriction, with no cohomology replacement. -/
theorem withTransfers_graph (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y)
    (e : (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) n).obj (op Y)) :
    (withTransfers k F n).transfer ((Cor.graphFunctor k).map f) e =
      (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) n).map f.op e := by
  let : HasExt.{u + 1} (SheafWithTransfers.{u + 1} k) := hasExt_of_enoughInjectives _
  exact SheafWithTransfers.ordinaryCohomologyTransfers_graph.{u + 1, w, u} k F n f e

/-- Ordinary coefficient maps are genuine morphisms of presheaves with transfers. -/
def withTransfersMap {F G : SheafWithTransfers.{u + 1} k} (a : F ⟶ G) (n : ℕ) :
    withTransfers k F n ⟶ withTransfers k G n := by
  let : HasExt.{u + 1} (SheafWithTransfers.{u + 1} k) := hasExt_of_enoughInjectives _
  exact SheafWithTransfers.ordinaryCohomologyTransfersMap.{u + 1, w, u} k n a

end AlgebraicGeometry.SheafCohomology
