/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.Basic
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.Basic

/-!
# The actual transfer comparison preserves the affine-line projection

This is the graph-comparison step used by
`Motivic/Cohomology/A1/StrictInvariance/DegreeInduction.lean` at
`kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`, blob
`4682a11fc6e866da5214677f7c98a9646226d008`.
The ordinary cohomology theory, actual projection and Ext universe are retained.
The source does not prove positive-degree invariance.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe w u

namespace AlgebraicGeometry.SheafCohomology

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
  [HasExt.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The canonical transfer structure and native ordinary cohomology test exactly
the same affine-line projection in each degree. -/
theorem withTransfers_isA1Invariant_iff (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    (withTransfers k F n).IsA1Invariant ↔
      A1.IsInvariant (.of k)
        (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) n) := by
  constructor
  · intro h X
    exact (NatIso.isIso_map_iff (withTransfersGraphIso k F n)
      ((SmoothSite.Contraction.projection
        (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).op).mp (h X)
  · intro h X
    exact (NatIso.isIso_map_iff (withTransfersGraphIso k F n)
      ((SmoothSite.Contraction.projection
        (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).op).mpr (h X)

end AlgebraicGeometry.SheafCohomology
