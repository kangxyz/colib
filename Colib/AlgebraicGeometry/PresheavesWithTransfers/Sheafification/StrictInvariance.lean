/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.HomotopyInvariance
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.PerfectField

/-! # Strict A¹-invariance of Nisnevich sheafification over a perfect field

Adapted from `Motivic/Cohomology/A1/Sheafification/StrictInvariance.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The Nisnevich sheafification of a homotopy-invariant presheaf with
transfers over a perfect field is strictly A¹-invariant. -/
@[colib_tag "COL-1029", colib_ref "MVW2006" "Lecture 13, Theorem 13.8" "adaptation"
  "Strict A¹-invariance of the actual Nisnevich sheafification over a perfect field"]
theorem nisnevichSheafify_isStrictA1Invariant
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ((nisnevichSheafify k).obj P).IsStrictA1Invariant := by
  let F : SheafWithTransfers.{u + 1} k := (nisnevichSheafify k).obj P
  have hF : F.obj.IsA1Invariant := nisnevichSheafify_isA1Invariant P hP
  exact SheafWithTransfers.isStrictA1Invariant_of_perfect F hF

end AlgebraicGeometry.PresheafWithTransfers
