/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Sheafification
public import Colib.Util.References
import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.Field
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.CylinderCriterion
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.WholeCylinderLifting

/-! # Homotopy invariance of Nisnevich sheafification with transfers

Adapted from `Motivic/Cohomology/A1/Sheafification/HomotopyInvariance.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- The actual transfer-preserving Nisnevich sheafification of a homotopy
invariant presheaf with transfers is homotopy invariant. -/
@[colib_tag "COL-1028", colib_ref "MVW2006" "Lecture 22, Theorem 22.3" "adaptation"
  "Homotopy invariance of Nisnevich sheafification over a field"]
theorem nisnevichSheafify_isA1Invariant
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ((nisnevichSheafify k).obj P).obj.IsA1Invariant := by
  have hZero : IntegralAffineLocalZero k := integralAffineLocalZero_of_field k
  have hLift : ModelWholeCylinderLifting P := modelWholeCylinderLifting_of_isA1Invariant P hP
  exact nisnevichSheafify_isA1Invariant_of_modelWholeCylinderLifting (k := k) hZero P hP hLift

end AlgebraicGeometry.PresheafWithTransfers
