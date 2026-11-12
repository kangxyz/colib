/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.CylinderCriterion
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.NativePolynomialLifting
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.Representatives.NativePolynomial

/-!
# Whole-cylinder lifting from homotopy invariance

The original distinguished cover supplies matching representatives. The
finite normalization and the paired section construction lift them to the
actual whole cylinder over a nonempty coefficient open.

Adapted from `Motivic/Cohomology/A1/Sheafification/WholeCylinderLifting.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

/-- A homotopy invariant presheaf with transfers has the original whole-cylinder
lifting property for its actual Nisnevich unit image. -/
theorem modelWholeCylinderLifting_of_isA1Invariant
    {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ModelWholeCylinderLifting P := by
  apply modelWholeCylinderLifting_of_nativePolynomialRepresentativeLifting P
  intro R _ _ _ _ _ _ t _
  exact nisnevichImage_lift_of_nativePolynomialRepresentatives R t P hP

end AlgebraicGeometry.PresheafWithTransfers
