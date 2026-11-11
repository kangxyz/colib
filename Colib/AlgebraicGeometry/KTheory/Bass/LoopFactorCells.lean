/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricChiScalar

/-! # Original cone-loop strength on the four whole quotient cells -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
open scoped Topology unitInterval
universe w
namespace KTheory.Bass.LoopFactor
variable (S : Arrow (Arrow LoopPrespectrum.{w})) (n : ℕ)

/-- The target cell keeps the arbitrary based loop and its independent time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopFactorCells.lean:20"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem coneStrength_target
    (γ : Path (S.right.right.point n) (S.right.right.point n)) (t : unitInterval) :
    Path.toContinuousMap ((coneStrength S).map n
      (Cell.target (loopSquare S) n γ)) t =
      Cell.target S n (γ t) := rfl

/-- The upper cell keeps the arbitrary based loop and its independent time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopFactorCells.lean:27"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem coneStrength_upper (r : unitInterval)
    (γ : Path (S.left.right.point n) (S.left.right.point n)) (t : unitInterval) :
    Path.toContinuousMap ((coneStrength S).map n
      (Cell.upper (loopSquare S) n r γ)) t =
      Cell.upper S n r (γ t) := rfl

/-- The lower cell keeps the arbitrary based loop and its independent time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopFactorCells.lean:34"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem coneStrength_lower (r : unitInterval)
    (γ : Path (S.right.left.point n) (S.right.left.point n)) (t : unitInterval) :
    Path.toContinuousMap ((coneStrength S).map n
      (Cell.lower (loopSquare S) n r γ)) t =
      Cell.lower S n r (γ t) := rfl

/-- The overlap cell keeps the arbitrary based loop and its independent time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopFactorCells.lean:41"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem coneStrength_overlap (r s : unitInterval)
    (γ : Path (S.left.left.point n) (S.left.left.point n)) (t : unitInterval) :
    Path.toContinuousMap ((coneStrength S).map n
      (Cell.overlap (loopSquare S) n r s γ)) t =
      Cell.overlap S n r s (γ t) := rfl

end KTheory.Bass.LoopFactor
