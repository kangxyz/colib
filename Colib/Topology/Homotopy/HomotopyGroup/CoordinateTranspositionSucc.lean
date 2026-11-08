/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Homotopy.HomotopyGroup.CoordinateTransposition

/-! Successor-indexed coordinate transposition retains the separate first parameter. -/
/-! Implementation provenance:
`Quillen/Topology/HomotopyGroups/CoordinateTranspositionSucc.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
open scoped unitInterval
namespace Topology

/-- Swapping two successor coordinates leaves the original first parameter unchanged. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/CoordinateTranspositionSucc.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs", simp]
theorem cubeCoordinateSwap_succ_zero {n : ℕ} (i j : Fin n)
    (z : Fin (n + 1) → unitInterval) :
    cubeCoordinateSwap i.succ j.succ z 0 = z 0 := by
  simp [cubeCoordinateSwap, (Fin.succ_ne_zero i).symm, (Fin.succ_ne_zero j).symm]

/-- The tail of a successor-coordinate swap is the original swap on the original tail. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/CoordinateTranspositionSucc.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs", simp]
theorem cubeCoordinateSwap_succ_tail {n : ℕ} (i j : Fin n)
    (z : Fin (n + 1) → unitInterval) :
    Fin.tail (cubeCoordinateSwap i.succ j.succ z) =
      cubeCoordinateSwap i j (Fin.tail z) := by
  funext k
  simp only [Fin.tail, cubeCoordinateSwap, Fin.succ_inj]

/-- Swapping, updating the first displayed direction, then swapping back updates the other one. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/CoordinateTranspositionSucc.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem cubeCoordinateSwap_update_swap_left {N : Type*} [DecidableEq N]
    (i j : N) (hij : i ≠ j) (z : N → unitInterval) (s : unitInterval) :
    cubeCoordinateSwap i j (Function.update (cubeCoordinateSwap i j z) i s) =
      Function.update z j s := by
  funext k
  by_cases hi : k = i
  · subst k
    simp [cubeCoordinateSwap, hij, hij.symm]
  · by_cases hj : k = j
    · subst k
      simp [cubeCoordinateSwap, hij.symm]
    · simp [cubeCoordinateSwap, hi, hj]

end Topology
