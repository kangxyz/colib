/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.Topology.Homotopy.OpenCover.TransParameters
public import Colib.Topology.Prespectrum.HomotopyComposition

/-!
# Level evaluation on the two halves of a prespectrum homotopy

Adapted from `Quillen/Topology/Prespectrum/NativeHomotopyCells.lean:48–90`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Both formulas use the
existing affine half-interval parametrizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory FundamentalGroupoid.OpenCover
open scoped Topology unitInterval

universe u

namespace Topology.LoopPrespectrum.Homotopy

variable {E F : LoopPrespectrum.{u}} {f g h : E ⟶ F}
  (H : Homotopy f g) (K : Homotopy g h)

/-- The entire first half retains the first homotopy at its original speed. -/
theorem trans_leftHalf (n : ℕ) (s : unitInterval) (x : E.space n) :
    (H.trans K).level n (leftHalf s, x) = H.level n (s, x) := by
  change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (leftHalf s, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · change H.level n (⟨2 * (leftHalf s : ℝ), _⟩, x) = H.level n (s, x)
    exact congrArg (fun t : unitInterval ↦ H.level n (t, x))
      (Subtype.ext (by
        change 2 * (leftHalf s : ℝ) = (s : ℝ)
        rw [coe_leftHalf]
        ring))
  · rename_i hs
    exfalso
    apply hs
    change (leftHalf s : ℝ) ≤ 1 / 2
    rw [coe_leftHalf]
    linarith [s.2.2]

/-- The entire second half retains the second homotopy, including its shared initial point. -/
theorem trans_rightHalf (n : ℕ) (s : unitInterval) (x : E.space n) :
    (H.trans K).level n (rightHalf s, x) = K.level n (s, x) := by
  change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (rightHalf s, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · rename_i hs
    have hs₀ : s = 0 := by
      apply Subtype.ext
      change (rightHalf s : ℝ) ≤ 1 / 2 at hs
      rw [coe_rightHalf] at hs
      change (s : ℝ) = 0
      linarith [s.2.1]
    subst s
    change H.level n (⟨2 * (rightHalf 0 : ℝ), _⟩, x) = K.level n (0, x)
    calc
      _ = H.level n (1, x) := congrArg (fun t : unitInterval ↦ H.level n (t, x))
        (Subtype.ext (by norm_num [coe_rightHalf]))
      _ = _ := (H.at_one n x).trans (K.at_zero n x).symm
  · change K.level n (⟨2 * (rightHalf s : ℝ) - 1, _⟩, x) = K.level n (s, x)
    exact congrArg (fun t : unitInterval ↦ K.level n (t, x))
      (Subtype.ext (by
        change 2 * (rightHalf s : ℝ) - 1 = (s : ℝ)
        rw [coe_rightHalf]
        ring))

end Topology.LoopPrespectrum.Homotopy
