/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.Topology.Path.CarrierHalfPaths

/-! Literal half-cell formulas for scalar paths, preserving the native concatenation speeds. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace Path.CarrierHalfPaths
variable {X : Type u} [TopologicalSpace X] {a b c : X} (p : Path a b) (q : Path b c)

theorem path_lower (s : unitInterval) : (p.trans q) (lower s) = p s := by
  rw [Path.trans_apply]
  split
  · exact congrArg p (Subtype.ext (by dsimp [lower]; ring))
  · rename_i hs
    exfalso
    apply hs
    change (s : ℝ) / 2 ≤ 1 / 2
    linarith [s.2.2]

theorem path_upper (s : unitInterval) : (p.trans q) (upper s) = q s := by
  rw [Path.trans_apply]
  split
  · rename_i hs
    have hs₀ : s = 0 := by
      apply Subtype.ext
      change ((s : ℝ) + 1) / 2 ≤ 1 / 2 at hs
      change (s : ℝ) = 0
      linarith [s.2.1]
    subst s
    calc
      _ = p 1 := congrArg p (Subtype.ext (by norm_num [upper]))
      _ = q 0 := p.target.trans q.source.symm
  · exact congrArg q (Subtype.ext (by dsimp [upper]; ring))

end Path.CarrierHalfPaths
