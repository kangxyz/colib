/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Mathlib.Topology.Path

/-!
# Recover both whole factors of an evaluated concatenation, including their shared midpoint

Intended upstream module: `Aglib.Topology.Path.EvaluationFactorExtraction`.

For arbitrary topological spaces and an arbitrary evaluation function, equality on the entire
concatenation implies equality on each entire factor. The reversal result assumes equality at
every reversed interval time.

Current coefficient-seed and mixed-route consumers:
`CoefficientBassPositiveJ0PositiveRailsNative`, `CoefficientBassPositiveLeftFirstRailsNative`,
`CoefficientBassPositiveLeftMiddleRailsNative`, `CoefficientBassPositiveLeftUnitRailsNative`,
`RelativeHomotopyFactorEvaluation`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u v
namespace Path.Evaluation
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {a b c : X} {a' b' c' : Y}

private def leftHalf (s : I) : I := ⟨(s : ℝ) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩
private def rightHalf (s : I) : I :=
  ⟨((s : ℝ) + 1) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩

private theorem trans_leftHalf (p : Path a b) (q : Path b c) (s : I) :
    (p.trans q) (leftHalf s) = p s := by
  calc
    _ = (p.trans q).extend ((s : ℝ) / 2) := (Path.extend_extends' _ _).symm
    _ = p.extend (2 * ((s : ℝ) / 2)) :=
      Path.extend_trans_of_le_half p q (by linarith [s.2.2])
    _ = p.extend (s : ℝ) := congrArg p.extend (by ring)
    _ = p s := Path.extend_extends' p s

private theorem trans_rightHalf (p : Path a b) (q : Path b c) (s : I) :
    (p.trans q) (rightHalf s) = q s := by
  calc
    _ = (p.trans q).extend (((s : ℝ) + 1) / 2) := (Path.extend_extends' _ _).symm
    _ = q.extend (2 * (((s : ℝ) + 1) / 2) - 1) :=
      Path.extend_trans_of_half_le p q (by linarith [s.2.1])
    _ = q.extend (s : ℝ) := congrArg q.extend (by ring)
    _ = q s := Path.extend_extends' q s

/-- Recover the whole first factor from whole concatenation evaluation. -/
theorem left_factor (f : X → Y) (p : Path a b) (q : Path b c)
    (p' : Path a' b') (q' : Path b' c')
    (h : ∀ s, f ((p.trans q) s) = (p'.trans q') s) (s : I) :
    f (p s) = p' s := by
  have hs := h (leftHalf s)
  simpa only [trans_leftHalf] using hs

/-- Recover the whole second factor, with the midpoint handled by the exact extension theorem. -/
theorem right_factor (f : X → Y) (p : Path a b) (q : Path b c)
    (p' : Path a' b') (q' : Path b' c')
    (h : ∀ s, f ((p.trans q) s) = (p'.trans q') s) (s : I) :
    f (q s) = q' s := by
  have hs := h (rightHalf s)
  simpa only [trans_rightHalf] using hs

/-- Recover the original whole path from evaluation of its reversal. -/
theorem unreverse (f : X → Y) (p : Path a b) (p' : Path a' b')
    (h : ∀ s, f (p.symm s) = p'.symm s) (s : I) :
    f (p s) = p' s := by
  have hs := h (unitInterval.symm s)
  simpa only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm] using hs

end Path.Evaluation
