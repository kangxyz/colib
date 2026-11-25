/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Path
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Whole path reconstruction from the two literal half slices, including their midpoint


For any topological space and continuous interval path, the two literal half paths reconstruct
every value, including their common midpoint. No comparison hypothesis is needed.

Adapted from `Quillen/Aglib/Topology/Path/CarrierHalfPaths.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

Current coefficient-seed and mixed-route consumers:
`CoefficientBassPositiveC1ReassociationPieces`,
`CoefficientBassPositiveC1ShiftedReassociationPieces`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace Path.CarrierHalfPaths
variable {X : Type u} [TopologicalSpace X]

/-- The original first-half clock, including both endpoints. -/
def lower (s : unitInterval) : unitInterval :=
  ⟨(s : ℝ) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩
/-- The original second-half clock, including the shared midpoint. -/
def upper (s : unitInterval) : unitInterval :=
  ⟨((s : ℝ) + 1) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩
/-- The shared midpoint of the original unit interval. -/
def middle : unitInterval := ⟨1 / 2, by norm_num⟩

/-- The literal first half of an arbitrary continuous path parameter. -/
def first (p : C(unitInterval, X)) : Path (p 0) (p middle) where
  toFun s := p (lower s)
  continuous_toFun := p.continuous.comp (by unfold lower; fun_prop)
  source' := congrArg p (by apply Subtype.ext; norm_num [lower])
  target' := congrArg p (by apply Subtype.ext; norm_num [lower, middle])

/-- The literal second half, with the same shared midpoint. -/
def last (p : C(unitInterval, X)) : Path (p middle) (p 1) where
  toFun s := p (upper s)
  continuous_toFun := p.continuous.comp (by unfold upper; fun_prop)
  source' := congrArg p (by apply Subtype.ext; norm_num [upper, middle])
  target' := congrArg p (by apply Subtype.ext; norm_num [upper])

/-- The two halves reconstruct every original value; the original clock is unchanged. -/
theorem trans_apply (p : C(unitInterval, X)) (s : unitInterval) :
    ((first p).trans (last p)) s = p s := by
  rw [Path.trans_apply]
  split_ifs
  · change p (lower _) = p s
    apply congrArg p
    apply Subtype.ext
    dsimp [lower]
    ring
  · change p (upper _) = p s
    apply congrArg p
    apply Subtype.ext
    dsimp [upper]
    ring

/-! The homotopy restrictions also come from
`Quillen/Topology/Path/ScalarRectangleConcatenation.lean` at the same revision. -/

section Homotopy
variable {Y : Type*} [TopologicalSpace Y] {f g h : C(Y, X)}
  (F : ContinuousMap.Homotopy f g) (G : ContinuousMap.Homotopy g h)

/-- Evaluate a concatenated homotopy on this literal half of the same clock. -/
theorem homotopy_lower (s : unitInterval) (x : Y) :
    (F.trans G) (lower s, x) = F (s, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split
  · change F (⟨2 * (lower s : ℝ), _⟩, x) = F (s, x)
    exact congrArg (fun t : unitInterval ↦ F (t, x))
      (Subtype.ext (by dsimp [lower]; ring))
  · rename_i hs
    exfalso
    apply hs
    change (s : ℝ) / 2 ≤ 1 / 2
    linarith [s.2.2]

/-- Evaluate a concatenated homotopy on this literal half of the same clock. -/
theorem homotopy_upper (s : unitInterval) (x : Y) :
    (F.trans G) (upper s, x) = G (s, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split
  · rename_i hs
    have hs₀ : s = 0 := by
      apply Subtype.ext
      change ((s : ℝ) + 1) / 2 ≤ 1 / 2 at hs
      change (s : ℝ) = 0
      linarith [s.2.1]
    subst s
    change F (⟨2 * (upper 0 : ℝ), _⟩, x) = G (0, x)
    calc
      _ = F (1, x) := congrArg (fun t : unitInterval ↦ F (t, x))
        (Subtype.ext (by norm_num [upper]))
      _ = _ := (F.map_one_left x).trans (G.map_zero_left x).symm
  · change G (⟨2 * (upper s : ℝ) - 1, _⟩, x) = G (s, x)
    exact congrArg (fun t : unitInterval ↦ G (t, x))
      (Subtype.ext (by dsimp [upper]; ring))
end Homotopy

/-- Both native half intervals cover the entire original parameter, not a sampled subset. -/
theorem cover (s : unitInterval) : (∃ t, lower t = s) ∨ (∃ t, upper t = s) := by
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · refine Or.inl ⟨⟨2 * (s : ℝ), by constructor <;> linarith [s.2.1]⟩, ?_⟩
    apply Subtype.ext
    dsimp [lower]
    ring
  · refine Or.inr ⟨⟨2 * (s : ℝ) - 1, by constructor <;> linarith [s.2.2]⟩, ?_⟩
    apply Subtype.ext
    dsimp [upper]
    ring

/-- The actual three-piece right-associated path covers its original whole time interval. -/
theorem three_cover (s : unitInterval) :
    (∃ t, lower t = s) ∨ (∃ t, upper (lower t) = s) ∨ (∃ t, upper (upper t) = s) := by
  rcases cover s with hs | ⟨t, rfl⟩
  · exact Or.inl hs
  · rcases cover t with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · exact Or.inr (Or.inl ⟨r, rfl⟩)
    · exact Or.inr (Or.inr ⟨r, rfl⟩)

end Path.CarrierHalfPaths
