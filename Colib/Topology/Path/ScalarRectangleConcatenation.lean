/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Topology.HomotopyLifting.PausedHomotopy

/-!
# Pasting continuous squares along a common edge

The two coordinate directions share the native affine half clocks. The scalar
cover also describes the right-associated decomposition into a half and two
quarters.

The concatenation and coverage lemmas are adapted from Quillen's
`ScalarRectangleConcatenation.lean` and `NativeHomotopyCells.lean` at revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

noncomputable section

open scoped Topology unitInterval

universe u

namespace Topology.ScalarRectangle
variable {X : Type u} [TopologicalSpace X]

/-- Both native half intervals cover the entire original parameter, not a sampled subset. -/
theorem cover (s : unitInterval) : (∃ t, firstHalfTime t = s) ∨ (∃ t, secondHalfTime t = s) := by
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · refine Or.inl ⟨⟨2 * (s : ℝ), by constructor <;> linarith [s.2.1]⟩, ?_⟩
    apply Subtype.ext
    dsimp [firstHalfTime]
    ring
  · refine Or.inr ⟨⟨2 * (s : ℝ) - 1, by constructor <;> linarith [s.2.2]⟩, ?_⟩
    apply Subtype.ext
    dsimp [secondHalfTime]
    ring

/-- The actual three-piece right-associated path covers its original whole time interval. -/
theorem three_cover (s : unitInterval) :
    (∃ t, firstHalfTime t = s) ∨ (∃ t, secondHalfTime (firstHalfTime t) = s) ∨
      (∃ t, secondHalfTime (secondHalfTime t) = s) := by
  rcases cover s with hs | ⟨t, rfl⟩
  · exact Or.inl hs
  · rcases cover t with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · exact Or.inr (Or.inl ⟨r, rfl⟩)
    · exact Or.inr (Or.inr ⟨r, rfl⟩)

section Homotopy
variable {Y : Type*} [TopologicalSpace Y] {f g h : C(Y, X)}
  (F : ContinuousMap.Homotopy f g) (G : ContinuousMap.Homotopy g h)

theorem homotopy_lower (s : unitInterval) (x : Y) :
    (F.trans G) (firstHalfTime s, x) = F (s, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split
  · change F (⟨2 * (firstHalfTime s : ℝ), _⟩, x) = F (s, x)
    exact congrArg (fun t : unitInterval ↦ F (t, x))
      (Subtype.ext (by dsimp [firstHalfTime]; ring))
  · rename_i hs
    exfalso
    apply hs
    change (s : ℝ) / 2 ≤ 1 / 2
    linarith [s.2.2]

theorem homotopy_upper (s : unitInterval) (x : Y) :
    (F.trans G) (secondHalfTime s, x) = G (s, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split
  · rename_i hs
    have hs₀ : s = 0 := by
      apply Subtype.ext
      change (1 + (s : ℝ)) / 2 ≤ 1 / 2 at hs
      change (s : ℝ) = 0
      linarith [s.2.1]
    subst s
    change F (⟨2 * (secondHalfTime 0 : ℝ), _⟩, x) = G (0, x)
    calc
      _ = F (1, x) := congrArg (fun t : unitInterval ↦ F (t, x))
        (Subtype.ext (by norm_num [secondHalfTime]))
      _ = _ := (F.map_one_left x).trans (G.map_zero_left x).symm
  · change G (⟨2 * (secondHalfTime s : ℝ) - 1, _⟩, x) = G (s, x)
    exact congrArg (fun t : unitInterval ↦ G (t, x))
      (Subtype.ext (by dsimp [secondHalfTime]; ring))
end Homotopy

variable (F G : C(unitInterval × unitInterval, X))

/-- The continuous slice of `F` obtained by fixing its first coordinate to `s`. -/
def row (s : unitInterval) : C(unitInterval, X) :=
  ⟨fun t ↦ F (s, t), by fun_prop⟩

/-- The homotopy between the first and last slices of `F`, with its first coordinate as homotopy
time.
-/
def rowHomotopy : ContinuousMap.Homotopy (row F 0) (row F 1) where
  toContinuousMap := F
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- Concatenate the actual original surfaces along their proved complete first-coordinate edge. -/
def concatFirst (h : ∀ t, F (1, t) = G (0, t)) : C(unitInterval × unitInterval, X) :=
  ((rowHomotopy F).trans ((rowHomotopy G).cast
    (ContinuousMap.ext (fun t ↦ (h t).symm)) rfl)).toContinuousMap

variable (h : ∀ t, F (1, t) = G (0, t))

theorem concatFirst_lower (s t : unitInterval) :
    concatFirst F G h (firstHalfTime s, t) = F (s, t) :=
  homotopy_lower (rowHomotopy F) ((rowHomotopy G).cast
    (ContinuousMap.ext (fun t ↦ (h t).symm)) rfl) s t

theorem concatFirst_upper (s t : unitInterval) :
    concatFirst F G h (secondHalfTime s, t) = G (s, t) :=
  homotopy_upper (rowHomotopy F) ((rowHomotopy G).cast
    (ContinuousMap.ext (fun t ↦ (h t).symm)) rfl) s t

theorem concatFirst_zero (t : unitInterval) : concatFirst F G h (0, t) = F (0, t) :=
  ((rowHomotopy F).trans ((rowHomotopy G).cast
    (ContinuousMap.ext (fun t ↦ (h t).symm)) rfl)).map_zero_left t

theorem concatFirst_one (t : unitInterval) : concatFirst F G h (1, t) = G (1, t) :=
  ((rowHomotopy F).trans ((rowHomotopy G).cast
    (ContinuousMap.ext (fun t ↦ (h t).symm)) rfl)).map_one_left t

/-- The continuous square map obtained by interchanging the two coordinates of `F`. -/
def swap : C(unitInterval × unitInterval, X) := ⟨fun z ↦ F (z.2, z.1), by fun_prop⟩

/-- The same continuous native concatenation in the independent second coordinate. -/
def concatSecond (h : ∀ s, F (s, 1) = G (s, 0)) : C(unitInterval × unitInterval, X) :=
  swap (concatFirst (swap F) (swap G) h)

variable (k : ∀ s, F (s, 1) = G (s, 0))

theorem concatSecond_lower (s t : unitInterval) :
    concatSecond F G k (s, firstHalfTime t) = F (s, t) :=
  concatFirst_lower (swap F) (swap G) k t s

theorem concatSecond_upper (s t : unitInterval) :
    concatSecond F G k (s, secondHalfTime t) = G (s, t) :=
  concatFirst_upper (swap F) (swap G) k t s

theorem concatSecond_zero (s : unitInterval) : concatSecond F G k (s, 0) = F (s, 0) :=
  concatFirst_zero (swap F) (swap G) k s

theorem concatSecond_one (s : unitInterval) : concatSecond F G k (s, 1) = G (s, 1) :=
  concatFirst_one (swap F) (swap G) k s

section ThreePieceSeam

variable {P A B C : C(unitInterval × unitInterval, X)}

/-- Three literal carrier-edge identities identify the whole edge with a right-associated
second-coordinate paste. The third surface is supplied with its prescribed parametrization. -/
theorem rightAssociated_seam
    (hBC : ∀ s, B (s, 1) = C (s, 0))
    (hA : ∀ s, A (s, 1) = concatSecond B C hBC (s, 0))
    (h₁ : ∀ t, P (1, firstHalfTime t) = A (0, t))
    (h₂ : ∀ t, P (1, secondHalfTime (firstHalfTime t)) = B (0, t))
    (h₃ : ∀ t, P (1, secondHalfTime (secondHalfTime t)) = C (0, t))
    (t : unitInterval) :
    P (1, t) = concatSecond A (concatSecond B C hBC) hA (0, t) := by
  rcases three_cover t with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
  · rw [concatSecond_lower]
    exact h₁ q
  · rw [concatSecond_upper, concatSecond_lower]
    exact h₂ q
  · rw [concatSecond_upper, concatSecond_upper]
    exact h₃ q

end ThreePieceSeam

end Topology.ScalarRectangle
