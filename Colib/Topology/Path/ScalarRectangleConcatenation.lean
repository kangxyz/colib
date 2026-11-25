/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Codex
-/
module

public import Colib.Topology.Path.CarrierHalfPaths

/-!
# Concatenate squares along a complete scalar edge

Both original half clocks remain unchanged. Adapted from
`Quillen/Topology/Path/ScalarRectangleConcatenation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open Topology
open Path.CarrierHalfPaths
open scoped Topology unitInterval
universe u

namespace Topology.ScalarRectangle

variable {X : Type u} [TopologicalSpace X]

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
    concatFirst F G h (lower s, t) = F (s, t) :=
  homotopy_lower (rowHomotopy F) ((rowHomotopy G).cast
    (ContinuousMap.ext (fun t ↦ (h t).symm)) rfl) s t

theorem concatFirst_upper (s t : unitInterval) :
    concatFirst F G h (upper s, t) = G (s, t) :=
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
    concatSecond F G k (s, lower t) = F (s, t) :=
  concatFirst_lower (swap F) (swap G) k t s

theorem concatSecond_upper (s t : unitInterval) :
    concatSecond F G k (s, upper t) = G (s, t) :=
  concatFirst_upper (swap F) (swap G) k t s

theorem concatSecond_zero (s : unitInterval) : concatSecond F G k (s, 0) = F (s, 0) :=
  concatFirst_zero (swap F) (swap G) k s

theorem concatSecond_one (s : unitInterval) : concatSecond F G k (s, 1) = G (s, 1) :=
  concatFirst_one (swap F) (swap G) k s

end Topology.ScalarRectangle
