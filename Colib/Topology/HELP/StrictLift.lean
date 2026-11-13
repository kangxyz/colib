/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Strict lifts up to a relative homotopy

For a fixed square, a lift retains the entire boundary exactly. Its
comparison homotopy is constant on that same boundary.
-/

@[expose] public section

open scoped Topology

namespace Topology

variable {A B X Y X' Y' : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

/-- An exact boundary lift with a homotopy relative to the entire boundary. -/
def StrictHomotopyLift (f : C(X, Y)) (i : C(A, B)) (a : C(A, X)) (b : C(B, Y)) : Prop :=
  ∃ c : C(B, X), c.comp i = a ∧ Nonempty ((f.comp c).HomotopyRel b (Set.range i))

/-- A commuting square of maps carries the original boundary lift and
the entire relative homotopy to the new target. -/
theorem StrictHomotopyLift.map {f : C(X, Y)} {g : C(X', Y')} {i : C(A, B)}
    {a : C(A, X)} {b : C(B, Y)} (h : StrictHomotopyLift f i a b)
    (p : C(X, X')) (q : C(Y, Y')) (w : q.comp f = g.comp p) :
    StrictHomotopyLift g i (p.comp a) (q.comp b) := by
  obtain ⟨c, hc, ⟨H⟩⟩ := h
  refine ⟨p.comp c, ?_, ⟨(H.compContinuousMap q).cast ?_ rfl⟩⟩
  · rw [ContinuousMap.comp_assoc, hc]
  · rw [← ContinuousMap.comp_assoc, w, ContinuousMap.comp_assoc]

end Topology
