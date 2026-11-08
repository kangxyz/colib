/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackSpatial

/-!
# Comparing normalized self-tracks along their actual coordinate lines

Evaluation functions may take values in a common target and the two original
cube dimensions may differ. Agreement along complete first-coordinate lines
suffices because all normalization reparametrizations preserve those lines.
-/
/-! Implementation provenance:
`Quillen/Topology/HomotopyGroups/GenLoopSelfTrackEvaluation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v w
namespace Topology

/-- Evaluated normalized paths agree when the original cube lines and actual track lines agree. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/GenLoopSelfTrackEvaluation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem genLoopNormalizedSelfTrackPath_pointwise
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (a : X → Z) (b : Y → Z) (m n : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (q : GenLoop (Fin (n + 1)) Y y)
    (α : Path p p) (β : Path q q)
    (z : Fin (m + 1) → unitInterval) (w : Fin (n + 1) → unitInterval)
    (h₀ : z 0 = w 0)
    (hp : ∀ s, a (p (Function.update z 0 s)) = b (q (Function.update w 0 s)))
    (hα : ∀ t s, a (α t (Function.update z 0 s)) = b (β t (Function.update w 0 s)))
    (t : unitInterval) :
    a (genLoopNormalizedSelfTrackPath m p α t z) =
      b (genLoopNormalizedSelfTrackPath n q β t w) := by
  let L := GenLoop.loopHomeo (X := X) (x := x) (0 : Fin (m + 1))
  let M := GenLoop.loopHomeo (X := Y) (x := y) (0 : Fin (n + 1))
  change a ((loopNormalizedSelfTrack (L.toHomotopyEquiv.toFun p)
      (α.map L.toHomotopyEquiv.toFun.continuous) t (z 0)) ((Cube.splitAt 0 z).2)) =
    b ((loopNormalizedSelfTrack (M.toHomotopyEquiv.toFun q)
      (β.map M.toHomotopyEquiv.toFun.continuous) t (w 0)) ((Cube.splitAt 0 w).2))
  rw [← h₀]
  refine loopNormalizedSelfTrack_pointwise
    (fun r : GenLoop {j : Fin (m + 1) // j ≠ 0} X x ↦ a (r ((Cube.splitAt 0 z).2)))
    (fun r : GenLoop {j : Fin (n + 1) // j ≠ 0} Y y ↦ b (r ((Cube.splitAt 0 w).2)))
    _ _ _ _ ?_ ?_ t (z 0)
  · intro s
    change a (p (Cube.insertAt 0 (s, (Cube.splitAt 0 z).2))) =
      b (q (Cube.insertAt 0 (s, (Cube.splitAt 0 w).2)))
    simpa only [cube_insertAt_splitAt] using hp s
  · intro r s
    change a (α r (Cube.insertAt 0 (s, (Cube.splitAt 0 z).2))) =
      b (β r (Cube.insertAt 0 (s, (Cube.splitAt 0 w).2)))
    simpa only [cube_insertAt_splitAt] using hα r s

end Topology
