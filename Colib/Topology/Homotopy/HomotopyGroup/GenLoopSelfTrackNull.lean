/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackConst
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackTransport

/-!
# Self-track classes with a specified original null path

The supplied null path conjugates the original self-track to a based path at
the constant cube. Its literal uncurrying represents the original normalized
class. This does not identify any particular geometric seed or stable map.
-/
/-! Implementation provenance:
`Quillen/Topology/HomotopyGroups/GenLoopSelfTrackNull.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u
namespace Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The actual supplied null path is retained in the higher-class representative. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/GenLoopSelfTrackNull.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem genLoopSelfTrackClass_eq_null_conjugate (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (α : Path p p)
    (Q : Path p GenLoop.const) :
    genLoopSelfTrackClass m p α =
      (⟦loopUncurry (genLoopOfBasedPath (Q.symm.trans (α.trans Q)))⟧ :
        HomotopyGroup.Pi (m + 2) X x) := by
  calc
    genLoopSelfTrackClass m p α = genLoopSelfTrackNormalization m GenLoop.const
        (FundamentalGroup.fundamentalGroupMulEquivOfPath Q (FundamentalGroup.fromPath ⟦α⟧)) :=
      (genLoopSelfTrackNormalization_transport m Q (FundamentalGroup.fromPath ⟦α⟧)).symm
    _ = genLoopSelfTrackClass m GenLoop.const (Q.symm.trans (α.trans Q)) := rfl
    _ = _ := genLoopSelfTrackClass_const m _

end Topology
