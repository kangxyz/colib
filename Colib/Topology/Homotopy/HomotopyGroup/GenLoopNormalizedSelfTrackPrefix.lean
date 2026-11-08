/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopPrefixNullCoherence

/-! # The original inverse-prefix word of a normalized self-track

The existing loop-homeomorphism normalization is exactly the displayed inverse-prefix word,
including both original cancellation paths. Currying its new coordinate zero gives the literal
cube of based paths. All original spatial coordinates and every path time are retained.
-/
/-! Implementation provenance:
  `Quillen/Topology/HomotopyGroups/GenLoopNormalizedSelfTrackPrefix.lean:22-86`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, coordinates,
endpoint casts, cancellations and path orientations are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The original normalization retains precisely the inverse prefix and both cancellations. -/
theorem genLoopNormalizedSelfTrackPath_prefix (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) (α : Path p p) :
    genLoopNormalizedSelfTrackPath n p α =
      (GenLoopPrefix.cancellation n p).symm.trans
        ((α.map (GenLoopPrefix.inversePrefix n p).continuous).trans
          (GenLoopPrefix.cancellation n p)) := by
  let L := GenLoop.loopHomeo (X := X) (x := x) (0 : Fin (n + 1))
  have hc (s : unitInterval) :
      L.symm (loopInversePrefixCancellation (L p) s) =
        GenLoopPrefix.cancellation n p s := rfl
  have hm (s : unitInterval) :
      L.symm (loopLeftTranslationEquiv (L p).symm (L (α s))) =
        GenLoopPrefix.inversePrefix n p (α s) := by
    change GenLoop.fromLoop 0
      (loopLeftTranslationEquiv (GenLoop.toLoop 0 p).symm (GenLoop.toLoop 0 (α s))) =
        GenLoop.transAt 0 (GenLoop.symmAt 0 p) (α s)
    rw [loopLeftTranslationEquiv_apply, ← GenLoop.fromLoop_symm_toLoop,
      ← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]
  apply Path.ext
  funext t
  change L.symm (loopNormalizedSelfTrack (L p) (α.map L.continuous) t) = _
  simp only [loopNormalizedSelfTrack, Path.trans_apply, Path.cast_coe, Path.map_coe,
    Path.symm_apply, Function.comp_apply]
  split_ifs
  · exact hc _
  · exact hm _
  · exact hc _

/-- Every original time and spatial coordinate has the same inverse-prefix representative. -/
theorem genLoopNormalizedSelfTrackPath_prefix_apply (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) (α : Path p p)
    (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    genLoopNormalizedSelfTrackPath n p α t z =
      ((GenLoopPrefix.cancellation n p).symm.trans
        ((α.map (GenLoopPrefix.inversePrefix n p).continuous).trans
          (GenLoopPrefix.cancellation n p))) t z :=
  congrArg (fun P ↦ P t z) (genLoopNormalizedSelfTrackPath_prefix n p α)

/-- Coordinate zero is exactly the original normalized path time, with no coordinate swap. -/
theorem loopCurry_genLoopNormalizedSelfTrackCube (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) (α : Path p p) :
    loopCurry (genLoopNormalizedSelfTrackCube n p α) =
      genLoopOfBasedPath (genLoopNormalizedSelfTrackPath n p α) := by
  apply GenLoop.ext
  intro z
  apply Path.ext
  funext t
  change genLoopNormalizedSelfTrackCube n p α (Fin.cons t z) =
    genLoopNormalizedSelfTrackPath n p α t z
  rw [genLoopNormalizedSelfTrackCube_apply]
  rfl

/-- Currying preserves each residual coordinate independently of the normalized path time. -/
theorem loopCurry_genLoopNormalizedSelfTrackCube_apply (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) (α : Path p p)
    (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    loopCurry (genLoopNormalizedSelfTrackCube n p α) z t =
      genLoopNormalizedSelfTrackPath n p α t z := by
  rw [loopCurry_genLoopNormalizedSelfTrackCube, genLoopOfBasedPath_apply]

end Topology

attribute [colib_ref "quillen"
    "Quillen/Topology/HomotopyGroups/GenLoopNormalizedSelfTrackPrefix.lean:22-86"
    "adaptation"
    "The whole original normalized self-track with both inverse-prefix cancellations"]
  Topology.genLoopNormalizedSelfTrackPath_prefix
  Topology.genLoopNormalizedSelfTrackPath_prefix_apply
  Topology.loopCurry_genLoopNormalizedSelfTrackCube
  Topology.loopCurry_genLoopNormalizedSelfTrackCube_apply
