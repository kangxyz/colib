/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackSpatial

/-! # Original spatial delays and unit paths of generalized loops

Adapted from `Quillen/Waldhausen/Additivity/CompactCoproductSpatial.lean:27–105` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, coordinates and path concatenations are retained. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval

universe u v

namespace Topology

variable {X : Type u} [TopologicalSpace X] {x : X} (n : ℕ)

/-- Delay an original cube along coordinate zero, keeping all residual coordinates. -/
def genLoopDelayLeft :
    C(unitInterval × GenLoop (Fin (n + 1)) X x, GenLoop (Fin (n + 1)) X x) where
  toFun tp := GenLoop.fromLoop 0 (Path.delayReflLeft tp.1 (GenLoop.toLoop 0 tp.2))
  continuous_toFun := (GenLoop.continuous_fromLoop 0).comp
    (Path.continuous_delayReflLeft.comp
      (continuous_fst.prodMk ((GenLoop.continuous_toLoop 0).comp continuous_snd)))

/-- Remove an original constant suffix in coordinate zero. -/
def genLoopDelayRight :
    C(unitInterval × GenLoop (Fin (n + 1)) X x, GenLoop (Fin (n + 1)) X x) where
  toFun tp := GenLoop.fromLoop 0 (Path.delayReflRight tp.1 (GenLoop.toLoop 0 tp.2))
  continuous_toFun := (GenLoop.continuous_fromLoop 0).comp
    (Path.continuous_delayReflRight.comp
      (continuous_fst.prodMk ((GenLoop.continuous_toLoop 0).comp continuous_snd)))

private theorem toLoop_const_zero :
    GenLoop.toLoop (X := X) (x := x) (0 : Fin (n + 1)) GenLoop.const = Path.refl GenLoop.const := by
  ext t z
  rfl

/-- The first endpoint is exactly the displayed constant-prefix concatenation. -/
theorem genLoopDelayLeft_zero (p : GenLoop (Fin (n + 1)) X x) :
    genLoopDelayLeft n (0, p) = GenLoop.transAt 0 GenLoop.const p := by
  change GenLoop.fromLoop 0 (Path.delayReflLeft 0 (GenLoop.toLoop 0 p)) = _
  rw [Path.delayReflLeft_zero, ← toLoop_const_zero n, GenLoop.fromLoop_trans_toLoop]

/-- The second endpoint is the unchanged original cube. -/
theorem genLoopDelayLeft_one (p : GenLoop (Fin (n + 1)) X x) :
    genLoopDelayLeft n (1, p) = p := by
  change GenLoop.fromLoop 0 (Path.delayReflLeft 1 (GenLoop.toLoop 0 p)) = _
  rw [Path.delayReflLeft_one]
  exact (GenLoop.loopHomeo 0).symm_apply_apply p

/-- The suffix-delay endpoint retains the exact original spatial concatenation. -/
theorem genLoopDelayRight_zero (p : GenLoop (Fin (n + 1)) X x) :
    genLoopDelayRight n (0, p) = GenLoop.transAt 0 p GenLoop.const := by
  change GenLoop.fromLoop 0 (Path.delayReflRight 0 (GenLoop.toLoop 0 p)) = _
  rw [Path.delayReflRight_zero, ← toLoop_const_zero n, GenLoop.fromLoop_trans_toLoop]

/-- Suffix removal ends at the unchanged original cube. -/
theorem genLoopDelayRight_one (p : GenLoop (Fin (n + 1)) X x) :
    genLoopDelayRight n (1, p) = p := by
  change GenLoop.fromLoop 0 (Path.delayReflRight 1 (GenLoop.toLoop 0 p)) = _
  rw [Path.delayReflRight_one]
  exact (GenLoop.loopHomeo 0).symm_apply_apply p

/-- The entire prefix-removal track fixes the original constant cube. -/
theorem genLoopDelayLeft_const (t : unitInterval) :
    genLoopDelayLeft (X := X) (x := x) n (t, GenLoop.const) = GenLoop.const := by
  ext z
  rfl

/-- The entire suffix-removal track fixes the original constant cube. -/
theorem genLoopDelayRight_const (t : unitInterval) :
    genLoopDelayRight (X := X) (x := x) n (t, GenLoop.const) = GenLoop.const := by
  ext z
  rfl

/-- The actual coordinate-zero suffix-removal path. -/
def genLoopRightUnitPath (p : GenLoop (Fin (n + 1)) X x) :
    Path (GenLoop.transAt 0 p GenLoop.const) p where
  toFun t := genLoopDelayRight n (t, p)
  continuous_toFun := (genLoopDelayRight n).continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := genLoopDelayRight_zero n p
  target' := genLoopDelayRight_one n p

/-- This suffix removal is exactly the old loop-space unit path under the original homeomorphism. -/
theorem genLoopRightUnitPath_original (p : GenLoop (Fin (n + 1)) X x)
    (t : unitInterval) :
    genLoopRightUnitPath n p t =
      GenLoop.fromLoop 0 (loopRightUnitPath (GenLoop.toLoop 0 p) t) := by
  change GenLoop.fromLoop 0 (Path.delayReflRight t (GenLoop.toLoop 0 p)) = _
  congr 1
  change Path.delayReflRight t (GenLoop.toLoop 0 p) =
    (Path.delayReflLeft t (GenLoop.toLoop 0 p).symm).symm
  rw [Path.delayReflLeft, Path.symm_symm, Path.symm_symm]


end Topology
