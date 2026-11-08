/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackEvaluation
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.TransposeSign
public import Colib.Topology.Prespectrum.SelfTrackCoordinateChange

/-!
# The actual successor normalized representative

After changing the normalization coordinate, the original coherent H-family
commutes pointwise with structure uncurrying. The two displayed cubes differ
only by the explicit track-time/structure-time swap. This module proves that
point-set equality before deriving any successor sign on homotopy groups.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackSuccessorRepresentative.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- The actual successor family retains both independent times and both original cancellations. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackSuccessorRepresentative.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.genLoopNormalizedSelfTrackCubeSecond_structure
    (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    H.genLoopNormalizedSelfTrackCubeSecond (n + 1) (m + 1)
        (loopUncurry (GenLoop.postcomp (E.structureMap n) (E.map_point n) p)) =
      transposeGenLoop (0 : Fin (m + 4)) 1 Fin.zero_ne_one
        (loopUncurry (GenLoop.postcomp (F.structureMap n) (F.map_point n)
          (genLoopNormalizedSelfTrackCube (m + 1) _ (H.genLoopPath n p)))) := by
  let q := loopUncurry (GenLoop.postcomp (E.structureMap n) (E.map_point n) p)
  let r := transposeGenLoop 0 1 Fin.zero_ne_one q
  ext z
  rw [Homotopy.genLoopNormalizedSelfTrackCubeSecond_apply]
  change genLoopNormalizedSelfTrackPath (m + 2) _ (H.genLoopPath (n + 1) r)
      (z 0) (cubeCoordinateSwap 0 1 (Fin.tail z)) =
    F.structureMap n
      (genLoopNormalizedSelfTrackPath (m + 1) _ (H.genLoopPath n p)
        ((cubeCoordinateSwap 0 1 z) 1)
        (Fin.tail (Fin.tail (cubeCoordinateSwap 0 1 z)))) ((cubeCoordinateSwap 0 1 z) 0)
  rw [cubeCoordinateSwap_zero_one_tail_tail]
  have hz₀ : cubeCoordinateSwap 0 1 z 0 = z 1 := by simp [cubeCoordinateSwap]
  have hz₁ : cubeCoordinateSwap 0 1 z 1 = z 0 := by simp [cubeCoordinateSwap]
  rw [hz₀, hz₁]
  have hcoord (s : unitInterval) :
      cubeCoordinateSwap 0 1
          (Function.update (cubeCoordinateSwap 0 1 (Fin.tail z)) 0 s) =
        Fin.cons (z 1) (Function.update (Fin.tail (Fin.tail z)) 0 s) := by
    rw [cubeCoordinateSwap_update_swap_left 0 1 Fin.zero_ne_one, Fin.cons_update]
    change Function.update (Fin.tail z) 1 s =
      Function.update (Fin.cons ((Fin.tail z) 0) (Fin.tail (Fin.tail z))) 1 s
    rw [Fin.cons_self_tail]
  symm
  refine genLoopNormalizedSelfTrackPath_pointwise
    (fun x ↦ F.structureMap n x (z 1)) id (m + 1) (m + 2)
    _ _ (H.genLoopPath n p) (H.genLoopPath (n + 1) r)
    (Fin.tail (Fin.tail z)) (cubeCoordinateSwap 0 1 (Fin.tail z)) ?_ ?_ ?_ (z 0)
  · simp [cubeCoordinateSwap, Fin.tail]
  · intro s
    change F.structureMap n (f.map n (p (Function.update (Fin.tail (Fin.tail z)) 0 s)))
        (z 1) =
      f.map (n + 1) (q (cubeCoordinateSwap 0 1
        (Function.update (cubeCoordinateSwap 0 1 (Fin.tail z)) 0 s)))
    rw [hcoord]
    change F.structureMap n (f.map n (p (Function.update (Fin.tail (Fin.tail z)) 0 s)))
        (z 1) =
      f.map (n + 1) (E.structureMap n
        (p (Function.update (Fin.tail (Fin.tail z)) 0 s)) (z 1))
    exact (congrArg (fun γ ↦ γ (z 1))
      (f.comm n (p (Function.update (Fin.tail (Fin.tail z)) 0 s)))).symm
  · intro t s
    change F.structureMap n (H.level n (t, p (Function.update (Fin.tail (Fin.tail z)) 0 s)))
        (z 1) =
      H.level (n + 1) (t, q (cubeCoordinateSwap 0 1
        (Function.update (cubeCoordinateSwap 0 1 (Fin.tail z)) 0 s)))
    rw [hcoord]
    exact (H.comm n t (p (Function.update (Fin.tail (Fin.tail z)) 0 s)) (z 1)).symm

end Topology.LoopPrespectrum
