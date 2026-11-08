/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Homotopy.HomotopyGroup.CoordinateTranspositionSucc
public import Colib.Topology.Prespectrum.SelfTrackHomotopyAdditivity

/-!
# An explicit change of the self-track normalization coordinate

Swap the first two input coordinates, normalize the actual H-track, and
restore those two spatial coordinates in the output. Track time stays first.
The two normalization procedures have equal classes in input degree at least
two, using the proved finite homomorphism and two original transpose signs.
This does not assert pointwise equality of the two procedures, or successor
compatibility with a prespectrum structure map.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackCoordinateChange.lean`
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

/-- The actual H-family commutes with the displayed spatial coordinate permutation. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackCoordinateChange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.genLoopPath_transpose (H : Homotopy f f) (n k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (p : GenLoop (Fin k) (E.space n) (E.point n))
    (t : unitInterval) :
    H.genLoopPath n (transposeGenLoop i j hij p) t =
      transposeGenLoop i j hij (H.genLoopPath n p t) := by
  ext z
  rfl

/-- Normalize along original input coordinate one and restore the original spatial order. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackCoordinateChange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def Homotopy.genLoopNormalizedSelfTrackCubeSecond (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    GenLoop (Fin (m + 3)) (F.space n) (F.point n) :=
  transposeGenLoop (0 : Fin (m + 2)).succ (1 : Fin (m + 2)).succ
    (fun h ↦ Fin.zero_ne_one (Fin.succ_inj.mp h))
    (genLoopNormalizedSelfTrackCube (m + 1) _
      (H.genLoopPath n (transposeGenLoop 0 1 Fin.zero_ne_one p)))

/-- Restoring the spatial order leaves track time first and swaps only the original tail. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackCoordinateChange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs", simp]
theorem Homotopy.genLoopNormalizedSelfTrackCubeSecond_apply
    (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n))
    (z : Fin (m + 3) → unitInterval) :
    H.genLoopNormalizedSelfTrackCubeSecond n m p z =
      genLoopNormalizedSelfTrackPath (m + 1) _
        (H.genLoopPath n (transposeGenLoop 0 1 Fin.zero_ne_one p))
        (z 0) (cubeCoordinateSwap 0 1 (Fin.tail z)) := by
  change genLoopNormalizedSelfTrackCube (m + 1) _ _
    (cubeCoordinateSwap (0 : Fin (m + 2)).succ (1 : Fin (m + 2)).succ z) = _
  rw [genLoopNormalizedSelfTrackCube_apply, cubeCoordinateSwap_succ_zero,
    cubeCoordinateSwap_succ_tail]

set_option backward.isDefEq.respectTransparency.types false in
/-- The two actual normalization coordinates give the same class in input degree at least two. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackCoordinateChange.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.genLoopNormalizedSelfTrackCubeSecond_class
    (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    (⟦H.genLoopNormalizedSelfTrackCubeSecond n m p⟧ :
      HomotopyGroup.Pi (m + 3) (F.space n) (F.point n)) =
        H.homotopyClassOperation n (m + 1) ⟦p⟧ := by
  have hinv (a : HomotopyGroup.Pi (m + 2) (E.space n) (E.point n)) :
      H.homotopyClassOperationHom n m a⁻¹ = (H.homotopyClassOperationHom n m a)⁻¹ :=
    map_inv (H.homotopyClassOperationHom n m) a
  have hinput : genLoopSelfTrackClass (m + 1) _
      (H.genLoopPath n (transposeGenLoop 0 1 Fin.zero_ne_one p)) =
        (H.homotopyClassOperation n (m + 1) ⟦p⟧)⁻¹ :=
    (congrArg (H.homotopyClassOperation n (m + 1))
      (transposeGenLoop_class 0 1 Fin.zero_ne_one p)).trans
        (hinv ⟦p⟧)
  exact (transposeGenLoop_class (0 : Fin (m + 2)).succ (1 : Fin (m + 2)).succ
    (fun h ↦ Fin.zero_ne_one (Fin.succ_inj.mp h)) _).trans
      ((congrArg (fun a : HomotopyGroup.Pi (m + 3) (F.space n) (F.point n) ↦ a⁻¹)
        ((genLoopNormalizedSelfTrackCube_class (m + 1) _ _).trans hinput)).trans
          (inv_inv (H.homotopyClassOperation n (m + 1) ⟦p⟧)))

end Topology.LoopPrespectrum
