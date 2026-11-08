/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.SelfTrackSuccessorSign

/-!
# The original self-track successor sign in every positive input degree

The point-set structure comparison only needs an original first coordinate.
Its alternate normalization is compared with the ordinary normalization at
the successor, whose input degree is already at least two. Thus the original
input degree one is included without any homomorphism premise in that degree.
The separate track and structure times and both original cancellations remain
explicit before applying the final coordinate-transposition sign.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackSuccessorPositive.lean`
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
    "Topology/Prespectrum/SelfTrackSuccessorPositive.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.genLoopNormalizedSelfTrackCubeSecond_structure_positive
    (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n)) :
    H.genLoopNormalizedSelfTrackCubeSecond (n + 1) m
        (loopUncurry (GenLoop.postcomp (E.structureMap n) (E.map_point n) p)) =
      transposeGenLoop (0 : Fin (m + 3)) 1 Fin.zero_ne_one
        (loopUncurry (GenLoop.postcomp (F.structureMap n) (F.map_point n)
          (genLoopNormalizedSelfTrackCube m _ (H.genLoopPath n p)))) := by
  let q := loopUncurry (GenLoop.postcomp (E.structureMap n) (E.map_point n) p)
  let r := transposeGenLoop 0 1 Fin.zero_ne_one q
  ext z
  rw [Homotopy.genLoopNormalizedSelfTrackCubeSecond_apply]
  change genLoopNormalizedSelfTrackPath (m + 1) _ (H.genLoopPath (n + 1) r)
      (z 0) (cubeCoordinateSwap 0 1 (Fin.tail z)) =
    F.structureMap n
      (genLoopNormalizedSelfTrackPath m _ (H.genLoopPath n p)
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
    (fun x ↦ F.structureMap n x (z 1)) id m (m + 1)
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


set_option backward.isDefEq.respectTransparency.types false in
/-- The actual finite self-track operation anti-commutes with the original successor maps. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackSuccessorPositive.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.homotopyClassOperation_structure_sign_positive
    (H : Homotopy f f) (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) (E.space n) (E.point n)) :
    H.homotopyClassOperation (n + 1) (m + 1) (structurePiMap E n m a) =
      (structurePiMap F n (m + 1) (H.homotopyClassOperation n m a))⁻¹ := by
  refine Quotient.inductionOn a (fun p ↦ ?_)
  exact (H.genLoopNormalizedSelfTrackCubeSecond_class (n + 1) m
    (loopUncurry (GenLoop.postcomp (E.structureMap n) (E.map_point n) p))).symm.trans
      ((congrArg (fun q : GenLoop (Fin (m + 3)) (F.space (n + 1)) (F.point (n + 1)) ↦
        (⟦q⟧ : HomotopyGroup.Pi (m + 3) (F.space (n + 1)) (F.point (n + 1))))
          (H.genLoopNormalizedSelfTrackCubeSecond_structure_positive n m p)).trans
        ((transposeGenLoop_class 0 1 Fin.zero_ne_one _).trans
          (congrArg (fun b : HomotopyGroup.Pi (m + 2) (F.space n) (F.point n) ↦
            (structurePiMap F n (m + 1) b)⁻¹)
              (genLoopNormalizedSelfTrackCube_class m _ (H.genLoopPath n p)))))


end Topology.LoopPrespectrum

attribute [colib_tag "COL-0321"]
  Topology.LoopPrespectrum.Homotopy.homotopyClassOperation_structure_sign_positive
