/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.SelfTrackSuccessorRepresentative
public import Colib.Topology.Prespectrum.StableHomotopy

/-!
# The original finite self-track successor sign

The explicit normalization-coordinate class comparison is followed by the
proved point-set structure comparison. Only then is the displayed interchange
of track time and structure time identified with group inversion. Both
successor maps are the original structure maps and actual inverse loop shifts.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackSuccessorSign.lean`
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

/-- The original structure-induced map evaluates its literal uncurried original cube. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackSuccessorSign.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs", simp]
theorem structurePiMap_mk (E : LoopPrespectrum.{u}) (n k : ℕ)
    (p : GenLoop (Fin (k + 1)) (E.space n) (E.point n)) :
    structurePiMap E n k ⟦p⟧ =
      (⟦loopUncurry (GenLoop.postcomp (E.structureMap n) (E.map_point n) p)⟧ :
        HomotopyGroup.Pi (k + 2) (E.space (n + 1)) (E.point (n + 1))) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual finite self-track operation anti-commutes with the original successor maps. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackSuccessorSign.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.homotopyClassOperation_structure_sign
    {E F : LoopPrespectrum.{u}} {f : E ⟶ F} (H : Homotopy f f) (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 2) (E.space n) (E.point n)) :
    H.homotopyClassOperation (n + 1) (m + 2) (structurePiMap E n (m + 1) a) =
      (structurePiMap F n (m + 2) (H.homotopyClassOperation n (m + 1) a))⁻¹ := by
  refine Quotient.inductionOn a (fun p ↦ ?_)
  exact (H.genLoopNormalizedSelfTrackCubeSecond_class (n + 1) (m + 1)
    (loopUncurry (GenLoop.postcomp (E.structureMap n) (E.map_point n) p))).symm.trans
      ((congrArg (fun q : GenLoop (Fin (m + 4)) (F.space (n + 1)) (F.point (n + 1)) ↦
        (⟦q⟧ : HomotopyGroup.Pi (m + 4) (F.space (n + 1)) (F.point (n + 1))))
          (H.genLoopNormalizedSelfTrackCubeSecond_structure n m p)).trans
        ((transposeGenLoop_class 0 1 Fin.zero_ne_one _).trans
          (congrArg (fun b : HomotopyGroup.Pi (m + 3) (F.space n) (F.point n) ↦
            (structurePiMap F n (m + 2) b)⁻¹)
              (genLoopNormalizedSelfTrackCube_class (m + 1) _ (H.genLoopPath n p)))))

end Topology.LoopPrespectrum
