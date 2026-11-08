/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.NormalizedSelfTrackNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.CoordinateTransposition

/-!
# The two original degree-one self-track normalizations

The existing unique-coordinate loop equivalence is a homeomorphism. On the
actual converted path, the normalized generalized-loop cube has track time
first, whereas the original K-one normalization has spatial time first.
Their literal cubes differ by the displayed transposition, hence their
classes are inverse. No scalar or prespectrum comparison is asserted here.
-/
/-! Implementation provenance:
`Quillen/Topology/HomotopyGroups/GenLoopSelfTrackKOne.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The actual original equivalence for one coordinate, with its continuous inverse. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/GenLoopSelfTrackKOne.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def genLoopHomeomorphOfUnique (N : Type v) [Unique N] :
    GenLoop N X x ≃ₜ Path x x where
  toEquiv := genLoopEquivOfUnique N
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : GenLoop N X x × unitInterval => z.1 (fun _ => z.2))
    exact Continuous.eval continuous_fst
      (continuous_pi (fun _ => continuous_snd))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : Path x x × (N → unitInterval) => z.1 (z.2 default))
    exact (Path.continuous_uncurry_iff.mpr continuous_id).comp
      (continuous_fst.prodMk ((continuous_apply default).comp continuous_snd))

/-- The forward map is literally the existing unique-coordinate path. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/GenLoopSelfTrackKOne.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem genLoopHomeomorphOfUnique_apply (N : Type v) [Unique N]
    (p : GenLoop N X x) (t : unitInterval) :
    genLoopHomeomorphOfUnique N p t = p (fun _ => t) := rfl

/-- The inverse retains the original path evaluated at its unique coordinate. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/GenLoopSelfTrackKOne.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem genLoopHomeomorphOfUnique_symm_apply (N : Type v) [Unique N]
    (γ : Path x x) (z : N → unitInterval) :
    (genLoopHomeomorphOfUnique N).symm γ z = γ (z default) := rfl

/-- The full inverse-prefix normalization retains both actual original times. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/GenLoopSelfTrackKOne.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem genLoopNormalizedSelfTrackPath_finOne_apply (γ : Path x x) (α : Path γ γ)
    (t : unitInterval) (z : Fin 1 → unitInterval) :
    genLoopNormalizedSelfTrackPath 0 ((genLoopHomeomorphOfUnique (Fin 1)).symm γ)
        (α.map (genLoopHomeomorphOfUnique (Fin 1)).symm.continuous) t z =
      loopNormalizedSelfTrack γ α t (z 0) := by
  let L := GenLoop.loopHomeo (X := X) (x := x) (0 : Fin 1)
  let p := (genLoopHomeomorphOfUnique (Fin 1)).symm γ
  let β := α.map (genLoopHomeomorphOfUnique (Fin 1)).symm.continuous
  change (loopNormalizedSelfTrack (L.toHomotopyEquiv.toFun p)
    (β.map L.toHomotopyEquiv.toFun.continuous) t (z 0)) ((Cube.splitAt 0 z).2) = _
  exact loopNormalizedSelfTrack_pointwise
    (fun q : GenLoop {j : Fin 1 // j ≠ 0} X x => q ((Cube.splitAt 0 z).2)) id
    _ γ _ α (fun _ => rfl) (fun _ _ => rfl) t (z 0)

/-- The two actual normalized cubes differ by exactly the track/spatial transposition. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/GenLoopSelfTrackKOne.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem genLoopNormalizedSelfTrackCube_finOne_transpose (γ : Path x x) (α : Path γ γ) :
    genLoopNormalizedSelfTrackCube 0 ((genLoopHomeomorphOfUnique (Fin 1)).symm γ)
        (α.map (genLoopHomeomorphOfUnique (Fin 1)).symm.continuous) =
      transposeGenLoop (0 : Fin 2) 1 Fin.zero_ne_one
        (loopUncurry ((genLoopHomeomorphOfUnique (Fin 1)).symm
          (loopNormalizedSelfTrack γ α))) := by
  apply GenLoop.ext
  intro z
  rw [genLoopNormalizedSelfTrackCube_apply, genLoopNormalizedSelfTrackPath_finOne_apply]
  change loopNormalizedSelfTrack γ α (z 0) (z 1) =
    loopNormalizedSelfTrack γ α ((cubeCoordinateSwap 0 1 z) 1)
      ((cubeCoordinateSwap 0 1 z) 0)
  simp [cubeCoordinateSwap]

/-- The spatial-first cube is precisely the existing original K-one normalization. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/GenLoopSelfTrackKOne.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem loopNormalizedSelfTrack_finOne_cube_class (γ : Path x x) (α : Path γ γ) :
    (⟦loopUncurry ((genLoopHomeomorphOfUnique (Fin 1)).symm
      (loopNormalizedSelfTrack γ α))⟧ : HomotopyGroup.Pi 2 X x) =
      loopKOneNormalization γ (FundamentalGroup.fromPath ⟦α⟧) := by
  apply (loopShiftMulEquiv 0).injective
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (⟦loopCurry (loopUncurry ((genLoopHomeomorphOfUnique (Fin 1)).symm
      (loopNormalizedSelfTrack γ α)))⟧ : HomotopyGroup.Pi 1 (Path x x) (Path.refl x)) = _
  rw [loopCurry_loopUncurry]
  exact (loopKOneNormalization_path γ α).symm

/-- Track-first normalization is inverse to the original spatial-first K-one normalization. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/GenLoopSelfTrackKOne.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem genLoopSelfTrackClass_finOne_eq_inv (γ : Path x x) (α : Path γ γ) :
    genLoopSelfTrackClass 0 ((genLoopHomeomorphOfUnique (Fin 1)).symm γ)
        (α.map (genLoopHomeomorphOfUnique (Fin 1)).symm.continuous) =
      (loopKOneNormalization γ (FundamentalGroup.fromPath ⟦α⟧))⁻¹ := by
  rw [← genLoopNormalizedSelfTrackCube_class,
    genLoopNormalizedSelfTrackCube_finOne_transpose]
  exact (transposeGenLoop_class (0 : Fin 2) 1 Fin.zero_ne_one _).trans
    (congrArg (fun a : HomotopyGroup.Pi 2 X x => a⁻¹)
      (loopNormalizedSelfTrack_finOne_cube_class γ α))

end Topology
