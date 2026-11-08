/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.SelfTrackHomotopyClass
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackKOne

/-!
# The original self-track on an actual based path

The literal family `H(t, γ(s))` is a path of based paths at the original
based image of `γ`. The unique-coordinate homeomorphism identifies it exactly
with the original generalized-loop track, including the basepoint correction.
The finite degree-one operation is consequently the inverse of the existing
spatial-first K-one normalization of this same path of paths.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackPath.lean`
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

/-- The literal original family of based paths, retaining its actual based image endpoint. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackPath.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def Homotopy.pathSelfTrack (H : Homotopy f f) (n : ℕ)
    (γ : Path (E.point n) (E.point n)) :
    Path (basedLoopMap (f.map n) (f.map_point n) γ)
      (basedLoopMap (f.map n) (f.map_point n) γ) where
  toFun t :=
    { toFun := fun s ↦ H.level n (t, γ s)
      continuous_toFun := by fun_prop
      source' := by rw [γ.source]; exact H.at_point n t
      target' := by rw [γ.target]; exact H.at_point n t }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : unitInterval × unitInterval ↦ H.level n (z.1, γ z.2))
    fun_prop
  source' := by
    apply Path.ext
    funext s
    exact H.at_zero n (γ s)
  target' := by
    apply Path.ext
    funext s
    exact H.at_one n (γ s)

/-- Neither the track parameter nor the original path parameter changes. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackPath.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs", simp]
theorem Homotopy.pathSelfTrack_apply (H : Homotopy f f) (n : ℕ)
    (γ : Path (E.point n) (E.point n)) (t s : unitInterval) :
    H.pathSelfTrack n γ t s = H.level n (t, γ s) := rfl

/-- The actual based image cube is the unique-coordinate cube of the original based image path. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackPath.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem genLoopPostcomp_finOne (n : ℕ) (γ : Path (E.point n) (E.point n)) :
    GenLoop.postcomp (f.map n) (f.map_point n)
        ((genLoopHomeomorphOfUnique (Fin 1)).symm γ) =
      (genLoopHomeomorphOfUnique (Fin 1)).symm
        (basedLoopMap (f.map n) (f.map_point n) γ) := rfl

/-- The unique-coordinate homeomorphism sends the original cube track to the literal path track. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackPath.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.genLoopPath_finOne_map (H : Homotopy f f) (n : ℕ)
    (γ : Path (E.point n) (E.point n)) :
    (H.genLoopPath n ((genLoopHomeomorphOfUnique (Fin 1)).symm γ)).map
        (genLoopHomeomorphOfUnique (Fin 1)).continuous = H.pathSelfTrack n γ := by
  apply Path.ext
  funext t
  apply Path.ext
  rfl

/-- The inverse homeomorphism retains the whole original path of paths as the cube track. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackPath.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.genLoopPath_finOne (H : Homotopy f f) (n : ℕ)
    (γ : Path (E.point n) (E.point n)) :
    H.genLoopPath n ((genLoopHomeomorphOfUnique (Fin 1)).symm γ) =
      (H.pathSelfTrack n γ).map (genLoopHomeomorphOfUnique (Fin 1)).symm.continuous := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro z
  rfl

/-- The original finite degree-one operation is inverse to the same literal path normalization. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackPath.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.homotopyClassOperation_finOne (H : Homotopy f f) (n : ℕ)
    (γ : Path (E.point n) (E.point n)) :
    H.homotopyClassOperation n 0
        ⟦(genLoopHomeomorphOfUnique (Fin 1)).symm γ⟧ =
      (loopKOneNormalization (basedLoopMap (f.map n) (f.map_point n) γ)
        (FundamentalGroup.fromPath ⟦H.pathSelfTrack n γ⟧))⁻¹ := by
  rw [H.homotopyClassOperation_mk, H.genLoopPath_finOne]
  exact genLoopSelfTrackClass_finOne_eq_inv (X := F.space n) (x := F.point n)
    (basedLoopMap (f.map n) (f.map_point n) γ) (H.pathSelfTrack n γ)

end Topology.LoopPrespectrum
