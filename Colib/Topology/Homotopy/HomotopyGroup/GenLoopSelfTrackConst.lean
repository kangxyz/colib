/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.ConstantNormalization
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.NormalizedSelfTrackNaturality

/-!
# The original self-track class at the constant cube

At the constant cube the actual inverse-prefix normalization represents the
literal uncurried based path. The comparison is a relative homotopy, not an
assertion of pointwise equality between the normalized and original paths.
-/
/-! Implementation provenance:
`Quillen/Topology/HomotopyGroups/GenLoopSelfTrackConst.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Normalizing a self-track of the constant loop retains its original relative class. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/GenLoopSelfTrackConst.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem loopNormalizedSelfTrack_refl_homotopic
    (α : Path (Path.refl x) (Path.refl x)) :
    (loopNormalizedSelfTrack (Path.refl x) α).Homotopic α := by
  have he : (FundamentalGroup.fromPath ⟦loopNormalizedSelfTrack (Path.refl x) α⟧ :
      FundamentalGroup (Path x x) (Path.refl x)) = FundamentalGroup.fromPath ⟦α⟧ := by
    rw [← loopKOneNormalization_path, loopKOneNormalization_refl,
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact Quotient.exact (congrArg CategoryTheory.End.asHom he)

/-- The normalized constant-cube track is homotopic to the supplied original based path. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/GenLoopSelfTrackConst.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem genLoopNormalizedSelfTrackPath_const_homotopic (m : ℕ)
    (α : Path (GenLoop.const : GenLoop (Fin (m + 1)) X x) GenLoop.const) :
    (genLoopNormalizedSelfTrackPath m GenLoop.const α).Homotopic α := by
  let G := GenLoop (Fin (m + 1)) X x
  let B := GenLoop {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x
  let L : G ≃ₜ Path (GenLoop.const : B) GenLoop.const :=
    GenLoop.loopHomeo (0 : Fin (m + 1))
  have hL : L.toHomotopyEquiv.toFun GenLoop.const = Path.refl GenLoop.const := by
    ext s z
    rfl
  have hL' : L.symm.toHomotopyEquiv.toFun (Path.refl GenLoop.const) = GenLoop.const :=
    (congrArg L.symm hL).symm.trans (L.symm_apply_apply _)
  let β : Path (Path.refl (GenLoop.const : B)) (Path.refl GenLoop.const) :=
    (α.map L.toHomotopyEquiv.toFun.continuous).cast hL.symm hL.symm
  have hn : loopNormalizedSelfTrack (L.toHomotopyEquiv.toFun GenLoop.const)
      (α.map L.toHomotopyEquiv.toFun.continuous) =
        loopNormalizedSelfTrack (Path.refl GenLoop.const) β := by
    apply Path.ext
    funext t
    apply Path.ext
    funext s
    exact loopNormalizedSelfTrack_pointwise id id _ _
      (α.map L.toHomotopyEquiv.toFun.continuous) β
      (fun s ↦ congrArg (fun p : Path (GenLoop.const : B) GenLoop.const ↦ p s) hL)
      (fun _ _ ↦ rfl) t s
  have hm := ((loopNormalizedSelfTrack_refl_homotopic β).map
    L.symm.toHomotopyEquiv.toFun).pathCast hL'.symm hL'.symm
  have hl : ((loopNormalizedSelfTrack (Path.refl GenLoop.const) β).map
      L.symm.toHomotopyEquiv.toFun.continuous).cast hL'.symm hL'.symm =
        genLoopNormalizedSelfTrackPath m GenLoop.const α := by
    rw [← hn]
    rfl
  have hr : (β.map L.symm.toHomotopyEquiv.toFun.continuous).cast
      hL'.symm hL'.symm = α := by
    ext t z
    exact congrArg (fun p : G ↦ p z) (L.symm_apply_apply (α t))
  rw [hl, hr] at hm
  exact hm

/-- At the constant cube the class is exactly the literal uncurried original track. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/GenLoopSelfTrackConst.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem genLoopSelfTrackClass_const (m : ℕ)
    (α : Path (GenLoop.const : GenLoop (Fin (m + 1)) X x) GenLoop.const) :
    genLoopSelfTrackClass m GenLoop.const α =
      (⟦loopUncurry (genLoopOfBasedPath α)⟧ : HomotopyGroup.Pi (m + 2) X x) := by
  rw [← genLoopNormalizedSelfTrackCube_class]
  have he : genLoopNormalizedSelfTrackCube m GenLoop.const α =
      loopUncurry (genLoopOfBasedPath (genLoopNormalizedSelfTrackPath m GenLoop.const α)) := by
    ext z
    rfl
  rw [he]
  apply Quotient.sound
  obtain ⟨H⟩ := genLoopOfBasedPath_homotopic
    (genLoopNormalizedSelfTrackPath_const_homotopic m α)
  exact ⟨loopUncurryHomotopy H⟩

end Topology
