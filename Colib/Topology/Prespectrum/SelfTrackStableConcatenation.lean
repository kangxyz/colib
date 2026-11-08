/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.SelfTrackStableTimeOperations

/-! # Concatenation and the constant track on the original stable groups -/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackStableConcatenation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- A literally constant track gives the identity finite homotopy class. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableConcatenation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.homotopyClassOperation_refl (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) (E.space n) (E.point n)) :
    (Homotopy.refl f).homotopyClassOperation n m a = 1 := by
  induction a using Quotient.inductionOn with
  | h p =>
    have hp : (Homotopy.refl f).genLoopPath n p =
        Path.refl (GenLoop.postcomp (f.map n) (f.map_point n) p) := by
      ext s z
      rfl
    rw [Homotopy.homotopyClassOperation_mk, hp, genLoopSelfTrackClass_refl]

/-- The original time concatenation gives the sum in its original track-group order. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableConcatenation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableStageOperation_trans (H K : Homotopy f f) (d : ℤ) (n : ℕ) :
    (H.trans K).stableStageOperation d n =
      K.stableStageOperation d n + H.stableStageOperation d n := by
  apply AddCommGrpCat.ext
  intro a
  exact congrArg Additive.ofMul
    (H.homotopyClassOperation_trans K ((-d).toNat + n + 2) (d.toNat + n + 1)
      (Additive.toMul a))

/-- The actual constant track gives the zero unchanged stage map. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableConcatenation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableStageOperation_refl (d : ℤ) (n : ℕ) :
    (Homotopy.refl f).stableStageOperation d n = 0 := by
  apply AddCommGrpCat.ext
  intro a
  exact congrArg Additive.ofMul
    (Homotopy.homotopyClassOperation_refl (f := f)
      ((-d).toNat + n + 2) (d.toNat + n + 1) (Additive.toMul a))

/-- Concatenation descends through the same alternating signs and the same final tail. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableConcatenation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableOperation_trans (H K : Homotopy f f) (d : ℤ) :
    (H.trans K).stableOperation d = K.stableOperation d + H.stableOperation d := by
  apply colimit.hom_ext
  intro n
  change stableHomotopyι E d n ≫ (H.trans K).stableOperation d =
    stableHomotopyι E d n ≫ (K.stableOperation d + H.stableOperation d)
  rw [Preadditive.comp_add, (H.trans K).stableOperation_ι,
    K.stableOperation_ι, H.stableOperation_ι, H.stableStageOperation_trans]
  simp only [smul_add, Preadditive.add_comp]

/-- The constant track descends to the zero original integer-graded operation. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableConcatenation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableOperation_refl (d : ℤ) :
    (Homotopy.refl f).stableOperation d = 0 := by
  apply colimit.hom_ext
  intro n
  change stableHomotopyι E d n ≫ (Homotopy.refl f).stableOperation d =
    stableHomotopyι E d n ≫ 0
  rw [(Homotopy.refl f).stableOperation_ι, Homotopy.stableStageOperation_refl]
  simp

end Topology.LoopPrespectrum

attribute [colib_tag "COL-0321"]
  Topology.LoopPrespectrum.Homotopy.stableOperation_trans
  Topology.LoopPrespectrum.Homotopy.stableOperation_refl
