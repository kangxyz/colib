/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.SelfTrackStableOperation

/-! # The literal second-level representative of the nonnegative self-track operation -/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackNonnegativeStage.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Nonnegative reindexing retains the actual second-level finite operation. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackNonnegativeStage.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableStageOperation_nonnegative (H : Homotopy f f) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 2) (E.space 2) (E.point 2)) :
    (shiftedStableReindexIso F (n : ℤ) 0).hom
        (H.stableStageOperation (n : ℤ) 0
          (nonnegativeStableStageEquiv E n (Additive.ofMul a))) =
      nonnegativeStableStageEquiv F (n + 1)
        (Additive.ofMul (H.homotopyClassOperation 2 (n + 1) a)) := by
  cases n <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The original stable operation evaluates the actual second-level class with sign plus one. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackNonnegativeStage.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableOperation_nonnegative_stage (H : Homotopy f f) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 2) (E.space 2) (E.point 2)) :
    H.stableOperation (n : ℤ)
        (stableHomotopyι E (n : ℤ) 0
          (nonnegativeStableStageEquiv E n (Additive.ofMul a))) =
      stableHomotopyι F ((n + 1 : ℕ) : ℤ) 0
        (nonnegativeStableStageEquiv F (n + 1)
          (Additive.ofMul (H.homotopyClassOperation 2 (n + 1) a))) := by
  have h := ConcreteCategory.congr_hom (H.stableOperation_ι (n : ℤ) 0)
    (nonnegativeStableStageEquiv E n (Additive.ofMul a))
  change H.stableOperation (n : ℤ)
      (stableHomotopyι E (n : ℤ) 0
        (nonnegativeStableStageEquiv E n (Additive.ofMul a))) =
    stableHomotopyι F ((n : ℤ) + 1) (parameterStableOffset (n : ℤ) + 0)
      ((shiftedStableReindexIso F (n : ℤ) 0).hom
        (((-1 : ℤ) ^ 0 • H.stableStageOperation (n : ℤ) 0)
          (nonnegativeStableStageEquiv E n (Additive.ofMul a)))) at h
  simp only [pow_zero, one_zsmul] at h
  rw [H.stableStageOperation_nonnegative] at h
  unfold parameterStableOffset at h
  split_ifs at h with hn
  · omega
  · simpa [hn] using h

end Topology.LoopPrespectrum
