/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackTimeOperations
public import Colib.Topology.Prespectrum.SelfTrackHomotopyClass

/-! # Original self-track reversal and concatenation on finite homotopy classes -/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackTimeOperations.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Literal reversal negates the original finite self-track class, including input Pi-one. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackTimeOperations.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.homotopyClassOperation_symm (H : Homotopy f f) (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) (E.space n) (E.point n)) :
    H.symm.homotopyClassOperation n m a = (H.homotopyClassOperation n m a)⁻¹ := by
  induction a using Quotient.inductionOn with
  | h p =>
    simp only [Homotopy.homotopyClassOperation_mk, Homotopy.genLoopPath_symm,
      genLoopSelfTrackClass_symm]

/-- The actual interval concatenation gives the reversed track-group product. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackTimeOperations.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.homotopyClassOperation_trans (H K : Homotopy f f) (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) (E.space n) (E.point n)) :
    (H.trans K).homotopyClassOperation n m a =
      K.homotopyClassOperation n m a * H.homotopyClassOperation n m a := by
  induction a using Quotient.inductionOn with
  | h p =>
    simp only [Homotopy.homotopyClassOperation_mk, Homotopy.genLoopPath_trans,
      genLoopSelfTrackClass_trans]

end Topology.LoopPrespectrum
