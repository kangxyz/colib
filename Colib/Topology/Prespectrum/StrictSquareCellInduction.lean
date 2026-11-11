/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.StrictDoubleSquareConeCells

/-!
# Induction over the four original total-cone cells

This is ordinary induction through the existing cone and pushout quotients.
It keeps both independent parameters in the overlap cell and assumes no new
compatibility or topology data.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare.Cell

/-- Prove a pointwise proposition on the four original quotient strata. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareCellInduction.lean:26"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells.",
  elab_as_elim]
theorem inductionOn (S : Arrow (Arrow LoopPrespectrum.{u})) (n : ℕ)
    {motive : (totalFunctor.obj S).space n → Prop} (x : (totalFunctor.obj S).space n)
    (hTarget : ∀ y, motive (target S n y))
    (hUpper : ∀ r y, motive (upper S n r y))
    (hLower : ∀ r y, motive (lower S n r y))
    (hOverlap : ∀ r s y, motive (overlap S n r s y)) : motive x := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl y => exact hTarget y
    | inr z =>
      rcases z with ⟨r,q⟩
      induction q using Quot.inductionOn with
      | h z => cases z with
        | inl z => cases z with
          | inl y => exact hUpper r y
          | inr y => exact hLower r y
        | inr z => exact hOverlap r z.1 z.2

end Topology.LoopPrespectrum.StrictSquare.Cell
