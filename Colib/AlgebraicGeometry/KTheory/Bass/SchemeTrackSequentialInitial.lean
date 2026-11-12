/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialTransport

/-! The original initial leg under actual whole-track equality transport. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeTrackSequentialPresentation
open NaturalTrack GeometricSeedCospan ModelZigzagSequentialization

/-- The initial current inclusion is the actual first forward arrow of the chosen presentation. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeTrackSequentialInitial.lean:22"
  "adaptation" "Original first ordinary-colimit leg under whole-track equality transport."]
theorem comparisonOfEq_initial_leg (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A B : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (h : A = B)
    (X : Scheme.{u}ᵒᵖ) :
    Telescope.inclusion (vertex squareFunctor M X) (current M A X) 0 ≫
        comparisonOfEq M A B h X =
      ZigzagSequentialization.initialColimitMap (vertex squareFunctor M X)
        (suspendedVertex squareFunctor M X) (forward M B X) (unit squareFunctor M X) := by
  subst B
  exact initial_leg M A X

end KTheory.Bass.SchemeTrackSequentialPresentation
