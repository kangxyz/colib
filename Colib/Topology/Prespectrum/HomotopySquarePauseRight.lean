/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Topology.Prespectrum.HomotopySquareOfPasting
public import Colib.Topology.Prespectrum.HomotopySquareBoundary
public import Colib.Topology.Prespectrum.RelativeHomotopyReparam

/-!
# The terminal pause on a prespectrum homotopy square

The original right edge is followed by a constant half-time, with the other
three edges unchanged. Adapted from `CoefficientTransformationComposition.lean:159-164`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology
open scoped Topology unitInterval

universe u

namespace Topology.LoopPrespectrum.Homotopy.Square

/-- Add the required terminal pause to one side track while keeping the other three sides exact. -/
def pauseRight {E F : LoopPrespectrum.{u}} {f₀ g₀ f₁ g₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} (S : H₀.Square H₁ L M) :
    H₀.Square H₁ L (M.trans (Homotopy.refl g₁)) :=
  (S.toBoundary.trans ((Homotopy.RelHomotopy.refl (L.trans H₁)).hcomp
    (Homotopy.RelHomotopy.transRefl M).symm.symmPath)).toSquare

end Topology.LoopPrespectrum.Homotopy.Square
