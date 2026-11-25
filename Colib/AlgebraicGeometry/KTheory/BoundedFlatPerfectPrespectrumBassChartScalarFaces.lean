/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBassChartScalarTracks
public import Colib.RingTheory.Polynomial.LaurentUnderSquare

/-!
# The forward and inverse chart evaluations of the Bass coefficient square

The two charts use separate geometric simplices and the same original
paused scalar parameter. These statements precede the boundary transports
to the raw Bass pushout square.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassChartScalarFaces.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectBassScalarComparison

open BoundedFlatPerfectDoubleSquareScalarPaths

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (g : a ⟶ b) (h : b ⟶ c)

/-- The positive chart evaluates at the original forward Laurent transformation. -/
theorem plusComparisonSquare_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum
      (RingedSpace.boundedAboveFlatPerfectWaldhausen
        (space (op P, (polynomialUnderFunctor R).obj a)).toRingedSpace)).space n) :
    prespectrumSimplexFamily (simplex P (underToLaurent R) g h) n
      (coefficientPausedSquareParameter (r, s), x) =
      ((BoundedFlatCoefficientTransformationComposition.movingSquare P
        (underToLaurent R) g h).pauseRight).level n (r, (s, x)) :=
  pausedSquare_native P (underToLaurent R) g h n r s x

/-- The negative chart evaluates in its own inverse-coordinate simplex. -/
theorem minusComparisonSquare_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum
      (RingedSpace.boundedAboveFlatPerfectWaldhausen
        (space (op P, (polynomialUnderFunctor R).obj a)).toRingedSpace)).space n) :
    prespectrumSimplexFamily (simplex P (underToLaurentInvert R) g h) n
      (coefficientPausedSquareParameter (r, s), x) =
      ((BoundedFlatCoefficientTransformationComposition.movingSquare P
        (underToLaurentInvert R) g h).pauseRight).level n (r, (s, x)) :=
  pausedSquare_native P (underToLaurentInvert R) g h n r s x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectBassScalarComparison
