/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0Native
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1UnaryComponents
public import Colib.KTheory.Waldhausen.Iterated.SimplexPostwhiskering
public import Colib.KTheory.Waldhausen.Iterated.SimplexWhiskering

/-!
# Native evaluation of the unary Bass composition components

The first and middle components retain the actual H0 cylinder and the Laurent
postcomposition or coefficient precomposition, respectively, at all levels.
Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassH1Components.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Components

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Entire first H1 piece: H0(u) followed by the original Laurent coefficient map of v. -/
theorem first_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (firstSimplex P u v) n
      (BoundedFlatCoefficientBassH0Diagram.parameter (s, t), x) =
      ((boundedAboveFlatCoefficientBassComparisonHomotopy P u).postcomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap
          (coefficientMap P ((laurentUnderFunctor R).map v)))).level n
        (s, HomotopyPushout.cylinder
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  rw [first_simplex_original, prespectrumSimplexFamily_postcomp,
    BoundedFlatCoefficientBassH0Diagram.native]
  rfl

/-- The original middle cylinder piece, after the actual coefficient-u overlap map. -/
theorem middle_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (middleSimplex P u v) n
      (BoundedFlatCoefficientBassH0Diagram.parameter (s, t), x) =
      (boundedAboveFlatCoefficientBassComparisonHomotopy P v).level n
        (s, HomotopyPushout.cylinder
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P b))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P b)) n
            (t, (boundedAboveFlatPerfectPullbackPrespectrumMap (coefficientMap P u)).map n x)) := by
  rw [middle_simplex_original, prespectrumSimplexFamily_precomp,
    BoundedFlatCoefficientBassH0Diagram.native]
  rfl

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Components
