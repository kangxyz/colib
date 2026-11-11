/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumComposition
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentProjection
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.HomotopyPushout

/-! # The original raw geometric bounded-flat Bass square

The positive and inverse-coordinate geometric split tracks are retained separately.
Implementation provenance: Quillen `Affine/BoundedFlatBassSquare.lean:28-42,60-83`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
open CategoryTheory Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The positive leg retains its actual geometric-plus-binary-normalization track. -/
def boundedAboveFlatLaurentPlusHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection R))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (laurentToPolynomial R)) :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy
    (laurentToPolynomial R) (polynomialProjection R)).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (laurentToPolynomial_projection R)) rfl

/-- The inverse-coordinate leg retains its separate original binary track. -/
def boundedAboveFlatLaurentMinusHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection R))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus R)) :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy
    (laurentMinus R) (polynomialProjection R)).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus_projection R)) rfl

/-- The actual original two-leg Bass square in the raw bounded-flat model. -/
def boundedAboveFlatBassSquareHomotopy (R : CommRingCat.{u}) :=
  (boundedAboveFlatLaurentPlusHomotopy R).symm.trans (boundedAboveFlatLaurentMinusHomotopy R)

/-- The actual original double-cylinder comparison for the raw bounded-flat Bass square. -/
def boundedAboveFlatBassSquareComparison (R : CommRingCat.{u}) :=
  HomotopyPushout.desc (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentToPolynomial R))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus R))
    (boundedAboveFlatBassSquareHomotopy R)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/BoundedFlatBassSquare.lean:28-42,60-83"
  "adaptation" "Actual original split chart tracks and raw double-cylinder comparison"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatLaurentPlusHomotopy
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatLaurentMinusHomotopy
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatBassSquareHomotopy
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatBassSquareComparison
