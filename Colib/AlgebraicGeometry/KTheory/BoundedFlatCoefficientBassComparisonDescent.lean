/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassComparisonPasting
public import Colib.Topology.Prespectrum.HomotopySquareOfPasting
public import Colib.Topology.Prespectrum.PushoutMovingHomotopy

/-!
# The actual moving Bass comparison on the polynomial-span pushout

The proved relative boundary gives the original moving square. Descent through the native
quotient pushout retains both literal endpoint maps, both charts, and all cylinder parameters.

Implementation provenance: Quillen `BoundedFlat/CoefficientBassMap.lean:359-399`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open scoped unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (g : a ⟶ b)

local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

/-- The actual geometric moving square descends to the two unchanged coefficient composites. -/
def boundedAboveFlatCoefficientBassComparisonHomotopy :
    Homotopy (boundedAboveFlatCoefficientBassSquareComparison P a ≫
      K (coefficientMap P ((laurentUnderFunctor R).map g)))
      (boundedAboveFlatCoefficientPolynomialSpanMap P g ≫
        boundedAboveFlatCoefficientBassSquareComparison P b) :=
  (HomotopyPushout.descSquareHomotopy
    (K (polynomialProjection P a)) (K (polynomialProjection P a))
    (boundedAboveFlatCoefficientPlusSquareHomotopy P g)
    (boundedAboveFlatCoefficientMinusSquareHomotopy P g)
    (boundedAboveFlatCoefficientBassDescPasting P g).toSquare).cast
      (boundedAboveFlatCoefficientBassSourceDesc_eq P g)
      (boundedAboveFlatCoefficientBassTargetDesc_eq P g)

/-- The left polynomial endpoint moves through its unchanged positive Laurent square. -/
theorem boundedAboveFlatCoefficientBassComparisonHomotopy_inl (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)).toRingedSpace)).space n) :
    (boundedAboveFlatCoefficientBassComparisonHomotopy P g).level n
      (r, (HomotopyPushout.inl
        (K (polynomialProjection P a))
        (K (polynomialProjection P a))).map n x) =
      (boundedAboveFlatCoefficientPlusSquareHomotopy P g).level n (r, x) := rfl

/-- The right polynomial endpoint moves through its distinct negative Laurent square. -/
theorem boundedAboveFlatCoefficientBassComparisonHomotopy_inr (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)).toRingedSpace)).space n) :
    (boundedAboveFlatCoefficientBassComparisonHomotopy P g).level n
      (r, (HomotopyPushout.inr
        (K (polynomialProjection P a))
        (K (polynomialProjection P a))).map n x) =
      (boundedAboveFlatCoefficientMinusSquareHomotopy P g).level n (r, x) := rfl

/-- The whole actual cylinder retains the square constructed from the proved geometric pasting. -/
theorem boundedAboveFlatCoefficientBassComparisonHomotopy_cylinder (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (space (op P, a)).toRingedSpace)).space n) :
    (boundedAboveFlatCoefficientBassComparisonHomotopy P g).level n
      (r, HomotopyPushout.cylinder
        (K (polynomialProjection P a))
        (K (polynomialProjection P a)) n (s, x)) =
      (boundedAboveFlatCoefficientBassDescPasting P g).toSquare.level n (r, (s, x)) := rfl

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassMap.lean:359-399"
  "adaptation" "The original descended comparison, with both chart tracks and the whole cylinder."]
  boundedAboveFlatCoefficientBassComparisonHomotopy
  boundedAboveFlatCoefficientBassComparisonHomotopy_inl
  boundedAboveFlatCoefficientBassComparisonHomotopy_inr
  boundedAboveFlatCoefficientBassComparisonHomotopy_cylinder

end AlgebraicGeometry.Scheme.Modules
