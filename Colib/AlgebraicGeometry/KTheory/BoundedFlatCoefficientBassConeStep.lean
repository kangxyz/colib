/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassComparisonDescent
public import Colib.Topology.Prespectrum.ConeHomotopySquare
public import Colib.Topology.Prespectrum.ParameterLooping

/-!
# The actual coefficient map on the raw Bass cone and one-step prespectrum

The original whole comparison yields the cone map of the literal polynomial-span descent.
The parameter-looped map uses that cone map, with no identity or composition coherence asserted.

Implementation provenance: Quillen `BoundedFlat/CoefficientBassMap.lean:401-427`
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

/-- The original relative comparison is recovered on every collapsed parameter-square point. -/
theorem boundedAboveFlatCoefficientBassComparisonHomotopy_collapse (n : ℕ)
    (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (space (op P, a)).toRingedSpace)).space n) :
    (boundedAboveFlatCoefficientBassComparisonHomotopy P g).level n
      ((Topology.ThreeSideSquare.collapse z).1, HomotopyPushout.cylinder
        (K (polynomialProjection P a))
        (K (polynomialProjection P a)) n
          ((Topology.ThreeSideSquare.collapse z).2, x)) =
      (boundedAboveFlatCoefficientBassDescPasting P g).level n (z.1, (z.2, x)) :=
  (boundedAboveFlatCoefficientBassComparisonHomotopy_cylinder P g n
    (Topology.ThreeSideSquare.collapse z).1 (Topology.ThreeSideSquare.collapse z).2 x).trans
      ((boundedAboveFlatCoefficientBassDescPasting P g).toSquare_collapse n z x)

/-- The genuine comparison-map homotopy induces an actual map of the original Bass square cones. -/
def boundedAboveFlatCoefficientBassConeMap :
    mappingCone (boundedAboveFlatCoefficientBassSquareComparison P a) ⟶
      mappingCone (boundedAboveFlatCoefficientBassSquareComparison P b) :=
  mappingConeSquareMap _ _ (boundedAboveFlatCoefficientPolynomialSpanMap P g)
    (K (coefficientMap P ((laurentUnderFunctor R).map g)))
    (boundedAboveFlatCoefficientBassComparisonHomotopy P g)

/-- Parameter-correct looping gives a map between the actual one-step Bass spectra. -/
def boundedAboveFlatCoefficientBassStepMap :
    parameterLooping (mappingCone (boundedAboveFlatCoefficientBassSquareComparison P a)) ⟶
      parameterLooping (mappingCone (boundedAboveFlatCoefficientBassSquareComparison P b)) :=
  parameterLoopingMap (boundedAboveFlatCoefficientBassConeMap P g)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassMap.lean:401-427"
  "adaptation" "Native comparison evaluation and actual raw cone and parameter-looped maps."]
  boundedAboveFlatCoefficientBassComparisonHomotopy_collapse
  boundedAboveFlatCoefficientBassConeMap
  boundedAboveFlatCoefficientBassStepMap

end AlgebraicGeometry.Scheme.Modules
