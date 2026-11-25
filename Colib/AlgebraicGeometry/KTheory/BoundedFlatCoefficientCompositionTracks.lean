/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientPolynomialSpanUnit

/-!
# Binary composition of actual coefficient pullback tracks

The unchanged raw coefficient, polynomial and Laurent maps retain their geometric composition
tracks, with the original scheme order and the polynomial and Laurent functor transports.
Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassCoherence.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (P : Over (Spec R))

local notation "K(" f ")" => boundedAboveFlatPerfectPullbackPrespectrumMap f

/-- The actual original coefficient composition retains contravariant scheme order. -/
def boundedAboveFlatCoefficientCompositionHomotopy {a b c : Under R}
    (u : a ⟶ b) (v : b ⟶ c) :
    Homotopy (K(coefficientMap P (u ≫ v)))
      (K(coefficientMap P u) ≫
        K(coefficientMap P v)) :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (coefficientMap P v)
    (coefficientMap P u)).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (coefficientMap_comp P u v)).symm rfl

variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The polynomial endpoint composition track on the unchanged native polynomial fibers. -/
def boundedAboveFlatCoefficientPolynomialCompositionHomotopy :
    Homotopy
      (boundedAboveFlatPerfectPullbackPrespectrumMap
        (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v))))
      (boundedAboveFlatPerfectPullbackPrespectrumMap
          (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap
          (coefficientMap P ((polynomialUnderFunctor R).map v))) :=
  (boundedAboveFlatCoefficientCompositionHomotopy P
    ((polynomialUnderFunctor R).map u) ((polynomialUnderFunctor R).map v)).cast
      (congrArg (fun k ↦ boundedAboveFlatPerfectPullbackPrespectrumMap (coefficientMap P k))
        ((polynomialUnderFunctor R).map_comp u v)).symm rfl

/-- The original Laurent coefficient composition track, on the actual raw cone target. -/
def boundedAboveFlatCoefficientLaurentCompositionHomotopy :
    Homotopy
      (boundedAboveFlatPerfectPullbackPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v))))
      (boundedAboveFlatPerfectPullbackPrespectrumMap
          (coefficientMap P ((laurentUnderFunctor R).map u)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap
          (coefficientMap P ((laurentUnderFunctor R).map v))) :=
  (boundedAboveFlatCoefficientCompositionHomotopy P
    ((laurentUnderFunctor R).map u) ((laurentUnderFunctor R).map v)).cast
      (congrArg (fun k ↦ boundedAboveFlatPerfectPullbackPrespectrumMap (coefficientMap P k))
        ((laurentUnderFunctor R).map_comp u v)).symm rfl

end AlgebraicGeometry.Scheme.Modules
