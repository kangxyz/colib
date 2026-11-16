/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinarySupportedBassSeed
public import Colib.RingTheory.KTheory.Bass.StrictLaurentInverseAction

/-!
# The actual inverse supported Laurent operation

The inverse identity automorphism of the original Laurent Model induces the negative
of the original stable quotient operation, without a stable invertibility assumption.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
CoefficientSupportedUnitQuotient.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Topology Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The actual inverse automorphism of the unchanged supported Laurent unit. -/
def boundedAboveFlatCoefficientSupportedInverseLaurentAction :
    LaurentSeed.ModelAction (boundedAboveFlatCoefficientSupportedModelFunctor f) :=
  (boundedAboveFlatCoefficientSupportedLaurentAction f).symm

/-- The original supported forward unit followed by the original Laurent quotient. -/
def boundedAboveFlatCoefficientSupportedForwardUnitQuotient (d : ℤ) :=
  (boundedAboveFlatCoefficientSupportedLaurentAction f).track.stableUnitQuotient d

/-- The actual inverse supported unit followed by that same original quotient. -/
def boundedAboveFlatCoefficientSupportedInverseUnitQuotient (d : ℤ) :=
  (boundedAboveFlatCoefficientSupportedInverseLaurentAction f).track.stableUnitQuotient d

/-- The actual inverse-unit quotient is the negative original forward-unit quotient. -/
theorem boundedAboveFlatCoefficientSupportedInverseUnitQuotient_eq_neg (d : ℤ) :
    boundedAboveFlatCoefficientSupportedInverseUnitQuotient f d =
      -boundedAboveFlatCoefficientSupportedForwardUnitQuotient f d :=
  (boundedAboveFlatCoefficientSupportedLaurentAction f).symm_stableUnitQuotient d

end AlgebraicGeometry.Scheme.Modules
