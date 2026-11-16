/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedConnectiveInvertibility
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientTwoChartStableSequence
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedUnitAction

/-!
# The original supported unit quotients and stage-zero chart exactness

For a qcqs ambient scheme and a compact removed open, the actual supported seed is invertible
in every nonnegative stable degree. Its exact original Laurent-track factorization and the
genuine spectral Bass short exact row therefore identify the original forward-unit quotient as
a natural isomorphism. The actual inverse unit gives its negative natural isomorphism. Original
stage-zero chart exactness follows from the same genuine row. No supported geometric first-
coordinate boundary or perfect scalar-operation evaluation comparison is asserted here.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
CoefficientSupportedUnitQuotient.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Topology Topology.LoopPrespectrum KTheory.Bass KTheory.Bass.TwoChartStable
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The actual stage-zero forward unit quotient is invertible on every coefficient object. -/
instance boundedAboveFlatCoefficientSupportedForwardUnitQuotient_app_isIso (a : Under R) (n : ℕ) :
    IsIso ((boundedAboveFlatCoefficientSupportedForwardUnitQuotient f (n : ℤ)).app a) := by
  let A := (boundedAboveFlatCoefficientSupportedLaurentAction f).track
  let : IsIso ((stableHomotopyFunctor (n : ℤ)).map (A.seedMap a)) := by
    change IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientSupportedBassTransition f 0).app a))
    infer_instance
  exact A.stableUnitQuotient_isIso_of_seed a
    (boundedAboveFlatCoefficientSupportedTwoChartSpectralConditions f 0 a) (n : ℤ)

/-- The original supported forward-unit quotient is a natural isomorphism. -/
instance boundedAboveFlatCoefficientSupportedForwardUnitQuotient_isIso (n : ℕ) :
    IsIso (boundedAboveFlatCoefficientSupportedForwardUnitQuotient f (n : ℤ)) :=
  NatIso.isIso_of_isIso_app _

/-- The original inverse supported unit quotient is a natural isomorphism. -/
instance boundedAboveFlatCoefficientSupportedInverseUnitQuotient_isIso (n : ℕ) :
    IsIso (boundedAboveFlatCoefficientSupportedInverseUnitQuotient f (n : ℤ)) := by
  let : IsIso ((boundedAboveFlatCoefficientSupportedLaurentAction f).track.stableUnitQuotient
      (n : ℤ)) := boundedAboveFlatCoefficientSupportedForwardUnitQuotient_isIso f n
  exact (boundedAboveFlatCoefficientSupportedLaurentAction f).symm_stableUnitQuotient_isIso (n : ℤ)

/-- The unchanged supported chart complex is exact in every nonnegative degree, including zero.
-/
theorem boundedAboveFlatCoefficientSupportedStageZeroChart_exact (a : Under R) (n : ℕ) :
    (chartComplex ((boundedAboveFlatCoefficientSupportedBassDiagram f 0).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) (n : ℤ)).Exact := by
  let A := (boundedAboveFlatCoefficientSupportedLaurentAction f).track
  let : IsIso ((stableHomotopyFunctor (n : ℤ)).map (A.seedMap a)) := by
    change IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientSupportedBassTransition f 0).app a))
    infer_instance
  exact (ShortComplex.ab_exact_iff_function_exact _).mpr
    (A.chart_exact_of_seed a
      (boundedAboveFlatCoefficientSupportedTwoChartSpectralConditions f 0 a) (n : ℤ))

end AlgebraicGeometry.Scheme.Modules
