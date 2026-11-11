/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientTelescope

/-! # The actual original integral Spec-to-fine comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSupportedSection
open GlobalSectionChangeIndex

/-- Spec comparison followed by the original global-to-coefficient telescope restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterFineTelescope.lean:23"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
def fineTelescopeComparison (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ parameterTelescope Q.left ⟶ boundedAboveFlatCoefficientAmbientBassTelescopeFunctor
      Q :=
  (telescopeIso Q).hom ≫ telescopeRestriction Q

/-- The actual fine comparison is stable at every coefficient object. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterFineTelescope.lean:28"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem fineTelescopeComparison_stable
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((fineTelescopeComparison Q).app a) :=
  (telescopeIso_stable Q a).comp (telescopeRestriction_isStableEquivalence Q a)

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient


namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

attribute [colib_tag "COL-0580"] fineTelescopeComparison_stable

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
