/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Scheme.IntegerBaseLaurentCoefficient
public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterLaurentUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionLaurentAction

/-! # The actual original integral Spec-to-fine comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSectionChangeIndex ParameterLaurentUnit

/-- The actual complete Spec-row pullback preserves the same forward Laurent unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientUnit.lean:26"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem ambientUnit_preserves
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (boundedAboveFlatGlobalSectionModelFunctor.map (laurentParameterIso Q
      a).hom.op).hom.toFunctor
      (ambientUnit Q.left (specUnder.obj a)) (globalLaurentUnit Q a) := by
  apply boundedAboveFlatGlobalSectionUnit_reindex_of_eq
  exact laurentParameterIso_unit Q a

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

