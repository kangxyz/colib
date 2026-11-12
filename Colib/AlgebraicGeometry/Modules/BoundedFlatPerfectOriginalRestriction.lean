/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullback
public import Colib.AlgebraicGeometry.Modules.PerfectOpenRestriction
public import Colib.AlgebraicGeometry.Modules.PerfectFlatPullbackRestriction
/-! # Original ordinary restriction of bounded-flat perfect complexes -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
/-- Original inclusion followed by restriction agrees with actual bounded-flat pullback. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Restriction.lean:37"
  "adaptation" "Original restriction comparison through the fully faithful inclusion"]
def boundedAboveFlatPerfectOriginalRestrictionIso :
    RingedSpace.boundedAboveFlatPerfectInclusion X.toRingedSpace ⋙
        perfectComplexesRestrictOpenImmersion j ≅
      boundedAboveFlatPerfectPullback j ⋙
        RingedSpace.boundedAboveFlatPerfectInclusion U.toRingedSpace :=
  Functor.fullyFaithfulCancelRight
    (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := U.toRingedSpace)))
    (Functor.isoWhiskerLeft (RingedSpace.boundedAboveFlatPerfectComplex X.toRingedSpace).ι
      (NatIso.mapHomologicalComplex (restrictFunctorIsoPullback j) (.up ℤ)))
end AlgebraicGeometry.Scheme.Modules
