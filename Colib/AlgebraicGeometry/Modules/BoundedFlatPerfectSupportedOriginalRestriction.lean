/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupportedApproximation

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPairPullback
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedRestriction
public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Support


/-! # Actual supported restriction versus bounded-flat pullback

The original supported inclusions compare literal restriction with actual pair pullback.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- Restriction and pullback agree through the original supported inclusions. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    SupportedRestriction.lean:32"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
def boundedAboveFlatPerfectSupportedOriginalRestrictionIso :
    boundedAboveFlatPerfectSupportedInclusion T.ι ⋙ perfectSupportedRestrict j T ≅
      boundedAboveFlatPerfectSupportedPullback (supportRestrictionPair j T) ⋙
        boundedAboveFlatPerfectSupportedInclusion (j ⁻¹ᵁ T).ι :=
  Functor.fullyFaithfulCancelRight (perfectSupported (j ⁻¹ᵁ T).ι).ι
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectSupported T.ι).ι
      (NatIso.mapHomologicalComplex (restrictFunctorIsoPullback j) (.up ℤ)))

end AlgebraicGeometry.Scheme.Modules
