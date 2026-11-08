/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullback
public import Colib.AlgebraicGeometry.Modules.PerfectFlatPullbackRestriction

/-! # Literal inclusion and flat perfect pullback

The two composites retain the same underlying complexes and chain maps. Open restriction
uses the actual geometric restriction-pullback isomorphism, not an assumed K-naturality law.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The literal bounded-flat inclusion commutes with genuine flat chain pullback. -/
def boundedAboveFlatPerfectInclusionFlatPullbackIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] :
    boundedAboveFlatPerfectInclusion Y.toRingedSpace ⋙ perfectFlatPullback f ≅
      boundedAboveFlatPerfectPullback f ⋙ boundedAboveFlatPerfectInclusion X.toRingedSpace :=
  Iso.refl _

/-- Ordinary open-subset restriction is the same actual chain functor. -/
def perfectRestrictSubsetIsoOpenImmersion (X : Scheme.{u}) (U : X.Opens) :
    perfectComplexesRestrictFunctor X U ≅ perfectComplexesRestrictOpenImmersion U.ι :=
  Iso.refl _

end AlgebraicGeometry.Scheme.Modules
