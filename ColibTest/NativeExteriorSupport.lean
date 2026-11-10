/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.Support

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow

universe u
variable {S : Scheme.{u}} (X Y T : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData)

example [IsFinite (exteriorSupportSourceProjection X Y W)] :
    IsFinite (exteriorIdentitySource X Y T W) := inferInstance
example [IsFinite (exteriorSupportSourceProjection X Y W)] :
    IsClosedImmersion (exteriorIdentityInclusion X Y T W) := inferInstance
example [GeometricallyIntegral T.hom] [IsIntegral W.subscheme]
    [IsLocallyNoetherian W.subscheme] : IsIntegral (exteriorIdentitySupport X Y T W) :=
  inferInstance
example : exteriorIdentitySource X Y T W ≫ pullback.snd X.hom T.hom =
    exteriorIdentityTarget X Y T W ≫ pullback.snd Y.hom T.hom := by
  rw [exteriorIdentitySource_snd, exteriorIdentityTarget_snd]

example (z : pullback (C := Scheme) X.hom Y.hom) (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) :
    IsClosedImmersion (exteriorIdentityInclusion X Y T (integralComponentAt z)) := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
  infer_instance
