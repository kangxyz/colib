/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.Target

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {S : Scheme.{u}} (X Y T : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData)

example : Set.range (exteriorIdentityTarget X Y T W) =
    (pullback.fst Y.hom T.hom) ⁻¹' Set.range (exteriorSupport_targetProjection X Y W) :=
  exteriorIdentityTarget_range X Y T W

example [IsFinite (exteriorSupport_sourceProjection X Y W)] :
    Set.range ((exteriorIdentityInclusion X Y T W).ker.subschemeι ≫
      pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom) =
      (pullback.fst Y.hom T.hom) ⁻¹' Set.range (exteriorSupport_targetProjection X Y W) :=
  exteriorIdentityImage_target_range X Y T W
