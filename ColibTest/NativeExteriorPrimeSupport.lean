/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.PrimeSupport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

example : (nativeExteriorSupportIso X Y T z hz).hom ≫
    (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι =
    exteriorIdentityInclusion X Y T (integralComponentAt z) :=
  nativeExteriorSupportIso_hom_inclusion X Y T z hz
