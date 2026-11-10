/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.Prime

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow

universe u
noncomputable section
variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

example : finiteCorrespondences (SmoothSite.product X T).hom (SmoothSite.product Y T).hom :=
  nativeExteriorPrime X Y T z hz
example : (nativeExteriorPrime X Y T z hz).1
    (genericPointOf (exteriorIdentityInclusion X Y T (integralComponentAt z)).ker
      (nativeExteriorImage_isIntegral X Y T z hz)) = 1 :=
  nativeExteriorPrime_apply X Y T z hz
