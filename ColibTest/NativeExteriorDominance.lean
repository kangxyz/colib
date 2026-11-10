/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.Dominance

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow

universe u
variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  (z : pullback (C := Scheme) X.hom Y.hom) (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

include hz

example : UniversallyOpen (exteriorIdentitySource X Y T (integralComponentAt z)) :=
  nativeExteriorSource_universallyOpen X Y T z hz
example [GeometricallyIntegral T.hom] :
    IsIntegral (exteriorIdentitySupport X Y T (integralComponentAt z)) :=
  nativeExteriorSupport_isIntegral X Y T z hz
example [GeometricallyIntegral T.hom] :
    Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) ∈
      irreducibleComponents (SmoothSite.product X T).left :=
  nativeExteriorSource_range_mem X Y T z hz
